import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.AnnularLatticeScales
import OAI.Analysis.RieszRectifiability.Nets.BoundaryCellGeometry

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_flat_ball_descendant_geometry {d : ℕ} (μ : Measure (Ambient d))
    (R₀ : ℝ) (hR₀ : 0 < R₀) (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points)
    (a : Ambient d) (ha : a ∈ μ.support)
    (hnear : dist a (z : Ambient d) < latticeRadius R₀ k / 16)
    (r A : ℝ) (hr : 0 < r) (hrtop : r < latticeRadius R₀ k / 16) (hA : 1 ≤ A)
    (I : ℕ) (hdepth : annularLatticeDepth R₀ k (r / (A + 2)) (by positivity) ≤ I) :
    ∃ i : SupportCellDescendant μ R₀ hR₀ k z,
      0 < i.depth ∧ i.depth ≤ I ∧ r ≤ (512 * (A + 2)) * i.radius ∧
        A * i.radius ≤ latticeRadius R₀ k / 8 ∧
        ball i.center (A * i.radius) ⊆ ball a r := by
  have hp := latticeRadius_pos R₀ hR₀ k
  have hAp : 0 < A + 2 := by linarith
  have hq : 0 < r / (A + 2) := div_pos hr hAp
  have hqr : r / (A + 2) ≤ r := (div_le_iff₀ hAp).mpr (by nlinarith)
  let t := annularLatticeDepth R₀ k (r / (A + 2)) hq
  have ht : 0 < t := annularLatticeDepth_pos R₀ k (r / (A + 2)) hq (by linarith)
  have hu : latticeRadius R₀ (k + t) ≤ (r / (A + 2)) / 8 :=
    annularLatticeDepth_radius_upper R₀ k (r / (A + 2)) hq
  have hl : r / (A + 2) ≤ 512 * latticeRadius R₀ (k + t) :=
    annularLatticeDepth_radius_lower R₀ hR₀ k (r / (A + 2)) hq (by linarith)
  have hmul : (A + 2) * latticeRadius R₀ (k + t) ≤ r / 8 := by
    have hv := mul_le_mul_of_nonneg_left hu hAp.le
    calc
      _ ≤ (A + 2) * ((r / (A + 2)) / 8) := hv
      _ = r / 8 := by field_simp
  have hu64 : latticeRadius R₀ (k + t) ≤ latticeRadius R₀ k / 64 := by
    have hup := latticeRadius_pos R₀ hR₀ (k + t)
    nlinarith
  obtain ⟨w, haw⟩ := supportLatticeCell_cover μ R₀ hR₀ (k + t) a ha
  have hwz := closed_cell_ancestor_eq_of_interior_point μ R₀ hR₀ k t ht z w a haw
    (by linarith) hu64
  let i : SupportCellDescendant μ R₀ hR₀ k z :=
    { depth := t, center := w, mem_net := w.property, ancestor := hwz }
  refine ⟨i, ht, hdepth, ?_, ?_, ?_⟩
  · change r ≤ (512 * (A + 2)) * latticeRadius R₀ (k + t)
    have hv := (div_le_iff₀ hAp).mp hl
    nlinarith
  · change A * latticeRadius R₀ (k + t) ≤ latticeRadius R₀ k / 8
    have hup := latticeRadius_pos R₀ hR₀ (k + t)
    nlinarith
  · intro x hx
    have hxa : dist x (w : Ambient d) < A * latticeRadius R₀ (k + t) := hx
    have hwa : dist (w : Ambient d) a ≤ 2 * latticeRadius R₀ (k + t) := by
      rw [dist_comm]
      exact (supportLatticeCell_bounds μ R₀ hR₀ (k + t) w).2 haw
    have htri := dist_triangle x (w : Ambient d) a
    change dist x a < r
    nlinarith

theorem exists_uniform_flat_ball_descendant_geometry (ρ A : ℝ) (hρ : 0 < ρ) (hA : 1 ≤ A) :
    ∃ I : ℕ, 0 < I ∧ ∀ {d : ℕ} (μ : Measure (Ambient d))
      (R₀ : ℝ) (hR₀ : 0 < R₀) (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points),
      ∀ a ∈ μ.support, dist a (z : Ambient d) < latticeRadius R₀ k / 16 →
      ∀ r : ℝ, 0 < r → ρ * latticeRadius R₀ k ≤ r → r < latticeRadius R₀ k / 16 →
      ∃ i : SupportCellDescendant μ R₀ hR₀ k z,
        0 < i.depth ∧ i.depth ≤ I ∧ r ≤ (512 * (A + 2)) * i.radius ∧
          A * i.radius ≤ latticeRadius R₀ k / 8 ∧
          ball i.center (A * i.radius) ⊆ ball a r := by
  obtain ⟨I, hI, hchoose⟩ := exists_uniform_annular_lattice_depth (ρ / (A + 2)) (by positivity)
  refine ⟨I, hI, ?_⟩
  intro d μ R₀ hR₀ k z a ha hnear r hr hfloor hcap
  apply exists_flat_ball_descendant_geometry μ R₀ hR₀ k z a ha hnear r A hr hcap hA I
  apply hchoose R₀ hR₀ k (r / (A + 2)) (by positivity)
  calc
    _ = (ρ * latticeRadius R₀ k) / (A + 2) := by ring
    _ ≤ r / (A + 2) := div_le_div_of_nonneg_right hfloor (by positivity)

end

end RieszRectifiability

end OAI
