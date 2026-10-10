import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.FlatAnnularAlternativeEvents
import OAI.Analysis.RieszRectifiability.Flatness.FlatCellGeometry

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

def HasFlatCell {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points) (A α : ℝ) : Prop :=
  ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S ∧
    (∀ x ∈ ball (z : Ambient d) (A * latticeRadius R₀ k), x ∈ μ.support →
      infDist x (S : Set (Ambient d)) ≤ α * latticeRadius R₀ k) ∧
    (∀ x ∈ ball (z : Ambient d) (A * latticeRadius R₀ k), x ∈ S →
      infDist x μ.support ≤ α * latticeRadius R₀ k)

def HasFlatDescendant {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points) (I : ℕ) (A α : ℝ) : Prop :=
  ∃ i : SupportCellDescendant μ R₀ hR₀ k z,
    0 < i.depth ∧ i.depth ≤ I ∧ A * i.radius ≤ latticeRadius R₀ k / 8 ∧
      HasFlatCell n μ R₀ hR₀ (k + i.depth) ⟨i.center, i.mem_net⟩ A α

theorem exists_uniform_flat_ball_to_cell {n d : ℕ} (hnd : n ≤ d)
    (ρ A α : ℝ) (hρ : 0 < ρ) (hA : 1 ≤ A) (hα : 0 < α) :
    ∃ I : ℕ, 0 < I ∧ ∀ (μ : Measure (Ambient d))
      (R₀ : ℝ) (hR₀ : 0 < R₀) (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points),
      HasFlatBallAbove n μ (ball (z : Ambient d) (latticeRadius R₀ k / 16))
        (ρ * latticeRadius R₀ k) (latticeRadius R₀ k / 16) (α / (1024 * (A + 2))) →
      HasFlatDescendant n μ R₀ hR₀ k z I A α := by
  obtain ⟨I, hI, hchoose⟩ := exists_uniform_flat_ball_descendant_geometry ρ A hρ hA
  refine ⟨I, hI, ?_⟩
  intro μ R₀ hR₀ k z hflat
  obtain ⟨a, ha, hnear, r, hr, hfloor, hcap, hbeta⟩ := hflat
  obtain ⟨i, hip, hiI, hscale, hisize, hsub⟩ :=
    hchoose μ R₀ hR₀ k z a ha hnear r hr hfloor hcap
  obtain ⟨S, hS, he⟩ := exists_bilateral_plane_error_lt hnd μ a r _ hbeta
  obtain ⟨hf, hb⟩ := bilateralPlaneError_lt_pointwise μ ⟨a, ha⟩ a r _ hr S hS he
  have hAp : 0 < A + 2 := by linarith
  have hbound : (α / (1024 * (A + 2))) * r ≤ α * i.radius := by
    calc
      _ ≤ (α / (1024 * (A + 2))) * ((512 * (A + 2)) * i.radius) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = α * i.radius / 2 := by field_simp; ring
      _ ≤ α * i.radius := by nlinarith [mul_pos hα i.radius_pos]
  refine ⟨i, hip, hiI, hisize, S, hS, ?_, ?_⟩
  · intro x hx hsupp
    exact (hf x (hsub hx) hsupp).le.trans hbound
  · intro x hx hs
    exact (hb x (hsub hx) hs).le.trans hbound

theorem HasFlatDescendant.enlarged_admissible {n d : ℕ}
    (μ : Measure (Ambient d)) (R₀ : ℝ) (hR₀ : 0 < R₀) (k : ℕ)
    (z : (supportLatticeNets μ R₀ hR₀ k).points) (I : ℕ) (A α : ℝ) (hA : 0 < A)
    (hcore : AdmissibleRadius μ (latticeRadius R₀ k / 8))
    (hflat : HasFlatDescendant n μ R₀ hR₀ k z I A α) :
    ∃ i : SupportCellDescendant μ R₀ hR₀ k z,
      0 < i.depth ∧ i.depth ≤ I ∧ AdmissibleRadius μ (A * i.radius) ∧
        HasFlatCell n μ R₀ hR₀ (k + i.depth) ⟨i.center, i.mem_net⟩ A α := by
  obtain ⟨i, hip, hiI, hsize, hfit⟩ := hflat
  exact ⟨i, hip, hiI, ⟨mul_pos hA i.radius_pos,
    (ENNReal.ofReal_le_ofReal hsize).trans hcore.2⟩, hfit⟩

end

end RieszRectifiability

end OAI
