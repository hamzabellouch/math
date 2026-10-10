import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.ADCellHaarPairs

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem clean_cell_dist_to_closed_point {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (a : Ambient d) (ha : a ∈ supportLatticeCell μ R hR k z)
    (x : Ambient d) (hx : x ∈ cleanSupportCell μ R hR k z) :
    dist x a ≤ 4 * latticeRadius R k := by
  have hb := (supportLatticeCell_bounds μ R hR k z).2
  have hxa : dist x (z : Ambient d) ≤ 2 * latticeRadius R k := hb hx.1
  have haa : dist a (z : Ambient d) ≤ 2 * latticeRadius R k := hb ha
  have ht := dist_triangle x (z : Ambient d) a
  rw [dist_comm (z : Ambient d) a] at ht
  linarith

theorem supportLatticeAncestor_forced_near_center {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k t : ℕ) (ht : 0 < t)
    (z : (supportLatticeNets μ R hR k).points)
    (w : (supportLatticeNets μ R hR (k + t)).points)
    (hnear : dist (w : Ambient d) (z : Ambient d) < latticeRadius R k / 4) :
    supportLatticeAncestor μ R hR k t w = z := by
  cases t with
  | zero => omega
  | succ t =>
    apply Subtype.ext
    exact congrArg (fun u : μ.support => (u : Ambient d))
      (netAncestor_forced_near_center R hR (supportLatticeNets μ R hR)
      k t (supportLatticeCenter μ R hR (k + (t + 1)) w)
      (supportLatticeCenter μ R hR k z) z.property hnear)

theorem closed_cell_ancestor_eq_of_interior_point {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k t : ℕ) (ht : 0 < t)
    (z : (supportLatticeNets μ R hR k).points)
    (w : (supportLatticeNets μ R hR (k + t)).points)
    (a : Ambient d) (ha : a ∈ supportLatticeCell μ R hR (k + t) w)
    (hnear : dist a (z : Ambient d) ≤ latticeRadius R k / 8)
    (hscale : latticeRadius R (k + t) ≤ latticeRadius R k / 64) :
    supportLatticeAncestor μ R hR k t w = z := by
  apply supportLatticeAncestor_forced_near_center μ R hR k t ht z w
  have haW : dist a (w : Ambient d) ≤ 2 * latticeRadius R (k + t) :=
    (supportLatticeCell_bounds μ R hR (k + t) w).2 ha
  have htri := dist_triangle (w : Ambient d) a (z : Ambient d)
  rw [dist_comm (w : Ambient d) a] at htri
  have hp := latticeRadius_pos R hR k
  linarith

def annularCellMassConstant (n : ℕ) (C : ℝ) : ℝ := C * (512 * 8 : ℝ) ^ n

theorem annularCellMassConstant_pos (n : ℕ) (C : ℝ) (hC : 0 < C) :
    0 < annularCellMassConstant n C := by unfold annularCellMassConstant; positivity

theorem clean_cell_annular_mass_bound {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (r : ℝ) (hr : 0 ≤ r) (hscale : r ≤ 512 * latticeRadius R k) :
    r ^ n ≤ annularCellMassConstant n C * μ.real (cleanSupportCell μ R hR k z) := by
  have hl := (cleanSupportCell_real_measure_bounds μ C G hC hG hg hlower R hR k hcore z).1
  have hK := annularCellMassConstant_pos n C hC
  calc
    _ ≤ (512 * latticeRadius R k) ^ n := pow_le_pow_left₀ hr hscale n
    _ = annularCellMassConstant n C * ((latticeRadius R k / 8) ^ n / C) := by
      unfold annularCellMassConstant
      simp only [mul_pow, div_pow]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hl hK.le

end

end RieszRectifiability

end OAI
