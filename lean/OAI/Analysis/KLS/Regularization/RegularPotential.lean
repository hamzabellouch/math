import OAI.Analysis.KLS.Stein.SteinHessianDefs
import OAI.Analysis.KLS.Measures.PotentialMeasure

namespace OAI

noncomputable section
open scoped ContDiff

namespace LeanBlast.KLS

structure IsRegularPotential {n : ℕ} (V : Space n → ℝ) (t t' : ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ V
  lower_pos : 0 < t
  le_upper : t ≤ t'
  lower_bound : ∀ x v : Space n,
    t * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v
  upper_bound : ∀ x v : Space n,
    fderiv ℝ (fderiv ℝ V) x v v ≤ t' * ‖v‖ ^ 2

theorem IsRegularPotential.upper_pos {n : ℕ} {V : Space n → ℝ} {t t' : ℝ}
    (hV : IsRegularPotential V t t') : 0 < t' :=
  lt_of_lt_of_le hV.lower_pos hV.le_upper

theorem IsRegularPotential.hessian_nonneg {n : ℕ} {V : Space n → ℝ} {t t' : ℝ}
    (hV : IsRegularPotential V t t') (x v : Space n) :
    0 ≤ fderiv ℝ (fderiv ℝ V) x v v :=
  (mul_nonneg hV.lower_pos.le (sq_nonneg _)).trans (hV.lower_bound x v)

theorem IsRegularPotential.hessian_pos {n : ℕ} {V : Space n → ℝ} {t t' : ℝ}
    (hV : IsRegularPotential V t t') (x : Space n) {v : Space n} (hv : v ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ V) x v v :=
  (mul_pos hV.lower_pos (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le (hV.lower_bound x v)

end LeanBlast.KLS

end

end OAI
