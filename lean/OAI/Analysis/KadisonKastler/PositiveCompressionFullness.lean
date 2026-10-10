import OAI.Analysis.KadisonKastler.PublishedSimpleDerivation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

namespace OAI

/-! # Uniform algebraic fullness from a positive compression

The type III spectral-projection argument produces an isometry `v` for
which `v* x* x v` is bounded below. Inverting a normalized compression
gives explicit left and right factors with controlled norms.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
  [PartialOrder A] [StarOrderedRing A]

theorem exists_fullness_factors_of_positive_compression
    (x v : A) (hv : star v * v = 1) {t : ℝ} (ht : 0 < t)
    (hq : algebraMap ℝ A t ≤ star v * (star x * x) * v) :
    ∃ b c : A, ‖b‖ ≤ t⁻¹ * ‖x‖ ∧ ‖c‖ ≤ 1 ∧ b * x * c = 1 := by
  let q := star v * (star x * x) * v
  let qn : A := t⁻¹ • q
  have hqn : (1 : A) ≤ qn := by
    have h := smul_le_smul_of_nonneg_left hq (inv_nonneg.mpr ht.le)
    simpa only [Algebra.algebraMap_eq_smul_one, smul_smul,
      inv_mul_cancel₀ ht.ne', one_smul] using h
  have hunit : IsUnit qn := CStarAlgebra.isUnit_of_le 1 hqn
  let r : A := CFC.rpow qn (-1)
  have hr_nonneg : 0 ≤ r := CFC.rpow_nonneg
  have hr_le : r ≤ 1 := CStarAlgebra.rpow_neg_one_le_one hqn
  have hr_norm : ‖r‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg r hr_nonneg).mpr hr_le
  have hrq : r * qn = 1 := by
    obtain ⟨u, hu⟩ := hunit
    have hpos : 0 ≤ (u : A) := by simpa only [hu] using (zero_le_one.trans hqn)
    dsimp [r]
    rw [← hu, CFC.rpow_neg_one_eq_inv u hpos]
    exact u.inv_val
  have hvnorm : ‖v‖ ≤ 1 := by
    have h : ‖star v * v‖ = ‖v‖ * ‖v‖ := CStarRing.norm_star_mul_self
    rw [hv, norm_one] at h
    nlinarith [norm_nonneg v]
  refine ⟨(t⁻¹ : ℝ) • (r * star v * star x), v, ?_, hvnorm, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ht.le)
    calc
      ‖r * star v * star x‖ ≤ ‖r‖ * ‖v‖ * ‖x‖ := by
        simpa only [norm_star] using (norm_mul_le (r * star v) (star x)).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le r (star v)) (norm_nonneg (star x)))
      _ ≤ 1 * 1 * ‖x‖ := by gcongr
      _ = ‖x‖ := by ring
  · calc
      ((t⁻¹ : ℝ) • (r * star v * star x)) * x * v = r * qn := by
        simp only [qn, q, smul_mul_assoc, mul_smul_comm, mul_assoc]
      _ = 1 := hrq

end

end KadisonKastler

end OAI
