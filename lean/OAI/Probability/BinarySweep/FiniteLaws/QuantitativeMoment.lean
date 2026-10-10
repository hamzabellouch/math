import Mathlib
import OAI.Probability.BinarySweep.Processes.Basic

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

lemma traceMoment_le_dimension_mul_pow {D q : ℕ} (hq : 0 < q)
    (K : RepSpace D →L[ℂ] RepSpace D) {η : ℝ} (hη : 0 ≤ η) (hK : ‖K‖ ≤ η) :
    traceMoment q K ≤ D * η ^ (2*q) := by
  let B := ((ContinuousLinearMap.adjoint K) * K) ^ q
  have hKK : ‖(ContinuousLinearMap.adjoint K) * K‖ ≤ η^2 := by
    calc
      _ ≤ ‖ContinuousLinearMap.adjoint K‖ * ‖K‖ := norm_mul_le _ _
      _ = ‖K‖ * ‖K‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
      _ ≤ η * η := mul_le_mul hK hK (norm_nonneg _) hη
      _ = _ := (sq η).symm
  have hB : ‖B‖ ≤ η ^ (2*q) := by
    calc
      _ ≤ ‖(ContinuousLinearMap.adjoint K) * K‖^q := norm_pow_le' _ hq
      _ ≤ (η^2)^q := pow_le_pow_left₀ (norm_nonneg _) hKK q
      _ = _ := (pow_mul η 2 q).symm
  unfold traceMoment
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin D) ℂ), Complex.re_sum]
  calc
    _ ≤ ∑ _i : Fin D, η^(2*q) := by
      apply Finset.sum_le_sum
      intro i _
      have hb : ‖EuclideanSpace.basisFun (Fin D) ℂ i‖ = 1 :=
        (EuclideanSpace.basisFun (Fin D) ℂ).orthonormal.1 i
      calc
        _ ≤ ‖inner ℂ (EuclideanSpace.basisFun (Fin D) ℂ i)
            (B (EuclideanSpace.basisFun (Fin D) ℂ i))‖ := Complex.re_le_norm _
        _ ≤ ‖EuclideanSpace.basisFun (Fin D) ℂ i‖ *
            ‖B (EuclideanSpace.basisFun (Fin D) ℂ i)‖ := norm_inner_le_norm _ _
        _ ≤ η^(2*q) := by
          rw [hb, one_mul]
          exact (B.le_opNorm _).trans (by rw [hb, mul_one]; exact hB)
    _ = _ := by simp

lemma logMoment_le_neg_log_dimension {D q : ℕ} (hD : 0 < D) (hq : 0 < q)
    (K : RepSpace D →L[ℂ] RepSpace D) (hK : ‖K‖ ≤ (D : ℝ)⁻¹) :
    logMoment (traceMoment q K) ≤ (-Real.log D : EReal) := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hi0 : 0 ≤ (D : ℝ)⁻¹ := inv_nonneg.mpr hD0.le
  have hi1 : (D : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hD0).mpr hD1
  have hm := traceMoment_le_dimension_mul_pow hq K hi0 hK
  have ht : traceMoment q K ≤ (D : ℝ)⁻¹ := by
    calc
      _ ≤ D * ((D : ℝ)⁻¹)^(2*q) := hm
      _ ≤ D * ((D : ℝ)⁻¹)^2 := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hi0 hi1 (by omega)) hD0.le
      _ = _ := by field_simp
  have he := ENNReal.log_le_log (ENNReal.ofReal_le_ofReal ht)
  simpa only [logMoment, ENNReal.log_ofReal_of_pos (inv_pos.mpr hD0), Real.log_inv, EReal.coe_neg] using he

end BinaryCoordinateSweeps

end

end OAI
