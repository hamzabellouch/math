import Mathlib
import OAI.Probability.BinarySweep.Processes.GridSweepPath

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma conditionalOperator_apply {b h D : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ)
    (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (RepSpace D)) (x : RepSpace D) :
    conditionalOperator H z ρ x = (conditionalNormalizer H z : ℂ)⁻¹ •
      ∑ g : GridChoices bits, if hg : pathEvent H g then
        (gridWeight bits z g : ℂ) • ρ (remainingPerm H g hg) x else 0 := by
  classical
  unfold conditionalOperator
  simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.smul_apply, LinearMap.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  split_ifs <;> rfl

theorem conditionalOperator_norm_le_one {b h D : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (RepSpace D))
    (hρ : IsUnitaryRep ρ) : ‖conditionalOperator H z ρ‖ ≤ 1 := by
  classical
  apply (conditionalOperator H z ρ).opNorm_le_bound (by norm_num)
  intro x
  rw [one_mul, conditionalOperator_apply, norm_smul]
  have hZ := conditionalNormalizer_pos H hz hz1
  have hsum : ‖∑ g : GridChoices bits, if hg : pathEvent H g then
      (gridWeight bits z g : ℂ) • ρ (remainingPerm H g hg) x else 0‖ ≤
      conditionalNormalizer H z * ‖x‖ := by
    calc
      _ ≤ ∑ g : GridChoices bits, ‖if hg : pathEvent H g then
        (gridWeight bits z g : ℂ) • ρ (remainingPerm H g hg) x else 0‖ := norm_sum_le _ _
      _ = _ := by
        unfold conditionalNormalizer
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro g _
        by_cases hg : pathEvent H g
        · simp only [dite_eq_left hg, ite_eq_left hg, norm_smul, hρ (remainingPerm H g hg) x,
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gridWeight_pos bits hz hz1 g)]
        · simp only [dite_eq_right hg, ite_eq_right hg, norm_zero, zero_mul]
  calc
    _ ≤ ‖(conditionalNormalizer H z : ℂ)⁻¹‖ * (conditionalNormalizer H z * ‖x‖) :=
      mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = ‖x‖ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ,
        ← mul_assoc, inv_mul_cancel₀ hZ.ne', one_mul]

theorem traceMoment_le_dimension {D : ℕ} (q : ℕ) (K : RepSpace D →L[ℂ] RepSpace D)
    (hK : ‖K‖ ≤ 1) : traceMoment q K ≤ D := by
  let B := ((ContinuousLinearMap.adjoint K) * K) ^ q
  have hB : ‖B‖ ≤ 1 := by
    cases q with
    | zero => exact ContinuousLinearMap.norm_id_le
    | succ q =>
      change ‖((ContinuousLinearMap.adjoint K) * K) ^ (q+1)‖ ≤ 1
      calc
        _ ≤ ‖(ContinuousLinearMap.adjoint K) * K‖ ^ (q+1) := norm_pow_le' _ (by omega)
        _ ≤ 1 ^ (q+1) := by
          gcongr
          calc
            _ ≤ ‖ContinuousLinearMap.adjoint K‖ * ‖K‖ := norm_mul_le _ _
            _ = ‖K‖ * ‖K‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
            _ ≤ 1 * 1 := mul_le_mul hK hK (norm_nonneg _) (by norm_num)
            _ = 1 := one_mul _
        _ = 1 := one_pow _
  unfold traceMoment
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin D) ℂ), Complex.re_sum]
  calc
    _ ≤ ∑ _i : Fin D, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have hb : ‖EuclideanSpace.basisFun (Fin D) ℂ i‖ = 1 :=
        (EuclideanSpace.basisFun (Fin D) ℂ).orthonormal.1 i
      calc
        _ ≤ ‖inner ℂ (EuclideanSpace.basisFun (Fin D) ℂ i)
            (B (EuclideanSpace.basisFun (Fin D) ℂ i))‖ := Complex.re_le_norm _
        _ ≤ ‖EuclideanSpace.basisFun (Fin D) ℂ i‖ *
            ‖B (EuclideanSpace.basisFun (Fin D) ℂ i)‖ := norm_inner_le_norm _ _
        _ ≤ 1 := by
          rw [hb, one_mul]
          exact (B.le_opNorm _).trans (by rw [hb, mul_one]; exact hB)
    _ = _ := by simp

lemma logMoment_traceMoment_le_log_dimension {D : ℕ} (q : ℕ)
    (K : RepSpace D →L[ℂ] RepSpace D) (hK : ‖K‖ ≤ 1) :
    logMoment (traceMoment q K) ≤ (Real.log D : EReal) := by
  have ht := traceMoment_le_dimension q K hK
  unfold logMoment
  cases D with
  | zero =>
    have he : ENNReal.ofReal (traceMoment q K) = 0 := ENNReal.ofReal_eq_zero.mpr (by simpa only [Nat.cast_zero] using ht)
    rw [he, ENNReal.log_zero]
    exact bot_le
  | succ D =>
    have hp : (0 : ℝ) < D+1 := by positivity
    have he := ENNReal.log_le_log (ENNReal.ofReal_le_ofReal ht)
    simpa only [Nat.cast_add, Nat.cast_one, ENNReal.log_ofReal_of_pos hp] using he

theorem conditional_moment_of_automatic_regime {b h D : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (q : ℕ) (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (RepSpace D))
    (hρ : IsUnitaryRep ρ)
    (ha : (1 + cExponent (gridSize bits)) * Real.log D ≤
      eExponent (gridSize bits) * h * Real.log (gridSize bits) - pathCost H) :
    logMoment (traceMoment q (conditionalOperator H z ρ)) ≤
      ((-cExponent (gridSize bits) * Real.log D +
        eExponent (gridSize bits) * h * Real.log (gridSize bits) - pathCost H : ℝ) : EReal) := by
  apply (logMoment_traceMoment_le_log_dimension q _
    (conditionalOperator_norm_le_one H hz hz1 ρ hρ)).trans
  exact_mod_cast (show Real.log D ≤ -cExponent (gridSize bits) * Real.log D +
    eExponent (gridSize bits) * h * Real.log (gridSize bits) - pathCost H by linarith)

end BinaryCoordinateSweeps

end

end OAI
