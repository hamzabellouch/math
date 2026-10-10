import OAI.Analysis.IrrationalRotation.Model.OperatorProperties
import OAI.Analysis.IrrationalRotation.Model.Product
import OAI.Analysis.IrrationalRotation.Analysis.FieldPowerBounds
import OAI.Analysis.IrrationalRotation.Rotation.WeightedShiftPowers
import OAI.Analysis.IrrationalRotation.Spectral.QuasinilpotentSeries

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.WeightedShift

theorem inner_single_operator_pow_eq_zero (w : Weight) (n : ℕ) (hn : 0 < n)
    (k : ℤ) (a : ℂ) :
    inner ℂ (lp.single 2 k a) ((operator w ^ n) (lp.single 2 k a)) = 0 := by
  rw [lp.inner_single_left, operator_pow_apply]
  have hk : k - (n : ℤ) ≠ k := by omega
  simp [lp.single_apply, hk]

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem vectorTrace_const_pow_eq_zero
    (T : Lp Hilbert 2 μ →L[ℂ] Lp Hilbert 2 μ) (w : X → Weight)
    (hT : ∀ ξ : Lp Hilbert 2 μ, T ξ =ᵐ[μ] fun x => operator (w x) (ξ x))
    (n : ℕ) (hn : 0 < n) (k : ℤ) (a : ℂ) :
    vectorTrace (Lp.const 2 μ (lp.single 2 k a)) (T ^ n) = 0 := by
  unfold vectorTrace
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [InvariantProjection.FieldPowerBounds.ae_pow_apply T
    (fun x => operator (w x)) hT n (Lp.const 2 μ (lp.single 2 k a)),
    Lp.coeFn_const 2 μ (lp.single 2 k a : Hilbert)] with x hpow hconst
  rw [hpow, hconst]
  exact inner_single_operator_pow_eq_zero (w x) n hn k a

end Invariant233.WeightedShift

namespace Invariant233.ProductModel

theorem shift_mul_multiplier_on_vector_ae (θ : ℕ → ℝ) (g : Base → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C)
    (ξ : Hilbert) :
    (shiftOperator * multiplier θ g C hC hg hb) ξ =ᵐ[baseMeasure]
      fun x => WeightedShift.operator (multiplierField θ g C hb x) (ξ x) := by
  have hm : multiplier θ g C hC hg hb ξ =ᵐ[baseMeasure]
      fun x => WeightedShift.diagonal (multiplierField θ g C hb x) (ξ x) := by
    unfold multiplier WeightedShift.fieldDiagonal WeightedShift.fieldDiagonalLinear
    exact WeightedShift.fieldDiagonalVec_ae (multiplierField θ g C hb) C hC
      (fun _x => lp.norm_le_of_forall_le hC (fun _k => hb _))
      (fun k => (hg.comp (Measurable.of_eval
        (fun i => (measurable_pi_apply i).add_const _))).aestronglyMeasurable) ξ
  filter_upwards [
    (WeightedShift.shift 1).toLinearIsometry.toContinuousLinearMap.coeFn_compLpL
      (multiplier θ g C hC hg hb ξ), hm] with x hs hm
  change shiftOperator (multiplier θ g C hC hg hb ξ) x = _
  rw [shiftOperator, hs, hm]
  rfl

theorem vectorTrace_shift_mul_multiplier_pow_eq_zero (θ : ℕ → ℝ) (g : Base → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C)
    (n : ℕ) (hn : 0 < n) :
    vectorTrace traceVector ((shiftOperator * multiplier θ g C hC hg hb) ^ n) = 0 :=
  WeightedShift.vectorTrace_const_pow_eq_zero _ _
    (shift_mul_multiplier_on_vector_ae θ g C hC hg hb) n hn 0 1

theorem vectorTrace_weightedOperator_pow_eq_zero (θ c : ℕ → ℝ)
    (n : ℕ) (hn : 0 < n) :
    vectorTrace traceVector (weightedOperator θ c ^ n) = 0 := by
  unfold weightedOperator
  exact vectorTrace_shift_mul_multiplier_pow_eq_zero θ _ _ _ _ _ n hn

theorem vectorTrace_traceVector_one : vectorTrace traceVector 1 = 1 := by
  unfold vectorTrace
  rw [one_apply_eq_self, L2.inner_def]
  calc
    (∫ x, inner ℂ (traceVector x) (traceVector x) ∂baseMeasure) =
        ∫ _x, (1 : ℂ) ∂baseMeasure := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_const 2 baseMeasure
        (lp.single 2 (0 : ℤ) (1 : ℂ) : Fiber)] with x hx
      change traceVector x = _ at hx
      simp [hx]
    _ = 1 := by simp

theorem vectorTrace_weightedOperator_inverse_one_sub_smul (θ c : ℕ → ℝ)
    (hT : NormQuasinilpotent (weightedOperator θ c)) (z : ℂ) :
    vectorTrace traceVector (Ring.inverse (1 - z • weightedOperator θ c)) = 1 := by
  rw [vectorTrace_inverse_one_sub_smul traceVector hT
    (vectorTrace_weightedOperator_pow_eq_zero θ c), vectorTrace_traceVector_one]

theorem vectorTrace_weightedOperator_resolvent (θ c : ℕ → ℝ)
    (hT : NormQuasinilpotent (weightedOperator θ c)) (z : ℂ) (hz : z ≠ 0) :
    vectorTrace traceVector (resolvent (weightedOperator θ c) z) = z⁻¹ := by
  rw [vectorTrace_resolvent_of_moments_zero traceVector hT
    (vectorTrace_weightedOperator_pow_eq_zero θ c) z hz,
    vectorTrace_traceVector_one, mul_one]

theorem vectorTrace_weightedOperator_logSeries_eq_zero (θ c : ℕ → ℝ)
    (hT : NormQuasinilpotent (weightedOperator θ c)) (z : ℂ) :
    vectorTrace traceVector (∑' n : ℕ,
      (-(z ^ (n + 1) / (n + 1 : ℂ))) • weightedOperator θ c ^ (n + 1)) = 0 :=
  vectorTrace_logSeries_eq_zero traceVector hT
    (vectorTrace_weightedOperator_pow_eq_zero θ c) z

end Invariant233.ProductModel

end

end OAI
