import OAI.Probability.SignedSweeps.GroupAverage
import OAI.Probability.SignedSweeps.Invariants

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma sweepOperator_norm_lt_one {d : ℕ} (lam : Partition (2 ^ d))
    (hl : 1 < lam.1.colLen 0) : ‖(sweepOperator lam).toContinuousLinearMap‖ < 1 := by
  apply opNorm_lt_one_of_pointwise
  intro x hx
  apply lt_of_le_of_ne (sweepOperator_contraction lam x)
  intro he
  have hf := sweep_norm_eq_implies_layer_fixed lam x he
  exact hx (specht_invariant_eq_zero lam hl x (fixed_by_layers_fixed_by_all lam x hf))

lemma linear_pow_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →ₗ[ℂ] E) {c : ℝ} (hc : 0 ≤ c) (hT : ∀ x, ‖T x‖ ≤ c * ‖x‖)
    (r : ℕ) (x : E) : ‖(T ^ r) x‖ ≤ c ^ r * ‖x‖ := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ']
    exact (hT _).trans ((mul_le_mul_of_nonneg_left ih hc).trans_eq (mul_assoc _ _ _).symm)

lemma linear_trace_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) {c : ℝ}
    (hT : ∀ x, ‖T x‖ ≤ c * ‖x‖) :
    (LinearMap.trace ℂ E T).re ≤ (finrank ℂ E : ℝ) * c := by
  classical
  let b := stdOrthonormalBasis ℂ E
  have h : ∀ i, (inner ℂ (b i) (T (b i))).re ≤ c := by
    intro i
    calc
      (inner ℂ (b i) (T (b i))).re ≤ ‖inner ℂ (b i) (T (b i))‖ := Complex.re_le_norm _
      _ ≤ ‖b i‖ * ‖T (b i)‖ := norm_inner_le_norm _ _
      _ ≤ ‖b i‖ * (c * ‖b i‖) := mul_le_mul_of_nonneg_left (hT _) (norm_nonneg _)
      _ = c := by simp only [b.norm_eq_one, one_mul, mul_one]
  rw [LinearMap.trace_eq_sum_inner T b, Complex.re_sum]
  simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)

lemma positiveSquare_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) :
    ‖(positiveSquare T).toContinuousLinearMap‖ = ‖T.toContinuousLinearMap‖ ^ 2 := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  change ‖T.adjoint.toContinuousLinearMap.comp T.toContinuousLinearMap‖ = _
  rw [LinearMap.adjoint_toContinuousLinearMap]
  simpa only [pow_two] using ContinuousLinearMap.norm_adjoint_comp_self T.toContinuousLinearMap

lemma weightedMoment_le_opNorm {d : ℕ} (lam : Partition (2 ^ d)) (r : ℕ) :
    weightedMoment lam r ≤ (spechtDimension lam : ℝ) ^ 2 *
      ‖(sweepOperator lam).toContinuousLinearMap‖ ^ (2 * r) := by
  have hbound (x : Specht lam) : ‖sweepSquare lam x‖ ≤
      (‖(sweepOperator lam).toContinuousLinearMap‖ ^ 2) * ‖x‖ := by
    rw [← positiveSquare_norm (sweepOperator lam)]
    exact (sweepSquare lam).toContinuousLinearMap.le_opNorm x
  have ht := linear_trace_bound (sweepSquare lam ^ r)
    (linear_pow_bound _ (sq_nonneg _) hbound r)
  unfold weightedMoment
  calc
    _ ≤ (spechtDimension lam : ℝ) *
        ((finrank ℂ (Specht lam) : ℝ) * (‖(sweepOperator lam).toContinuousLinearMap‖ ^ 2) ^ r) :=
      mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _)
    _ = _ := by rw [← pow_mul]; simp [spechtDimension, pow_two, mul_assoc]

lemma weightedMoment_tendsto_zero {d : ℕ} (lam : Partition (2 ^ d))
    (hl : 1 < lam.1.colLen 0) :
    Filter.Tendsto (weightedMoment lam) Filter.atTop (nhds 0) := by
  have hsq : ‖(sweepOperator lam).toContinuousLinearMap‖ ^ 2 < 1 := by
    nlinarith [sweepOperator_norm_lt_one lam hl, norm_nonneg (sweepOperator lam).toContinuousLinearMap]
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg _) hsq).const_mul
    ((spechtDimension lam : ℝ) ^ 2)
  simp only [mul_zero, ← pow_mul] at ht
  exact squeeze_zero (weightedMoment_nonneg lam) (weightedMoment_le_opNorm lam) ht

lemma eventually_weightedMoment_le_one {d : ℕ} (lam : Partition (2 ^ d))
    (hl : 1 < lam.1.colLen 0) :
    ∀ᶠ r in Filter.atTop, weightedMoment lam r ≤ 1 :=
  (weightedMoment_tendsto_zero lam hl).eventually_le_const (by norm_num)

end SignedSweeps
end

end OAI
