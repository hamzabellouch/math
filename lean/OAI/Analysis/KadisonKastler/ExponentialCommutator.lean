import OAI.Analysis.KadisonKastler.ClosedExponentialGenerator
import Mathlib.Analysis.Normed.Operator.Mul

namespace OAI

/-! # Exponentiating a bounded inner derivation -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The bounded commutator operator on a normed algebra. -/
def boundedCommutator (x : A) : A →L[ℂ] A :=
  ContinuousLinearMap.mul ℂ A x - (ContinuousLinearMap.mul ℂ A).flip x

omit [CompleteSpace A] in
@[simp] theorem boundedCommutator_apply (x y : A) :
    boundedCommutator x y = x * y - y * x := rfl

omit [CompleteSpace A] in
theorem norm_boundedCommutator_le (x : A) : ‖boundedCommutator x‖ ≤ 2 * ‖x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  change ‖x * y - y * x‖ ≤ _
  calc
    _ ≤ ‖x * y‖ + ‖y * x‖ := norm_sub_le _ _
    _ ≤ ‖x‖ * ‖y‖ + ‖y‖ * ‖x‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by ring

omit [CompleteSpace A] in
private theorem leftMul_pow_apply (x y : A) (n : ℕ) :
    ((ContinuousLinearMap.mul ℂ A x) ^ n) y = x ^ n * y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change x * (((ContinuousLinearMap.mul ℂ A x) ^ n) y) = _
    rw [ih, pow_succ', mul_assoc]

omit [CompleteSpace A] in
private theorem rightMul_pow_apply (x y : A) (n : ℕ) :
    (((ContinuousLinearMap.mul ℂ A).flip x) ^ n) y = y * x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change ((((ContinuousLinearMap.mul ℂ A).flip x) ^ n) y) * x = _
    rw [ih, pow_succ, mul_assoc]

private theorem exp_leftMul_apply (x y : A) :
    NormedSpace.exp (ContinuousLinearMap.mul ℂ A x) y = NormedSpace.exp x * y := by
  have h := (ContinuousLinearMap.apply ℂ A y).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (ContinuousLinearMap.mul ℂ A x))
  change HasSum (fun n : ℕ => (n.factorial⁻¹ : ℂ) •
    ((ContinuousLinearMap.mul ℂ A x) ^ n) y)
    (NormedSpace.exp (ContinuousLinearMap.mul ℂ A x) y) at h
  simp only [leftMul_pow_apply] at h
  have h' : HasSum (fun n : ℕ => (n.factorial⁻¹ : ℂ) • (x ^ n * y))
      (NormedSpace.exp x * y) := by
    simpa only [smul_mul_assoc] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) x).mul_right y
  exact h.unique h'

private theorem exp_rightMul_apply (x y : A) :
    NormedSpace.exp ((ContinuousLinearMap.mul ℂ A).flip x) y = y * NormedSpace.exp x := by
  have h := (ContinuousLinearMap.apply ℂ A y).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((ContinuousLinearMap.mul ℂ A).flip x))
  change HasSum (fun n : ℕ => (n.factorial⁻¹ : ℂ) •
    (((ContinuousLinearMap.mul ℂ A).flip x) ^ n) y)
    (NormedSpace.exp ((ContinuousLinearMap.mul ℂ A).flip x) y) at h
  simp only [rightMul_pow_apply] at h
  have h' : HasSum (fun n : ℕ => (n.factorial⁻¹ : ℂ) • (y * x ^ n))
      (y * NormedSpace.exp x) := by
    simpa only [mul_smul_comm] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) x).mul_left y
  exact h.unique h'

/-- The identity holds in every complete complex normed algebra. -/
theorem exp_boundedCommutator_apply (x y : A) :
    NormedSpace.exp (boundedCommutator x) y =
      NormedSpace.exp x * y * NormedSpace.exp (-x) := by
  let : NormedAlgebra ℚ (A →L[ℂ] A) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  have hc : Commute (ContinuousLinearMap.mul ℂ A x)
      (-((ContinuousLinearMap.mul ℂ A).flip x)) := by
    apply Commute.neg_right
    apply ContinuousLinearMap.ext
    intro z
    change x * (z * x) = (x * z) * x
    exact (mul_assoc _ _ _).symm
  rw [boundedCommutator, sub_eq_add_neg, NormedSpace.exp_add_of_commute hc]
  have he : -((ContinuousLinearMap.mul ℂ A).flip x) =
      (ContinuousLinearMap.mul ℂ A).flip (-x) := by rw [map_neg]
  rw [he]
  change NormedSpace.exp (ContinuousLinearMap.mul ℂ A x)
    (NormedSpace.exp ((ContinuousLinearMap.mul ℂ A).flip (-x)) y) = _
  rw [exp_leftMul_apply, exp_rightMul_apply, mul_assoc]

end

end KadisonKastler

end OAI
