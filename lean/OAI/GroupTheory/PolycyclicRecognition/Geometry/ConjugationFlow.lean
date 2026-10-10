import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentFlow
import Mathlib.Analysis.Normed.Operator.Mul

namespace OAI

/-! # The actual conjugation flow of a matrix exponential

Left and right multiplication give the exponential formula for the adjoint
operator. This supplies the conjugation identity used by root distortion.
-/

noncomputable section

namespace PolycyclicRecognition

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def leftRegular : A →ₐ[ℝ] (A →L[ℝ] A) where
  toFun := ContinuousLinearMap.mul ℝ A
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' _ _ := by ext; simp
  map_mul' _ _ := by ext; simp [mul_assoc]
  commutes' _ := by ext; simp [Algebra.algebraMap_eq_smul_one]

def rightRegular : Aᵐᵒᵖ →ₐ[ℝ] (A →L[ℝ] A) where
  toFun x := (ContinuousLinearMap.mul ℝ A).flip x.unop
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' _ _ := by ext; simp
  map_mul' _ _ := by ext; simp [mul_assoc]
  commutes' _ := by ext; simp [Algebra.algebraMap_eq_smul_one]

theorem continuous_leftRegular : Continuous (leftRegular : A → (A →L[ℝ] A)) :=
  (ContinuousLinearMap.mul ℝ A).continuous

theorem continuous_rightRegular : Continuous (rightRegular : Aᵐᵒᵖ → (A →L[ℝ] A)) :=
  (ContinuousLinearMap.mul ℝ A).flip.continuous.comp MulOpposite.continuous_unop

def adjointOperator (x : A) : A →L[ℝ] A :=
  leftRegular x - rightRegular (MulOpposite.op x)

@[simp] theorem adjointOperator_apply (x y : A) :
    adjointOperator x y = x * y - y * x := rfl

variable [CompleteSpace A]

/-- Exponentiating the commutator operator gives actual conjugation. -/
theorem exp_adjointOperator_apply (x y : A) :
    (NormedSpace.exp (adjointOperator x)) y =
      NormedSpace.exp x * y * NormedSpace.exp (-x) := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  let : NormedAlgebra ℚ (A →L[ℝ] A) := NormedAlgebra.restrictScalars ℚ ℝ _
  let : NormedAlgebra ℚ Aᵐᵒᵖ := NormedAlgebra.restrictScalars ℚ ℝ _
  have hc : Commute (leftRegular x) (-rightRegular (MulOpposite.op x)) := by
    ext z
    simp [leftRegular, rightRegular, mul_assoc]
  rw [adjointOperator, sub_eq_add_neg, NormedSpace.exp_add_of_commute hc]
  have hl := NormedSpace.map_exp (leftRegular (A := A)) continuous_leftRegular x
  have hr := NormedSpace.map_exp (rightRegular (A := A)) continuous_rightRegular
    (MulOpposite.op (-x))
  have he : rightRegular (MulOpposite.op (-x)) = -rightRegular (MulOpposite.op x) := by
    rw [MulOpposite.op_neg, map_neg]
  rw [he] at hr
  rw [← hl, ← hr]
  simp only [NormedSpace.exp_op]
  simp [leftRegular, rightRegular, mul_assoc]

theorem exp_smul_adjointOperator_apply (t : ℝ) (x y : A) :
    (NormedSpace.exp (t • adjointOperator x)) y =
      NormedSpace.exp (t • x) * y * NormedSpace.exp (-(t • x)) := by
  have h : t • adjointOperator x = adjointOperator (t • x) := by
    ext y
    simp [smul_sub]
  rw [h, exp_adjointOperator_apply]

/-- A continuous linear intertwiner also intertwines the actual analytic
operator exponentials, so restricted root actions agree with ambient ones. -/
theorem exp_intertwine_apply
    {V U : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    (f : V →L[ℝ] U) (S : V →L[ℝ] V) (T : U →L[ℝ] U)
    (hf : ∀ v, f (S v) = T (f v)) (v : V) :
    f ((NormedSpace.exp S) v) = (NormedSpace.exp T) (f v) := by
  have hp (n : ℕ) (v : V) : f ((S ^ n) v) = (T ^ n) (f v) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', pow_succ']
      change f (S ((S ^ n) v)) = T ((T ^ n) (f v))
      rw [hf, ih]
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) S).map
    (f.comp (ContinuousLinearMap.apply ℝ V v))
    (f.comp (ContinuousLinearMap.apply ℝ V v)).continuous
  have ht := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) T).map
    (ContinuousLinearMap.apply ℝ U (f v))
    (ContinuousLinearMap.apply ℝ U (f v)).continuous
  have hs' : HasSum (fun n : ℕ => (n.factorial⁻¹ : ℝ) • (T ^ n) (f v))
      (f ((NormedSpace.exp S) v)) := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, smul_apply, map_smul, hp] using hs
  have ht' : HasSum (fun n : ℕ => (n.factorial⁻¹ : ℝ) • (T ^ n) (f v))
      ((NormedSpace.exp T) (f v)) := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply,
      smul_apply] using ht
  exact hs'.unique ht'

end PolycyclicRecognition

end

end OAI
