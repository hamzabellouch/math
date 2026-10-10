import Mathlib

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.MatrixAlphabet

open Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

def letter (o i : I) : Matrix I I ℂ := single o i 1 + single i o 1

omit [Fintype I] in
@[simp] lemma star_letter (o i : I) : star (letter o i) = letter o i := by
  simp only [letter, star_add, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single,
    star_one, add_comm]

lemma trace_letter (o i : I) (hi : i ≠ o) : (letter o i).trace = 0 := by
  simp [letter, Matrix.trace_single_eq_of_ne _ _ _ hi, Matrix.trace_single_eq_of_ne _ _ _ hi.symm]

lemma trace_mul_letter (o i j : I) (hi : i ≠ o) (hj : j ≠ o) :
    (letter o i * letter o j).trace = if i = j then 2 else 0 := by
  classical
  simp only [letter, add_mul, mul_add, Matrix.trace_add]
  rw [Matrix.single_mul_single_of_ne (1 : ℂ) o i o hi 1,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne (1 : ℂ) i o j hj.symm 1]
  simp only [Matrix.trace_zero, zero_add, one_mul]
  by_cases h : i = j
  · subst j
    norm_num
  · rw [Matrix.single_mul_single_of_ne (1 : ℂ) o i j h 1]
    simp [h, Matrix.trace_single_eq_of_ne _ _ _ h]

noncomputable def scale : ℂ := (Real.sqrt ((Fintype.card I : ℝ) / 2) : ℂ)

omit [DecidableEq I] in
@[simp] lemma star_scale : star (scale (I := I)) = scale (I := I) := by
  simp [scale]

omit [DecidableEq I] in
lemma scale_sq : (scale (I := I)) ^ 2 = (Fintype.card I : ℂ) / 2 := by
  rw [scale, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
  push_cast
  rfl

noncomputable def normalizedLetter (o i : I) : Matrix I I ℂ := scale (I := I) • letter o i

@[simp] lemma star_normalizedLetter (o i : I) :
    star (normalizedLetter o i) = normalizedLetter o i := by
  simp only [normalizedLetter, star_smul, star_scale, star_letter]

lemma trace_normalizedLetter (o i : I) (hi : i ≠ o) : (normalizedLetter o i).trace = 0 := by
  simp only [normalizedLetter, Matrix.trace_smul, trace_letter o i hi, smul_zero]

lemma normalized_trace_mul [Nonempty I] (o i j : I) (hi : i ≠ o) (hj : j ≠ o) :
    (Fintype.card I : ℂ)⁻¹ * (normalizedLetter o i * normalizedLetter o j).trace =
      if i = j then 1 else 0 := by
  have hm : (Fintype.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  rw [normalizedLetter, normalizedLetter, smul_mul_smul_comm, Matrix.trace_smul,
    trace_mul_letter o i j hi hj]
  simp only [smul_eq_mul, ← sq, scale_sq]
  split_ifs <;> field_simp
  norm_num

end Kadison.MatrixAlphabet
end

end OAI
