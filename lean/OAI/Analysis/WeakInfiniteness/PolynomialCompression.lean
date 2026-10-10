import Mathlib
import OAI.Analysis.WeakInfiniteness.UniversalFreeEmbedding
import OAI.Analysis.WeakInfiniteness.WordCompression

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint

namespace WeakPureInfiniteness

noncomputable def operatorLetters {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) :
    Bool → H →L[ℂ] H := fun i => if i then T else star T

noncomputable def universalWord : List Bool → UniversalContraction
  | [] => 1
  | i :: w => (if i then universalContractionGenerator else star universalContractionGenerator) *
      universalWord w

@[simp]
lemma contractionEvaluation_word (π : ContractionRepresentation) (w : List Bool) :
    contractionEvaluation π (universalWord w) = wordEval (operatorLetters π.operator) w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    cases i <;> simp [universalWord, wordEval, operatorLetters, ih,
      ContinuousLinearMap.mul_def]

noncomputable def universalPolynomial (s : Finset (List Bool)) (a : List Bool → ℂ) :
    UniversalContraction := ∑ w ∈ s, a w • universalWord w

noncomputable def polynomialOperator {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (s : Finset (List Bool))
    (a : List Bool → ℂ) (T : H →L[ℂ] H) : H →L[ℂ] H :=
  ∑ w ∈ s, a w • wordEval (operatorLetters T) w

@[simp]
lemma contractionEvaluation_polynomial (π : ContractionRepresentation)
    (s : Finset (List Bool)) (a : List Bool → ℂ) :
    contractionEvaluation π (universalPolynomial s a) = polynomialOperator s a π.operator := by
  simp [universalPolynomial, polynomialOperator]

lemma norm_universalPolynomial_le_iff (s : Finset (List Bool)) (a : List Bool → ℂ)
    {C : ℝ} (hC : 0 ≤ C) :
    ‖universalPolynomial s a‖ ≤ C ↔
      ∀ π : ContractionRepresentation, ‖polynomialOperator s a π.operator‖ ≤ C := by
  constructor
  · intro h π
    rw [← contractionEvaluation_polynomial]
    exact (NonUnitalStarAlgHom.norm_apply_le (contractionEvaluation π).toNonUnitalStarAlgHom _).trans h
  · intro h
    change ‖((universalPolynomial s a).val : ContractionAmbient)‖ ≤ C
    apply lp.norm_le_of_forall_le hC
    intro π
    change ‖contractionEvaluation π (universalPolynomial s a)‖ ≤ C
    rw [contractionEvaluation_polynomial]
    exact h π

section PolynomialCompression

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma operatorLetters_compress (K : Submodule ℂ H) [CompleteSpace K]
    (T : H →L[ℂ] H) (i : Bool) :
    operatorLetters (compress K T) i = compress K (operatorLetters T i) := by
  cases i
  · exact adjoint_compress K T
  · rfl

lemma polynomialOperator_compression_exact (s : Finset (List Bool)) (a : List Bool → ℂ)
    (T : H →L[ℂ] H) (ξ : H) :
    let m := s.sup List.length
    let K := wordSpace (operatorLetters T) (fun _ : Unit => ξ) m
    let ξ₀ : K := ⟨ξ, testVector_mem_wordSpace _ _ _ ()⟩
    (polynomialOperator s a (compress K T) ξ₀ : H) = polynomialOperator s a T ξ := by
  dsimp only
  let m := s.sup List.length
  let K := wordSpace (operatorLetters T) (fun _ : Unit => ξ) m
  let ξ₀ : K := ⟨ξ, testVector_mem_wordSpace _ _ _ ()⟩
  change K.subtypeL (polynomialOperator s a (compress K T) ξ₀) = _
  simp only [polynomialOperator, sum_apply, FunLike.coe_smul,
    Pi.smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro w hw
  congr 1
  have he : operatorLetters (compress K T) = fun i => compress K (operatorLetters T i) := by
    funext i
    exact operatorLetters_compress K T i
  rw [he]
  exact wordSpace_compression_exact (operatorLetters T) (fun _ : Unit => ξ) m w
    (Finset.le_sup hw) ()

lemma norm_universalPolynomial_le_of_finite_tests
    (s : Finset (List Bool)) (a : List Bool → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ π : ContractionRepresentation, FiniteDimensional ℂ π.hilbert →
      ‖polynomialOperator s a π.operator‖ ≤ C) :
    ‖universalPolynomial s a‖ ≤ C := by
  apply (norm_universalPolynomial_le_iff s a hC).mpr
  intro π
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro ξ
  by_cases hξ : ξ = 0
  · simp [hξ]
  let m := s.sup List.length
  let K := wordSpace (operatorLetters π.operator) (fun _ : Unit => ξ) m
  let : Nontrivial K := ⟨⟨⟨ξ, testVector_mem_wordSpace _ _ _ ()⟩, 0,
    fun he => hξ (congrArg Subtype.val he)⟩⟩
  let π₀ : ContractionRepresentation :=
    { hilbert := { Carrier := K }
      operator := compress K π.operator
      norm_operator_le_one := (norm_compress_le K π.operator).trans π.norm_operator_le_one }
  let ξ₀ : K := ⟨ξ, testVector_mem_wordSpace _ _ _ ()⟩
  have he : (polynomialOperator s a π₀.operator ξ₀ : π.hilbert) =
      polynomialOperator s a π.operator ξ := polynomialOperator_compression_exact s a π.operator ξ
  rw [← he]
  exact (ContinuousLinearMap.le_opNorm (polynomialOperator s a π₀.operator) ξ₀).trans
    (mul_le_mul_of_nonneg_right (h π₀ inferInstance) (norm_nonneg ξ₀))

end PolynomialCompression

end WeakPureInfiniteness
end

end OAI
