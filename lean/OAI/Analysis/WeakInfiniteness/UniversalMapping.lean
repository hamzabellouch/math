import Mathlib
import OAI.Analysis.WeakInfiniteness.PolynomialCompression
import OAI.Analysis.WeakInfiniteness.States

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
open scoped ComplexOrder

namespace WeakPureInfiniteness

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def algebraWord (x : A) : List Bool → A
  | [] => 1
  | i :: w => (if i then x else star x) * algebraWord x w

def algebraPolynomial (x : A) (c : List Bool →₀ ℂ) : A :=
  c.sum fun w a => a • algebraWord x w

lemma map_algebraWord (φ : A →⋆ₐ[ℂ] B) (x : A) (w : List Bool) :
    φ (algebraWord x w) = algebraWord (φ x) w := by
  induction w with
  | nil => exact map_one φ
  | cons i w ih => cases i <;> simp [algebraWord, ih, map_star]

lemma map_algebraPolynomial (φ : A →⋆ₐ[ℂ] B) (x : A) (c : List Bool →₀ ℂ) :
    φ (algebraPolynomial x c) = algebraPolynomial (φ x) c := by
  simp [algebraPolynomial, Finsupp.sum, map_algebraWord]

lemma algebraWord_operator {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) (w : List Bool) :
    algebraWord T w = wordEval (operatorLetters T) w := by
  induction w with
  | nil => rfl
  | cons i w ih => cases i <;> simp [algebraWord, ih, wordEval, operatorLetters,
      ContinuousLinearMap.mul_def]

lemma algebraWord_universal (w : List Bool) :
    algebraWord universalContractionGenerator w = universalWord w := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [algebraWord, universalWord, ih]

lemma algebraPolynomial_universal (c : List Bool →₀ ℂ) :
    algebraPolynomial universalContractionGenerator c = universalPolynomial c.support c := by
  simp only [algebraPolynomial, Finsupp.sum, algebraWord_universal, universalPolynomial]

lemma algebraPolynomial_operator {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) (c : List Bool →₀ ℂ) :
    algebraPolynomial T c = polynomialOperator c.support c T := by
  simp only [algebraPolynomial, Finsupp.sum, algebraWord_operator, polynomialOperator]

lemma norm_finitePolynomial_le_universal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (T : H →L[ℂ] H)
    (hT : ‖T‖ ≤ 1) (c : List Bool →₀ ℂ) :
    ‖algebraPolynomial T c‖ ≤ ‖algebraPolynomial universalContractionGenerator c‖ := by
  by_cases hn : Nontrivial H
  · let := hn
    let e := (stdOrthonormalBasis ℂ H).repr
    let : Nontrivial (EuclideanSpace ℂ (Fin (Module.finrank ℂ H))) := e.symm.toEquiv.nontrivial
    let D := e.conjStarAlgEquiv T
    have hD : ‖D‖ ≤ 1 := (NonUnitalStarAlgHom.norm_apply_le e.conjStarAlgEquiv T).trans hT
    let π : ContractionRepresentation :=
      { hilbert := { Carrier := EuclideanSpace ℂ (Fin (Module.finrank ℂ H)) }
        operator := D
        norm_operator_le_one := hD }
    have he := map_algebraPolynomial e.conjStarAlgEquiv.toStarAlgHom T c
    calc
      ‖algebraPolynomial T c‖ = ‖algebraPolynomial D c‖ := by
        change ‖algebraPolynomial T c‖ = ‖algebraPolynomial (e.conjStarAlgEquiv.toStarAlgHom T) c‖
        rw [← he]
        exact (StarAlgEquiv.norm_map e.conjStarAlgEquiv _).symm
      _ = ‖contractionEvaluation π (algebraPolynomial universalContractionGenerator c)‖ := by
        rw [map_algebraPolynomial]; rfl
      _ ≤ _ := NonUnitalStarAlgHom.norm_apply_le (contractionEvaluation π) _
  · let := not_nontrivial_iff_subsingleton.mp hn
    have hz : algebraPolynomial T c = 0 := Subsingleton.elim _ _
    rw [hz, norm_zero]
    exact norm_nonneg _

lemma norm_operatorPolynomial_le_universal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H)
    (hT : ‖T‖ ≤ 1) (c : List Bool →₀ ℂ) :
    ‖algebraPolynomial T c‖ ≤ ‖algebraPolynomial universalContractionGenerator c‖ := by
  rw [algebraPolynomial_operator]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro ξ
  let K := wordSpace (operatorLetters T) (fun _ : Unit => ξ) (c.support.sup List.length)
  let ξ₀ : K := ⟨ξ, testVector_mem_wordSpace _ _ _ ()⟩
  have he : (polynomialOperator c.support c (compress K T) ξ₀ : H) =
      polynomialOperator c.support c T ξ := polynomialOperator_compression_exact _ _ _ _
  rw [← he]
  have hb := norm_finitePolynomial_le_universal (compress K T) ((norm_compress_le _ _).trans hT) c
  rw [algebraPolynomial_operator] at hb
  exact (ContinuousLinearMap.le_opNorm _ ξ₀).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

lemma norm_algebraPolynomial_le_universal [PartialOrder A] [StarOrderedRing A]
    (x : A) (hx : ‖x‖ ≤ 1) (c : List Bool →₀ ℂ) :
    ‖algebraPolynomial x c‖ ≤ ‖algebraPolynomial universalContractionGenerator c‖ := by
  by_cases hn : Nontrivial A
  · let := hn
    obtain ⟨f, _, hf⟩ := exists_norming_gns (algebraPolynomial x c)
    rw [← hf, map_algebraPolynomial]
    exact norm_operatorPolynomial_le_universal _
      ((NonUnitalStarAlgHom.norm_apply_le f.gnsNonUnitalStarAlgHom x).trans hx) c
  · let := not_nontrivial_iff_subsingleton.mp hn
    rw [Subsingleton.elim (algebraPolynomial x c) 0, norm_zero]
    exact norm_nonneg _

end WeakPureInfiniteness
end

end OAI
