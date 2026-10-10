import OAI.Analysis.KadisonSimilarity.Tracial.TracialMomentContinuity

namespace OAI

/-! Scalar homogeneity of each finite integer-power mixed word. -/

noncomputable section
namespace KadisonSimilarity
open HochschildPatching

variable {B I : Type*} [CStarAlgebra B]

def intWordCoeffNumber (a : Option I) (l : List (IntAtom I)) : ℕ :=
  coeffNumber a + (l.map (fun b => coeffNumber b.2)).sum

theorem integerEval_smul (F : I → B) (c : ℂ) (u : unitary B)
    (a : Option I) (l : List (IntAtom I)) :
    integerEval (fun i => c • F i) u a l =
      c ^ intWordCoeffNumber a l • integerEval F u a l := by
  have ht (l : List (IntAtom I)) :
      (l.map (fun b => ((u ^ b.1 : unitary B) : B) * wordCoeff (fun i => c • F i) b.2)).prod =
      c ^ (l.map (fun b => coeffNumber b.2)).sum •
        (l.map (fun b => ((u ^ b.1 : unitary B) : B) * wordCoeff F b.2)).prod := by
    induction l with
    | nil => simp
    | cons b l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [wordCoeff_smul, ih]
      simp only [pow_add, mul_smul_comm, smul_mul_assoc, smul_smul, mul_comm]
  unfold integerEval intWordCoeffNumber
  rw [wordCoeff_smul, ht, pow_add]
  simp only [mul_smul_comm, smul_mul_assoc, smul_smul, mul_comm]

def wordScalar (c : I → ℂ) : Option I → ℂ
  | none => 1
  | some i => c i

lemma wordCoeff_smul_family (F : I → B) (c : I → ℂ) (a : Option I) :
    wordCoeff (fun i => c i • F i) a = wordScalar c a • wordCoeff F a := by
  cases a <;> simp [wordCoeff, wordScalar]

/-- Each coefficient can be rescaled separately, including coefficients that
occur repeatedly in the word. -/
theorem integerEval_smul_family (F : I → B) (c : I → ℂ) (u : unitary B)
    (a : Option I) (l : List (IntAtom I)) :
    integerEval (fun i => c i • F i) u a l =
      (wordScalar c a * (l.map (fun b => wordScalar c b.2)).prod) • integerEval F u a l := by
  have ht (v : List (IntAtom I)) :
      (v.map (fun b => ((u ^ b.1 : unitary B) : B) * wordCoeff (fun i => c i • F i) b.2)).prod =
      (v.map (fun b => wordScalar c b.2)).prod •
        (v.map (fun b => ((u ^ b.1 : unitary B) : B) * wordCoeff F b.2)).prod := by
    induction v with
    | nil => simp
    | cons b v ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [wordCoeff_smul_family, ih]
      simp only [mul_smul_comm, smul_mul_assoc, smul_smul, mul_comm]
  unfold integerEval
  rw [wordCoeff_smul_family, ht]
  simp only [mul_smul_comm, smul_mul_assoc, smul_smul, mul_comm]

end KadisonSimilarity

end

end OAI
