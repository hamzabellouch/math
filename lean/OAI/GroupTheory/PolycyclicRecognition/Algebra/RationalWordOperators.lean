import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalWordEvaluation

namespace OAI

/-! # Degree and signed reversal on rational words -/

noncomputable section
namespace PolycyclicRecognition

variable {n : ℕ}

def rationalWordDegree : RationalWords n →ₗ[ℚ] RationalWords n :=
  (Finsupp.linearCombination ℚ (fun w : FreeMonoid (Fin n) =>
    (w.length : ℚ) • MonoidAlgebra.single w 1)).comp
    (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

def rationalWordAntipode : RationalWords n →ₗ[ℚ] RationalWords n :=
  (Finsupp.linearCombination ℚ (fun w : FreeMonoid (Fin n) =>
    (-1 : ℚ) ^ w.length • MonoidAlgebra.single (FreeMonoid.ofList w.toList.reverse) 1)).comp
    (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

theorem rationalWordDegree_single (w : FreeMonoid (Fin n)) (q : ℚ) :
    rationalWordDegree (MonoidAlgebra.single w q) =
      q • ((w.length : ℚ) • MonoidAlgebra.single w 1) := by
  change Finsupp.linearCombination ℚ _ (Finsupp.single w q) = _
  exact Finsupp.linearCombination_single (R := ℚ)
    (v := fun w : FreeMonoid (Fin n) => (w.length : ℚ) • MonoidAlgebra.single w 1) q w

theorem rationalWordAntipode_single (w : FreeMonoid (Fin n)) (q : ℚ) :
    rationalWordAntipode (MonoidAlgebra.single w q) =
      q • ((-1 : ℚ) ^ w.length • MonoidAlgebra.single (FreeMonoid.ofList w.toList.reverse) 1) := by
  change Finsupp.linearCombination ℚ _ (Finsupp.single w q) = _
  exact Finsupp.linearCombination_single (R := ℚ)
    (v := fun w : FreeMonoid (Fin n) =>
      (-1 : ℚ) ^ w.length • MonoidAlgebra.single (FreeMonoid.ofList w.toList.reverse) 1) q w

theorem rationalWordDegree_letter_mul (i : Fin n) (p : RationalWords n) :
    rationalWordDegree (rationalWordLetter i * p) =
      rationalWordLetter i * p + rationalWordLetter i * rationalWordDegree p := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change rationalWordDegree (rationalWordLetter i * MonoidAlgebra.single w 1) =
      rationalWordLetter i * MonoidAlgebra.single w 1 +
        rationalWordLetter i * rationalWordDegree (MonoidAlgebra.single w 1)
    simp only [rationalWordLetter, MonoidAlgebra.single_mul_single, one_mul,
      rationalWordDegree_single, one_smul, Algebra.mul_smul_comm]
    simp only [FreeMonoid.length, FreeMonoid.toList_of_mul, List.length_cons,
      Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    exact add_comm _ _
  | add p q hp hq =>
    simp only [mul_add, map_add, hp, hq]
    abel
  | smul r p hp =>
    simp only [Algebra.mul_smul_comm, map_smul, hp, smul_add]

theorem rationalWordAntipode_letter_mul (i : Fin n) (p : RationalWords n) :
    rationalWordAntipode (rationalWordLetter i * p) =
      -(rationalWordAntipode p * rationalWordLetter i) := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change rationalWordAntipode (rationalWordLetter i * MonoidAlgebra.single w 1) =
      -(rationalWordAntipode (MonoidAlgebra.single w 1) * rationalWordLetter i)
    simp only [rationalWordLetter, MonoidAlgebra.single_mul_single, one_mul,
      rationalWordAntipode_single, one_smul, smul_mul_assoc]
    simp only [FreeMonoid.length, FreeMonoid.toList_of_mul, List.length_cons,
      List.reverse_cons, FreeMonoid.ofList_append, FreeMonoid.ofList_singleton,
      pow_succ, mul_neg, mul_one, neg_smul]
  | add p q hp hq => simp only [mul_add, map_add, hp, hq, add_mul, neg_add_rev]; abel
  | smul r p hp =>
    simp only [Algebra.mul_smul_comm, map_smul, hp, smul_mul_assoc, smul_neg]

end PolycyclicRecognition

end

end OAI
