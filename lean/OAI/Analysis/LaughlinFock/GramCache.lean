import Mathlib
import OAI.Analysis.LaughlinFock.FastCoupling

namespace OAI

/-! Gram Cache. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def kernelHighestTerm (D : ℕ) (r : CopyLabel D) (A : Occupation 24)
    (x y j k : Orbital 24) : ℚ :=
  if x<y ∧ j<k ∧ (x.val+y.val-1)+j.val+k.val=D then
    (fastIntegerCopyPolynomial D D r.val.val (x.val+y.val-1) j.val k.val : ℚ) *
      ((x.val:ℚ)-(y.val:ℚ)) * (x.val+y.val-1).factorial * j.val.factorial * k.val.factorial *
      rationalWordVacuum [x,y,j,k] A
  else 0

def kernelHighestEntry (D : ℕ) (r : CopyLabel D) (A : Occupation 24) : ℚ :=
  ∑ j ∈ A, ∑ k ∈ A, ∑ x ∈ A, ∑ y ∈ A, kernelHighestTerm D r A x y j k

theorem integerHighestEntry_kernel (D : ℕ) (r : CopyLabel D) (A : Occupation 24) :
    integerHighestEntry D r A = kernelHighestEntry D r A := by
  simp only [integerHighestEntry, kernelHighestEntry, integerHighestTerm, kernelHighestTerm,
    integerCopyPolynomial_fast]

def highestLookup (xs : List (Occupation 24 × List ℚ)) (r : ℕ) (A : Occupation 24) : ℚ :=
  (((xs.find? (fun row => row.1=A)).map Prod.snd).getD []).getD (r/2) 0

def cachedFourGram (D : ℕ) (xs : List (Occupation 24 × List ℚ)) :
    Matrix (CopyLabel D) (CopyLabel D) ℚ := fun r s =>
  ∑ A ∈ highestFourOccupations D,
    2 * highestLookup xs r.val.val A * highestLookup xs s.val.val A /
      (2^(2*D) * occupationFactorial A)

theorem integerFourGram_cached (D : ℕ) (xs : List (Occupation 24 × List ℚ))
    (h : ∀ r A, A ∈ highestFourOccupations D →
      kernelHighestEntry D r A = highestLookup xs r.val.val A) :
    integerFourGram D = cachedFourGram D xs := by
  ext r s
  apply Finset.sum_congr rfl
  intro A hA
  rw [integerHighestEntry_kernel, integerHighestEntry_kernel, h r A hA, h s A hA]

def boundedMatrixEntriesDecidable {ι κ : Type*} [Fintype ι] {α : Type*} [DecidableEq α]
    (s : Finset κ) (A B : ι → κ → α) : Decidable (∀ i, ∀ a∈s, A i a = B i a) :=
  @Fintype.decidableForallFintype _ _ (fun _ => Finset.decidableDforallFinset) _

def boundedEntriesDecidable {κ : Type*} {α : Type*} [DecidableEq α]
    (s : Finset κ) (A B : κ → α) : Decidable (∀ a∈s, A a = B a) :=
  Finset.decidableDforallFinset (p := fun a _ => A a = B a)

end LaughlinFock
end

end OAI
