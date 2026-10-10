import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.DisjointBlock
variable {O : Type*} [Fintype O]

def pairCount (U : Fin 2 → O → Bool) (o : O) : ℕ :=
  (U 0 o).toNat + (U 1 o).toNat

def assignmentSet (U : Fin 2 → O → Bool) : Finset O := by
  classical
  exact Finset.univ.filter (fun o => pairCount U o = 1 ∧ U 0 o = true)

def outsideArray (c : O → ℕ) (A : Finset O) (i : Fin 2) (o : O) : Bool := by
  classical
  exact if i = 0 then decide (c o = 2 ∨ (c o = 1 ∧ o ∈ A))
    else decide (c o = 2 ∨ (c o = 1 ∧ o ∉ A))

omit [Fintype O] in
theorem pairCount_le_two (U : Fin 2 → O → Bool) (o : O) : pairCount U o ≤ 2 := by
  unfold pairCount
  cases U 0 o <;> cases U 1 o <;> decide

 theorem assignmentSet_subset (U : Fin 2 → O → Bool) :
    assignmentSet U ⊆ Finset.univ.filter (fun o => pairCount U o = 1) := by
  classical
  intro o ho
  simpa only [assignmentSet, Finset.mem_filter, Finset.mem_univ, true_and] using (Finset.mem_filter.mp ho).2.1

 theorem outsideArray_encode (U : Fin 2 → O → Bool) :
    outsideArray (pairCount U) (assignmentSet U) = U := by
  classical
  funext i o
  simp only [outsideArray, assignmentSet, Finset.mem_filter, Finset.mem_univ, true_and]
  fin_cases i <;>
    cases h0 : U 0 o <;> cases h1 : U 1 o <;>
    simp [pairCount, h0, h1]

 theorem pairCount_outsideArray (c : O → ℕ) (hc : ∀ o, c o ≤ 2)
    (A : Finset O) (hA : A ⊆ Finset.univ.filter (fun o => c o = 1)) (o : O) :
    pairCount (outsideArray c A) o = c o := by
  classical
  have hmem : o ∈ A → c o = 1 := fun ho => (Finset.mem_filter.mp (hA ho)).2
  have hcases : c o = 0 ∨ c o = 1 ∨ c o = 2 := by have := hc o; omega
  rcases hcases with h | h | h <;> by_cases ho : o ∈ A <;>
    simp [pairCount, outsideArray, h, ho] at *

 theorem assignmentSet_outsideArray (c : O → ℕ) (hc : ∀ o, c o ≤ 2)
    (A : Finset O) (hA : A ⊆ Finset.univ.filter (fun o => c o = 1)) :
    assignmentSet (outsideArray c A) = A := by
  classical
  ext o
  simp only [assignmentSet, Finset.mem_filter, Finset.mem_univ, true_and,
    pairCount_outsideArray c hc A hA]
  have hmem : o ∈ A → c o = 1 := fun ho => (Finset.mem_filter.mp (hA ho)).2
  by_cases ho : o ∈ A
  · simp [outsideArray, ho, hmem ho]
  · simp [outsideArray, ho]
    omega

def arrayEquivAssignments (c : O → ℕ) (hc : ∀ o, c o ≤ 2) :
    {U : Fin 2 → O → Bool // ∀ o, pairCount U o = c o} ≃
      {A : Finset O // A ⊆ Finset.univ.filter (fun o => c o = 1)} where
  toFun U := ⟨assignmentSet U.val, by
    intro o ho
    have h := assignmentSet_subset U.val ho
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, U.property] using h⟩
  invFun A := ⟨outsideArray c A.val, pairCount_outsideArray c hc A.val A.property⟩
  left_inv U := by
    apply Subtype.ext
    have hfun : pairCount U.val = c := funext U.property
    change outsideArray c (assignmentSet U.val) = U.val
    calc
      outsideArray c (assignmentSet U.val) = outsideArray (pairCount U.val) (assignmentSet U.val) :=
        congrArg (fun e : O → ℕ => outsideArray e (assignmentSet U.val)) hfun.symm
      _ = U.val := outsideArray_encode U.val
  right_inv A := by
    apply Subtype.ext
    exact assignmentSet_outsideArray c hc A.val A.property

def doubleSet (c : O → ℕ) : Finset O := by
  classical
  exact Finset.univ.filter (fun o => c o = 2)

def singleSet (c : O → ℕ) : Finset O := by
  classical
  exact Finset.univ.filter (fun o => c o = 1)

 theorem outsideArray_first_sum (c : O → ℕ) (A : Finset O)
    (hA : A ⊆ singleSet c) :
    (∑ o, (outsideArray c A 0 o).toNat) = (doubleSet c).card + A.card := by
  classical
  have hpoint (o : O) : (outsideArray c A 0 o).toNat =
      (if c o = 2 then 1 else 0) + (if o ∈ A then 1 else 0) := by
    have hmem : o ∈ A → c o = 1 := fun ho => (Finset.mem_filter.mp (hA ho)).2
    by_cases ho : o ∈ A
    · simp [outsideArray, ho, hmem ho]
    · simp [outsideArray, ho]
      by_cases h2 : c o = 2 <;> simp [h2]
  simp_rw [hpoint, Finset.sum_add_distrib]
  simp [doubleSet]

 theorem outsideArray_second_sum [DecidableEq O] (c : O → ℕ) (A : Finset O) :
    (∑ o, (outsideArray c A 1 o).toNat) =
      (doubleSet c).card + ((singleSet c) \ A).card := by
  classical
  have hpoint (o : O) : (outsideArray c A 1 o).toNat =
      (if c o = 2 then 1 else 0) + (if c o = 1 ∧ o ∉ A then 1 else 0) := by
    by_cases h2 : c o = 2
    · have h1 : c o ≠ 1 := by omega
      simp [outsideArray, h2]
    · by_cases h1 : c o = 1 <;> by_cases ho : o ∈ A <;> simp [outsideArray, h2, h1, ho]
  have hset : Finset.univ.filter (fun o => c o = 1 ∧ o ∉ A) = singleSet c \ A := by
    ext o
    simp [singleSet]
  simp_rw [hpoint, Finset.sum_add_distrib]
  simp [doubleSet, hset]

end Problem315.DisjointBlock

end

end OAI
