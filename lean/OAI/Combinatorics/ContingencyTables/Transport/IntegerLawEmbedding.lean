import OAI.Combinatorics.ContingencyTables.Transport.IntegerEquivLaw

namespace OAI

/-! # Propagating a finite law inside a larger executable state box -/

namespace ContingencyTables.IntegerLaw
open scoped BigOperators Classical
noncomputable section

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable {Q : ℕ}

lemma push_count_injective (p : IntegerLaw A Q) (f : A → B)
    (hf : Function.Injective f) (a : A) : (p.push f).count (f a)=p.count a := by
  change (∑ x,if f x=f a then p.count x else 0)=_
  simp only [hf.eq_iff,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

/-- A transition matrix may contain unused box states. Starting in the
embedded state set gives exactly the pushed-forward original walk. -/
theorem walk_push_count (K : A → IntegerLaw A Q) (L : B → IntegerLaw B Q)
    (f : A → B) (hf : ∀ x,L (f x)=(K x).push f) (start : A) (N : ℕ) (b : B) :
    (walk L (f start) N).count b=((walk K start N).push f).count b := by
  induction N generalizing b with
  | zero =>
    change (if b=f start then 1 else 0)=∑ a,if f a=b then (if a=start then 1 else 0) else 0
    have he (a : A) : (if f a=b then (if a=start then 1 else 0) else 0)=
        if a=start then (if f start=b then 1 else 0) else 0 := by
      by_cases h : a=start <;> simp [h]
    simp_rw [he]
    simp [eq_comm]
  | succ N ih =>
    change (∑ y,(walk L (f start) N).count y*(L y).count b)=
      ∑ a,if f a=b then (∑ x,(walk K start N).count x*(K x).count a) else 0
    simp_rw [ih]
    change (∑ y,(∑ x,if f x=y then (walk K start N).count x else 0)*(L y).count b)=_
    simp_rw [Finset.sum_mul,ite_mul,zero_mul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    simp_rw [hf]
    change (∑ x,(walk K start N).count x*(∑ a,if f a=b then (K x).count a else 0))=_
    simp_rw [Finset.mul_sum,mul_ite,mul_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp

end
end ContingencyTables.IntegerLaw

end OAI
