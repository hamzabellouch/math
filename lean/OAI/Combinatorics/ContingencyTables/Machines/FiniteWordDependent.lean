import OAI.Combinatorics.ContingencyTables.Transport.FiniteDependentLaw
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordWalk

namespace OAI

/-! # Independent words with a state-dependent second output -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture FairBits

noncomputable section

variable {A B X Z : Type*} [Fintype A] [Fintype B] [Fintype X] [Fintype Z]

lemma mapLaw_product_bind [DecidableEq Z] (p : RationalLaw A) (q : RationalLaw B)
    (f : A → B → Z) :
    mapLaw (productLaw p q) (fun ab => f ab.1 ab.2)=
      bindLaw p (fun a => mapLaw q (f a)) := by
  apply RationalLaw.ext
  funext z
  simp only [mapLaw,productLaw,bindLaw,Fintype.sum_prod_type,Finset.mul_sum,mul_ite,mul_zero]

omit [Fintype Z] in
/-- Fresh terminal bits are independent of the bits used to obtain the
state, even though the completion space depends on that state. -/
theorem mapLaw_dependent_product {Y : X → Type*} [∀ x,Fintype (Y x)]
    [DecidableEq X] [∀ x,DecidableEq (Y x)]
    (p : RationalLaw A) (q : RationalLaw B) (f : A → X) (g : (x : X) → B → Y x) :
    mapLaw (productLaw p q) (fun ab => (⟨f ab.1,g (f ab.1) ab.2⟩ : Sigma Y))=
      dependentJointLaw (mapLaw p f) (fun x => mapLaw q (g x)) := by
  apply RationalLaw.ext
  funext z
  rcases z with ⟨x,y⟩
  simp only [mapLaw,productLaw,dependentJointLaw,Fintype.sum_prod_type,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : f a=x
  · subst x
    simp only [Sigma.mk.inj_iff,heq_eq_eq,true_and,ite_true,Finset.mul_sum,mul_ite,mul_zero]
  · have hn (b : B) : (⟨f a,g (f a) b⟩ : Sigma Y)≠⟨x,y⟩ :=
      fun hh => h (congrArg Sigma.fst hh)
    simp only [hn,ite_false,h,Finset.sum_const_zero,zero_mul]


/-- First drawing a state and then applying a fresh common word to that
state gives the corresponding composition of output laws. -/
theorem mapLaw_product_finish [DecidableEq X] [DecidableEq Z]
    (p : RationalLaw A) (q : RationalLaw B) (f : A → X) (finish : X → B → Z) :
    mapLaw (productLaw p q) (fun ab => finish (f ab.1) ab.2)=
      bindLaw (mapLaw p f) (fun x => mapLaw q (finish x)) := by
  apply RationalLaw.ext
  funext z
  simp only [mapLaw,productLaw,bindLaw,Fintype.sum_prod_type]
  symm
  calc
    _ = ∑ a,p.mass a*(∑ b,if finish (f a) b=z then q.mass b else 0) := by
      simp_rw [Finset.sum_mul,ite_mul,zero_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> simp

end
end ContingencyTables.FirstSuccess

end OAI
