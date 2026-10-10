import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Unselected
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ArithmeticClause
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SquarefreeExpression

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.ArithmeticSaving
open Finset Classical OrdinaryCorrelations.PivotSummation
variable {ι β : Type*} [DecidableEq ι] {k E : ℕ}

abbrev Unselected (e : Fin k ↪ ι) := {v : ι // v ∉ Set.range e}

noncomputable def splice (e : Fin k ↪ ι) (u : Unselected e → β) (v : Fin k → β) : ι → β :=
  fun a => if h : a ∈ Set.range e then v (Classical.choose h) else u ⟨a,h⟩

@[simp] lemma splice_selected (e : Fin k ↪ ι) (u : Unselected e → β) (v : Fin k → β) (i : Fin k) :
    splice e u v (e i) = v i := by
  unfold splice
  rw [dite_eq_left (show e i ∈ Set.range e from ⟨i,rfl⟩)]
  congr 1
  exact e.injective (Classical.choose_spec (show e i ∈ Set.range e from ⟨i,rfl⟩))

@[simp] lemma splice_unselected (e : Fin k ↪ ι) (u : Unselected e → β) (v : Fin k → β)
    (a : Unselected e) : splice e u v a.val = u a := by simp [splice,a.property]

noncomputable def assignmentEquiv (e : Fin k ↪ ι) :
    (Unselected e → β) × (Fin k → β) ≃ (ι → β) where
  toFun x := splice e x.1 x.2
  invFun x := (fun a => x a.val, fun i => x (e i))
  left_inv x := by ext a <;> simp only [splice_unselected,splice_selected]
  right_inv x := by
    funext a
    by_cases ha : a ∈ Set.range e
    · obtain ⟨i,rfl⟩ := ha
      exact splice_selected e _ _ i
    · simp only [splice,ha,dite_false]

noncomputable def prefixSplice (e : Fin k ↪ ι) (u : Unselected e → ℕ)
    (i : Fin k) (v : Fin i.val → ℕ) : ι → ℕ :=
  splice e u (fun j => if hj : j.val < i.val then v ⟨j,hj⟩ else 0)

lemma prefixSplice_agrees (e : Fin k ↪ ι) (u : Unselected e → ℕ) (v : Fin k → ℕ)
    (i : Fin k) (a : ι) (ha : ∀ j : Fin k, e j=a → j.val < i.val) :
    prefixSplice e u i (earlierTuple v i) a = splice e u v a := by
  by_cases hr : a ∈ Set.range e
  · obtain ⟨j,hj⟩ := hr
    have hij := ha j hj
    subst a
    simp only [prefixSplice,splice_selected,dite_eq_left hij,earlierTuple]
  · unfold prefixSplice
    simp only [splice,hr,dite_false]

structure TriangularExpressions (e : Fin k ↪ ι) (E : ℕ) where
  expression : Fin k → SquarefreeExpression ι E
  modulus : Fin k → ι
  linear : Fin k → Bool
  divisor_modulus : ∀ i, linear i=false → modulus i=e i
  divisor_own_absent : ∀ i, linear i=false → e i ∉ (expression i).support
  linear_modulus_ne : ∀ i, linear i=true → modulus i≠e i
  future_absent : ∀ i j, i<j → e j ∉ insert (modulus i) (expression i).support

namespace TriangularExpressions
variable {e : Fin k ↪ ι} (d : TriangularExpressions e E)

lemma support_agrees (u : Unselected e → ℕ) (v : Fin k → ℕ) (i : Fin k)
    (a : ι) (ha : a ∈ (d.expression i).support) (hne : a≠e i) :
    prefixSplice e u i (earlierTuple v i) a = splice e u v a := by
  apply prefixSplice_agrees
  intro j hj
  by_contra hn
  have hle : i.val ≤ j.val := by omega
  have hij : i<j := by
    apply lt_of_le_of_ne (show i≤j from hle)
    intro he
    subst j
    exact hne hj.symm
  exact d.future_absent i j hij (mem_insert_of_mem (hj.symm ▸ ha))

lemma modulus_agrees (u : Unselected e → ℕ) (v : Fin k → ℕ) (i : Fin k)
    (hi : d.linear i=true) :
    prefixSplice e u i (earlierTuple v i) (d.modulus i) = splice e u v (d.modulus i) := by
  apply prefixSplice_agrees
  intro j hj
  by_contra hn
  have hle : i.val ≤ j.val := by omega
  have hij : i<j := by
    apply lt_of_le_of_ne (show i≤j from hle)
    intro he
    subst j
    exact d.linear_modulus_ne i hi hj.symm
  exact d.future_absent i j hij (mem_insert.mpr (Or.inl hj))

lemma coefficient_agrees (u : Unselected e → ℕ) (v : Fin k → ℕ) (i : Fin k) :
    (d.expression i).linearCoeff (e i) (fun a => (prefixSplice e u i (earlierTuple v i) a:ℤ)) =
      (d.expression i).linearCoeff (e i) (fun a => ((splice e u v a : ℕ):ℤ)) := by
  apply SquarefreeExpression.linearCoeff_congr_on
  intro a ha hne
  exact congrArg Nat.cast (d.support_agrees u v i a ha hne)

lemma constant_agrees (u : Unselected e → ℕ) (v : Fin k → ℕ) (i : Fin k) :
    (d.expression i).constantTerm (e i) (fun a => (prefixSplice e u i (earlierTuple v i) a:ℤ)) =
      (d.expression i).constantTerm (e i) (fun a => ((splice e u v a : ℕ):ℤ)) := by
  apply SquarefreeExpression.constantTerm_congr_on
  intro a ha hne
  exact congrArg Nat.cast (d.support_agrees u v i a ha hne)

lemma divisor_agrees (u : Unselected e → ℕ) (v : Fin k → ℕ) (i : Fin k)
    (hi : d.linear i=false) :
    (d.expression i).eval (fun a => (prefixSplice e u i (earlierTuple v i) a:ℤ)) =
      (d.expression i).eval (fun a => ((splice e u v a : ℕ):ℤ)) := by
  apply SquarefreeExpression.eval_congr_on
  intro a ha
  apply congrArg Nat.cast
  apply d.support_agrees u v i a ha
  intro he
  exact d.divisor_own_absent i hi (he ▸ ha)

noncomputable def clause (u : Unselected e → ℕ) (i : Fin k) (v : Fin i.val → ℕ) : ArithmeticClause :=
  let x := prefixSplice e u i v
  if d.linear i then
    .linear ((d.expression i).linearCoeff (e i) (fun a => (x a:ℤ)))
      ((d.expression i).constantTerm (e i) (fun a => (x a:ℤ))) (x (d.modulus i))
  else .divisor ((d.expression i).eval (fun a => (x a:ℤ)))

lemma clause_actual (u : Unselected e → ℕ) (v : Fin k → ℕ) (i : Fin k) :
    d.clause u i (earlierTuple v i) =
      if d.linear i then
        .linear ((d.expression i).linearCoeff (e i) (fun a => ((splice e u v a : ℕ):ℤ)))
          ((d.expression i).constantTerm (e i) (fun a => ((splice e u v a : ℕ):ℤ)))
          (splice e u v (d.modulus i))
      else .divisor ((d.expression i).eval (fun a => ((splice e u v a : ℕ):ℤ))) := by
  by_cases hi : d.linear i=true
  · simp only [clause,hi,ite_true,d.coefficient_agrees,d.constant_agrees,d.modulus_agrees u v i hi]
  · have hf : d.linear i=false := Bool.eq_false_iff.mpr hi
    simp only [clause,hf,Bool.false_eq_true,ite_false,d.divisor_agrees u v i hf]

end TriangularExpressions
end OrdinaryCorrelations.ArithmeticSaving

end

end OAI
