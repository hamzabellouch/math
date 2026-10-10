import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Splice
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.CoordinateEquiv

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.ArithmeticSaving
open Finset Classical
variable {ι : Type*} [DecidableEq ι] {E k : ℕ}
namespace SquarefreeExpression

noncomputable def restrict (d : SquarefreeExpression ι E) (U : Finset ι) : SquarefreeExpression U E where
  factors i := univ.filter (fun p : U => p.val ∈ d.factors i)
  coefficient := d.coefficient

@[simp] lemma mem_restrict_factors (d : SquarefreeExpression ι E) (U : Finset ι) (i : Fin E) (p : U) :
    p ∈ (d.restrict U).factors i ↔ p.val ∈ d.factors i := by simp [restrict]

@[simp] lemma mem_restrict_support (d : SquarefreeExpression ι E) (U : Finset ι) (p : U) :
    p ∈ (d.restrict U).support ↔ p.val ∈ d.support := by
  simp only [support,mem_biUnion,mem_univ,true_and]
  apply exists_congr
  intro i
  simp only [restrict]
  split_ifs with hc <;> simp [hc]

lemma prod_restrict (d : SquarefreeExpression ι E) (U : Finset ι)
    (hU : ∀ i, d.factors i ⊆ U) (x : ι → ℤ) (i : Fin E) :
    (∏ p ∈ (d.restrict U).factors i, x p.val) = ∏ p ∈ d.factors i, x p := by
  apply prod_bij (fun p _ => p.val)
  · intro p hp; exact (mem_restrict_factors _ _ _ _).mp hp
  · intro p hp q hq he; exact Subtype.ext he
  · intro p hp
    exact ⟨⟨p,hU i hp⟩,(mem_restrict_factors _ _ _ _).mpr hp,rfl⟩
  · intro p hp; rfl

lemma eval_restrict (d : SquarefreeExpression ι E) (U : Finset ι)
    (hU : ∀ i, d.factors i ⊆ U) (x : ι → ℤ) :
    (d.restrict U).eval (fun p => x p.val) = d.eval x := by
  unfold eval
  apply sum_congr rfl
  intro i hi
  rw [d.prod_restrict U hU x i]
  rfl

lemma prod_restrict_erase (d : SquarefreeExpression ι E) (U : Finset ι)
    (hU : ∀ i, d.factors i ⊆ U) (x : ι → ℤ) (i : Fin E) (q : U) :
    (∏ p ∈ ((d.restrict U).factors i).erase q, x p.val) = ∏ p ∈ (d.factors i).erase q.val, x p := by
  apply prod_bij (fun p _ => p.val)
  · intro p hp
    obtain ⟨hp,hpm⟩ := mem_erase.mp hp
    exact mem_erase.mpr ⟨fun he => hp (Subtype.ext he),(mem_restrict_factors _ _ _ _).mp hpm⟩
  · intro p hp q hq he; exact Subtype.ext he
  · intro p hp
    obtain ⟨hp,hpm⟩ := mem_erase.mp hp
    refine ⟨⟨p,hU i hpm⟩,mem_erase.mpr ⟨?_,(mem_restrict_factors _ _ _ _).mpr hpm⟩,rfl⟩
    intro he
    exact hp (congrArg Subtype.val he)
  · intro p hp; rfl

lemma coefficient_restrict (d : SquarefreeExpression ι E) (U : Finset ι)
    (hU : ∀ i, d.factors i ⊆ U) (x : ι → ℤ) (q : U) :
    (d.restrict U).linearCoeff q (fun p => x p.val) = d.linearCoeff q.val x := by
  unfold linearCoeff
  apply sum_congr rfl
  intro i hi
  simp only [mem_restrict_factors]
  split_ifs
  · rw [d.prod_restrict_erase U hU x i q]
    rfl
  · rfl

lemma constant_restrict (d : SquarefreeExpression ι E) (U : Finset ι)
    (hU : ∀ i, d.factors i ⊆ U) (x : ι → ℤ) (q : U) :
    (d.restrict U).constantTerm q (fun p => x p.val) = d.constantTerm q.val x := by
  unfold constantTerm
  apply sum_congr rfl
  intro i hi
  simp only [mem_restrict_factors]
  split_ifs
  · rfl
  · rw [d.prod_restrict U hU x i]
    rfl
end SquarefreeExpression

namespace TriangularExpressions
variable {e : Fin k ↪ ι} (d : TriangularExpressions e E) (U : Finset ι)
    (he : ∀ i, e i ∈ U)

noncomputable def restrictEmbedding : Fin k ↪ U where
  toFun i := ⟨e i,he i⟩
  inj' := fun _ _ heq => e.injective (congrArg Subtype.val heq)

noncomputable def restrict (hm : ∀ i, d.modulus i ∈ U) :
    TriangularExpressions (restrictEmbedding U he) E where
  expression i := (d.expression i).restrict U
  modulus i := ⟨d.modulus i,hm i⟩
  linear := d.linear
  divisor_modulus i hi := Subtype.ext (d.divisor_modulus i hi)
  divisor_own_absent i hi := by
    rw [SquarefreeExpression.mem_restrict_support]
    exact d.divisor_own_absent i hi
  linear_modulus_ne i hi := fun heq => d.linear_modulus_ne i hi (congrArg Subtype.val heq)
  future_absent i j hij := by
    intro hp
    apply d.future_absent i j hij
    rcases mem_insert.mp hp with hp|hp
    · exact mem_insert.mpr (Or.inl (congrArg Subtype.val hp))
    · exact mem_insert_of_mem ((SquarefreeExpression.mem_restrict_support _ _ _).mp hp)

lemma numericClause_restrict [Fintype ι] (hm : ∀ i, d.modulus i ∈ U)
    (hf : ∀ i j, (d.expression i).factors j ⊆ U) (x : ι → ℕ) (i : Fin k) :
    (d.restrict U he hm).numericClause i (fun p => x p.val) = d.numericClause i x := by
  by_cases hlin : d.linear i = true
  · have hr : (d.restrict U he hm).linear i = true := hlin
    rw [numericClause, ite_eq_left hr, numericClause, ite_eq_left hlin]
    change ArithmeticClause.linear
      (((d.expression i).restrict U).linearCoeff (restrictEmbedding U he i) (fun p => (x p.val:ℤ)))
      (((d.expression i).restrict U).constantTerm (restrictEmbedding U he i) (fun p => (x p.val:ℤ)))
      (x (d.modulus i)) = _
    rw [(d.expression i).coefficient_restrict U (hf i) (fun a => (x a:ℤ)) (restrictEmbedding U he i),
      (d.expression i).constant_restrict U (hf i) (fun a => (x a:ℤ)) (restrictEmbedding U he i)]
    rfl
  · have hr : ¬(d.restrict U he hm).linear i = true := hlin
    rw [numericClause, ite_eq_right hr, numericClause, ite_eq_right hlin]
    change ArithmeticClause.divisor (((d.expression i).restrict U).eval (fun p => (x p.val:ℤ))) = _
    rw [(d.expression i).eval_restrict U (hf i) (fun a => (x a:ℤ))]

lemma admissible_restrict [Fintype ι] (hm : ∀ i, d.modulus i ∈ U)
    (hf : ∀ i j, (d.expression i).factors j ⊆ U) (P K : ℝ) (x : ι → ℕ)
    (hx : d.Admissible P K x) : (d.restrict U he hm).Admissible P K (fun p => x p.val) := by
  intro i
  rw [d.numericClause_restrict U he hm hf x i]
  exact hx i

end TriangularExpressions
end OrdinaryCorrelations.ArithmeticSaving

end

end OAI
