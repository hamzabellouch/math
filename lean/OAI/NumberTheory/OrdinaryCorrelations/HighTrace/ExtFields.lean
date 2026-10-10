import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SquarefreeExpression

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.ArithmeticSaving.SquarefreeExpression
open Finset Classical
variable {α β : Type*} [DecidableEq α] [DecidableEq β] {E : ℕ}

lemma ext_fields (d e : SquarefreeExpression α E) (hf : d.factors=e.factors)
    (hc : d.coefficient=e.coefficient) : d=e := by
  cases d; cases e
  dsimp only at hf hc
  subst_vars
  rfl

noncomputable def relabel (d : SquarefreeExpression α E) (e : α ↪ β) : SquarefreeExpression β E where
  factors i := (d.factors i).image e
  coefficient := d.coefficient

@[simp] lemma factors_relabel (d : SquarefreeExpression α E) (e : α ↪ β) (i : Fin E) :
    (d.relabel e).factors i=(d.factors i).image e := rfl

@[simp] lemma coefficient_relabel (d : SquarefreeExpression α E) (e : α ↪ β) (i : Fin E) :
    (d.relabel e).coefficient i=d.coefficient i := rfl

@[simp] lemma mem_relabel_factor (d : SquarefreeExpression α E) (e : α ↪ β) (i : Fin E) (p : α) :
    e p ∈ (d.relabel e).factors i ↔ p ∈ d.factors i := by
  simp only [factors_relabel,mem_image,e.injective.eq_iff,exists_eq_right]

lemma support_relabel (d : SquarefreeExpression α E) (e : α ↪ β) :
    (d.relabel e).support=d.support.image e := by
  ext p
  change p ∈ (univ : Finset (Fin E)).biUnion
    (fun i => if d.coefficient i=0 then ∅ else (d.factors i).image e) ↔ _
  rw [mem_biUnion]
  simp only [mem_univ,true_and,mem_image]
  constructor
  · rintro ⟨i,hi⟩
    by_cases hc : d.coefficient i=0
    · simp [hc] at hi
    · rw [ite_eq_right hc] at hi
      obtain ⟨q,hq,rfl⟩ := mem_image.mp hi
      exact ⟨q,d.mem_support hc hq,rfl⟩
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨i,hi,hq⟩ := mem_biUnion.mp hq
    by_cases hc : d.coefficient i=0
    · simp [hc] at hq
    · refine ⟨i,?_⟩
      rw [ite_eq_right hc] at hq ⊢
      exact mem_image.mpr ⟨q,hq,rfl⟩

lemma eval_relabel (d : SquarefreeExpression α E) (e : α ↪ β) (x : β → ℤ) :
    (d.relabel e).eval x=d.eval (fun p => x (e p)) := by
  unfold eval
  apply sum_congr rfl
  intro i hi
  simp only [coefficient_relabel,factors_relabel,prod_image e.injective.injOn]

lemma linearCoeff_relabel (d : SquarefreeExpression α E) (e : α ↪ β) (x : β → ℤ) (q : α) :
    (d.relabel e).linearCoeff (e q) x=d.linearCoeff q (fun p => x (e p)) := by
  unfold linearCoeff
  apply sum_congr rfl
  intro i hi
  simp only [mem_relabel_factor,coefficient_relabel]
  split_ifs
  · congr 1
    have he : ((d.factors i).image e).erase (e q)=((d.factors i).erase q).image e := by
      ext p
      simp only [mem_erase,mem_image]
      constructor
      · rintro ⟨hn,⟨r,hr,rfl⟩⟩
        exact ⟨r,⟨fun h => hn (congrArg e h),hr⟩,rfl⟩
      · rintro ⟨r,⟨hr,hmem⟩,rfl⟩
        exact ⟨fun h => hr (e.injective h),⟨r,hmem,rfl⟩⟩
    rw [factors_relabel,he,prod_image e.injective.injOn]
  · rfl

lemma constant_relabel (d : SquarefreeExpression α E) (e : α ↪ β) (x : β → ℤ) (q : α) :
    (d.relabel e).constantTerm (e q) x=d.constantTerm q (fun p => x (e p)) := by
  unfold constantTerm
  apply sum_congr rfl
  intro i hi
  simp only [mem_relabel_factor,coefficient_relabel]
  split_ifs
  · rfl
  · simp only [factors_relabel,prod_image e.injective.injOn]

end OrdinaryCorrelations.ArithmeticSaving.SquarefreeExpression

end

end OAI
