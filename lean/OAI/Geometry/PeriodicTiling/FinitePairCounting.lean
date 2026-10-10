import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Prod
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases

namespace OAI

universe uV uC uι uA uB

namespace PeriodicTilingThree

open scoped BigOperators Classical

section

variable {V : Type uV} {C : Type uC} [Fintype V] [Fintype C] {k : ℕ}

noncomputable def allBadAssignments
    (pair : (Fin k × Fin 2) ↪ V) (Good : Fin k → Finset (C × C)) :
    Finset (V → C) := by
  classical
  exact Finset.univ.filter fun f =>
    ∀ j, (f (pair (j, 0)), f (pair (j, 1))) ∉ Good j

@[simp] theorem mem_allBadAssignments
    (pair : (Fin k × Fin 2) ↪ V) (Good : Fin k → Finset (C × C)) (f : V → C) :
    f ∈ allBadAssignments pair Good ↔
      ∀ j, (f (pair (j, 0)), f (pair (j, 1))) ∉ Good j := by
  classical
  simp [allBadAssignments]

private abbrev Outside (pair : (Fin k × Fin 2) ↪ V) :=
  {v : V // v ∉ Set.range pair}

private noncomputable def vertexDecomposition (pair : (Fin k × Fin 2) ↪ V) :
    ((Fin k × Fin 2) ⊕ Outside pair) ≃ V := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective pair pair.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range pair))

private theorem vertexDecomposition_inl {V : Type uV} [Fintype V] (pair : (Fin k × Fin 2) ↪ V)
    (x : Fin k × Fin 2) : vertexDecomposition pair (Sum.inl x) = pair x := rfl

private theorem outside_card (pair : (Fin k × Fin 2) ↪ V) :
    Fintype.card (Outside pair) = Fintype.card V - 2 * k := by
  classical
  have h := Fintype.card_congr (vertexDecomposition pair)
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at h
  omega

private def edgeAssignmentEquiv : ((Fin k × Fin 2) → C) ≃ (Fin k → C × C) where
  toFun f j := (f (j, 0), f (j, 1))
  invFun f x := if x.2 = 0 then (f x.1).1 else (f x.1).2
  left_inv f := by
    funext x
    rcases x with ⟨j, b⟩
    fin_cases b <;> simp
  right_inv f := by
    funext j
    simp

private noncomputable def assignmentDecomposition (pair : (Fin k × Fin 2) ↪ V) :
    (V → C) ≃ (Fin k → C × C) × (Outside pair → C) :=
  ((Equiv.arrowCongr (vertexDecomposition pair).symm (Equiv.refl C)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)).trans
    (Equiv.prodCongr edgeAssignmentEquiv (Equiv.refl _))

private theorem assignmentDecomposition_apply
    {V : Type uV} {C : Type uC} [Fintype V] [Fintype C] (pair : (Fin k × Fin 2) ↪ V)
    (f : V → C) (j : Fin k) :
    (assignmentDecomposition pair f).1 j = (f (pair (j, 0)), f (pair (j, 1))) := rfl

private def constrainedProductEquiv {ι : Type uι} {A : Type uA} {B : Type uB} (p : ι → A → Prop) :
    {x : (ι → A) × B // ∀ i, p i (x.1 i)} ≃ (∀ i, {a : A // p i a}) × B where
  toFun x := (fun i => ⟨x.1.1 i, x.2 i⟩, x.1.2)
  invFun x := ⟨(fun i => (x.1 i).1, x.2), fun i => (x.1 i).2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

private noncomputable def badAssignmentEquiv
    (pair : (Fin k × Fin 2) ↪ V) (Good : Fin k → Finset (C × C)) :
    {f : V → C // ∀ j, (f (pair (j, 0)), f (pair (j, 1))) ∉ Good j} ≃
      (∀ j : Fin k, {c : C × C // c ∉ Good j}) × (Outside pair → C) :=
  ((assignmentDecomposition pair).subtypeEquiv (fun _ => Iff.rfl)).trans
    (constrainedProductEquiv fun j c => c ∉ Good j)

theorem allBadAssignments_card
    (pair : (Fin k × Fin 2) ↪ V) (Good : Fin k → Finset (C × C)) :
    (allBadAssignments pair Good).card =
      (∏ j : Fin k, (Fintype.card C ^ 2 - (Good j).card)) *
        Fintype.card C ^ (Fintype.card V - 2 * k) := by
  classical
  have hbad : (allBadAssignments pair Good).card =
      Fintype.card {f : V → C // ∀ j, (f (pair (j, 0)), f (pair (j, 1))) ∉ Good j} := by
    rw [Fintype.card_subtype]
    rfl
  have hcolor (j : Fin k) : Fintype.card {c : C × C // c ∉ Good j} =
      Fintype.card C ^ 2 - (Good j).card := by
    rw [Fintype.card_subtype_compl]
    simp [Fintype.card_prod, pow_two]
  rw [hbad, Fintype.card_congr (badAssignmentEquiv pair Good), Fintype.card_prod,
    Fintype.card_pi, Fintype.card_fun, outside_card]
  simp_rw [hcolor]

theorem allBadAssignments_card_le
    (pair : (Fin k × Fin 2) ↪ V) (Good : Fin k → Finset (C × C)) (g : ℕ)
    (hgood : ∀ j, g ≤ (Good j).card) :
    (allBadAssignments pair Good).card ≤
      (Fintype.card C ^ 2 - g) ^ k * Fintype.card C ^ (Fintype.card V - 2 * k) := by
  classical
  rw [allBadAssignments_card]
  apply Nat.mul_le_mul_right
  calc
    (∏ j : Fin k, (Fintype.card C ^ 2 - (Good j).card)) ≤
        ∏ _j : Fin k, (Fintype.card C ^ 2 - g) :=
      Finset.prod_le_prod (fun j _ => Nat.sub_le_sub_left (hgood j) _)
    _ = (Fintype.card C ^ 2 - g) ^ k := by simp

end

end PeriodicTilingThree

end OAI
