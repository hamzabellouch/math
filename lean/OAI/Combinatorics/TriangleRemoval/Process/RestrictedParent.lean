import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.PathForest

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.PathForest
variable {s : ℕ}

noncomputable def restrictedParent (F : PathForest s) (S : Finset (Fin s))
    (hS : ∀ v ∈ S, ∀ p, F.parent v = some p → p ∈ S)
    (i : Fin S.card) : Option (Fin S.card) :=
  match hp : F.parent (S.orderEmbOfFin rfl i) with
  | none => none
  | some p => some ((S.orderIsoOfFin rfl).symm
      ⟨p,hS _ (S.orderEmbOfFin_mem rfl i) p hp⟩)

noncomputable def restrict (F : PathForest s) (S : Finset (Fin s))
    (hS : ∀ v ∈ S, ∀ p, F.parent v = some p → p ∈ S) : PathForest S.card := by
  refine ⟨F.restrictedParent S hS,?_⟩
  intro i j hij
  unfold restrictedParent at hij
  split at hij
  · contradiction
  · rename_i p hp
    have hj := Option.some.inj hij
    subst j
    apply (S.orderEmbOfFin rfl).lt_iff_lt.mp
    have he : S.orderEmbOfFin rfl ((S.orderIsoOfFin rfl).symm
        ⟨p,hS _ (S.orderEmbOfFin_mem rfl i) p hp⟩) = p :=
      congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply _)
    rw [he]
    exact F.property _ _ hp

noncomputable def index (S : Finset (Fin s)) (v : Fin s) (hv : v ∈ S) : Fin S.card :=
  (S.orderIsoOfFin rfl).symm ⟨v,hv⟩

@[simp] lemma embed_index (S : Finset (Fin s)) (v : Fin s) (hv : v ∈ S) :
    S.orderEmbOfFin rfl (index S v hv) = v :=
  congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply _)

@[simp] lemma index_embed (S : Finset (Fin s)) (i : Fin S.card) :
    index S (S.orderEmbOfFin rfl i) (S.orderEmbOfFin_mem rfl i) = i :=
  (S.orderIsoOfFin rfl).symm_apply_apply i

lemma restrict_parent_some (F : PathForest s) (S : Finset (Fin s))
    (hS : ∀ v ∈ S, ∀ p, F.parent v = some p → p ∈ S) (i j : Fin S.card) :
    (F.restrict S hS).parent i = some j ↔
      F.parent (S.orderEmbOfFin rfl i) = some (S.orderEmbOfFin rfl j) := by
  change F.restrictedParent S hS i = some j ↔ _
  unfold restrictedParent
  split
  · rename_i he
    rw [he]
    simp
  · rename_i p hp
    simp only [hp,Option.some.injEq]
    change index S p (hS _ (S.orderEmbOfFin_mem rfl i) p hp) = j ↔ _
    constructor
    · intro he
      rw [← he,embed_index]
    · intro he
      subst p
      exact index_embed S j

lemma restrict_step_iff (F : PathForest s) (S : Finset (Fin s))
    (hS : ∀ v ∈ S, ∀ p, F.parent v = some p → p ∈ S) (i j : Fin S.card) :
    (F.restrict S hS).Step i j ↔
      F.Step (S.orderEmbOfFin rfl i) (S.orderEmbOfFin rfl j) :=
  restrict_parent_some F S hS j i

lemma restrict_ancestor (F : PathForest s) (S : Finset (Fin s))
    (hS : ∀ v ∈ S, ∀ p, F.parent v = some p → p ∈ S)
    {x y : Fin s} (hx : x ∈ S) (hy : y ∈ S) (h : F.Ancestor x y) :
    (F.restrict S hS).Ancestor (index S x hx) (index S y hy) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail y z hxy hyz ih =>
    have hym : y ∈ S := hS z hy y hyz
    apply Relation.ReflTransGen.tail (ih hym)
    apply (F.restrict_step_iff S hS _ _).mpr
    simpa only [embed_index] using hyz

lemma original_ancestor (F : PathForest s) (S : Finset (Fin s))
    (hS : ∀ v ∈ S, ∀ p, F.parent v = some p → p ∈ S)
    {i j : Fin S.card} (h : (F.restrict S hS).Ancestor i j) :
    F.Ancestor (S.orderEmbOfFin rfl i) (S.orderEmbOfFin rfl j) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail i j hij hjk ih =>
    exact Relation.ReflTransGen.tail ih ((F.restrict_step_iff S hS _ _).mp hjk)

noncomputable def restrictMark (S : Finset (Fin s)) (a : Fin s) : Option (Fin S.card) := by
  classical
  exact if ha : a ∈ S then some (index S a ha) else none

lemma restrict_onPath (F : PathForest s) (S : Finset (Fin s))
    (hS : ∀ v ∈ S, ∀ p, F.parent v = some p → p ∈ S)
    {x a : Fin s} (hx : x ∈ S) (ha : a ∈ S) (h : F.Ancestor x a) :
    (F.restrict S hS).OnPath (restrictMark S a) (index S x hx) := by
  classical
  refine ⟨index S a ha,?_,F.restrict_ancestor S hS hx ha h⟩
  simp only [restrictMark,dite_eq_left ha]

theorem restrict_two_path_cover (F : PathForest s) (S : Finset (Fin s))
    (hS : ∀ v ∈ S, ∀ p, F.parent v = some p → p ∈ S) (a b : Fin s)
    (hc : ∀ v ∈ S, (a ∈ S ∧ F.Ancestor v a) ∨ (b ∈ S ∧ F.Ancestor v b)) :
    ∀ i, (F.restrict S hS).OnPath (restrictMark S a) i ∨
      (F.restrict S hS).OnPath (restrictMark S b) i := by
  intro i
  have hi := S.orderEmbOfFin_mem rfl i
  rcases hc _ hi with ⟨ha,hva⟩ | ⟨hb,hvb⟩
  · exact Or.inl (by simpa only [index_embed] using F.restrict_onPath S hS hi ha hva)
  · exact Or.inr (by simpa only [index_embed] using F.restrict_onPath S hS hi hb hvb)

end SharpTerminalLeave.PathForest

end

end OAI
