import Mathlib
import OAI.Geometry.HyperbolicGroups.FrozenFaceSide
import OAI.Geometry.HyperbolicGroups.RelativeMultiplicity
import OAI.Geometry.HyperbolicGroups.RelativeFrozenSide

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)
variable (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))

include hm in
lemma frozenFaceSide_exists (k : FrozenCell n w d)
    (F : KindFace n w d ell hell word c hc f P select (.inr k)) (j : Fin ((frozenBoundary n w d).size k)) :
    ∃ y, P.faceClass y = F.val ∧ ∃ o, P.index y = .inl (.inr ⟨k,o,j⟩) := by
  have ho := P.faceClass_out F.val
  have hk : (target n w d ell hell word c hc f).kind (P.index F.val.out) = .inl (.inr k) := by
    change P.faceKind (P.faceClass F.val.out) = _
    rw [ho]
    exact F.property.2
  obtain ⟨o,i,hi⟩ : ∃ (o : Bool) (i : Fin ((frozenBoundary n w d).size k)),
      P.index F.val.out = .inl (.inr ⟨k,o,i⟩) := by
    cases h : P.index F.val.out with
    | inl s =>
      cases s with
      | inl a => rw [h] at hk; cases hk
      | inr s =>
        rcases s with ⟨k',o,i⟩
        rw [h] at hk
        have hh : k' = k := Sum.inr.inj (Sum.inl.inj hk)
        subst k'
        exact ⟨o,i,rfl⟩
    | inr s => rw [h] at hk; cases hk

  obtain ⟨y,hy,he⟩ := frozen_side_exists n w d ell hell word c hc f P hm hi j
  exact ⟨y,((P.faceClass_eq).mpr hy).symm.trans ho,o,he⟩

def frozenFaceDart (k : FrozenCell n w d)
    (F : KindFace n w d ell hell word c hc f P select (.inr k)) (j : Fin ((frozenBoundary n w d).size k)) : P.Dart :=
  (frozenFaceSide_exists n w d ell hell word c hc f P select hm k F j).choose
lemma frozenFaceDart_face (k : FrozenCell n w d)
    (F : KindFace n w d ell hell word c hc f P select (.inr k)) (j : Fin ((frozenBoundary n w d).size k)) :
    P.faceClass (frozenFaceDart n w d ell hell word c hc f P select hm k F j) = F.val :=
  (frozenFaceSide_exists n w d ell hell word c hc f P select hm k F j).choose_spec.1
lemma frozenFaceDart_index (k : FrozenCell n w d)
    (F : KindFace n w d ell hell word c hc f P select (.inr k)) (j : Fin ((frozenBoundary n w d).size k)) :
    ∃ o, P.index (frozenFaceDart n w d ell hell word c hc f P select hm k F j) = .inl (.inr ⟨k,o,j⟩) :=
  (frozenFaceSide_exists n w d ell hell word c hc f P select hm k F j).choose_spec.2
lemma frozenFaceDart_selected (k : FrozenCell n w d)
    (F : KindFace n w d ell hell word c hc f P select (.inr k)) (j : Fin ((frozenBoundary n w d).size k)) :
    select (P.faceClass (frozenFaceDart n w d ell hell word c hc f P select hm k F j)) = true := by
  rw [frozenFaceDart_face]
  exact F.property.1

lemma frozenFaceDart_injective (k : FrozenCell n w d) : Function.Injective
    (fun p : KindFace n w d ell hell word c hc f P select (.inr k) × Fin ((frozenBoundary n w d).size k) =>
      frozenFaceDart n w d ell hell word c hc f P select hm k p.1 p.2) := by
  intro p q h
  apply Prod.ext
  · apply Subtype.ext
    have hf := congrArg P.faceClass h
    simpa only [frozenFaceDart_face] using hf
  · obtain ⟨o,ho⟩ := frozenFaceDart_index n w d ell hell word c hc f P select hm k p.1 p.2
    obtain ⟨o',ho'⟩ := frozenFaceDart_index n w d ell hell word c hc f P select hm k q.1 q.2
    have hh := congrArg P.index h
    rw [ho,ho'] at hh
    have he : (o, p.2) = (o', q.2) := eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj (Sum.inl.inj hh))).2
    exact congrArg (fun t : Bool × Fin ((frozenBoundary n w d).size k) => t.2) he

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
