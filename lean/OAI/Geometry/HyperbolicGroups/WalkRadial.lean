import Mathlib
import OAI.Geometry.HyperbolicGroups.MappedPicture
import OAI.Geometry.HyperbolicGroups.FaceWalk
import OAI.Geometry.HyperbolicGroups.WalkCell
import OAI.Geometry.HyperbolicGroups.WalkCancel
import OAI.Geometry.HyperbolicGroups.WalkNormal

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]
namespace WalkPicture
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T)

def RadialInjective (apex : V → Bool) : Prop := ∀ a b,
  apex (T.start (T.label (P.index a))) = true → P.pairing.vertex.SameCycle a b →
    T.label (P.index a) = T.label (P.index b) → a = b

lemma makeSimpleRadial (apex : V → Bool)
    (hr : ∀ s, apex (T.start (T.label s)) = true →
      apex (T.start (T.rev (T.label s))) = false) :
    ∃ Q : WalkPicture.{u} T, Nonempty (P.Retains Q) ∧
      Q.Simple ∧ Q.RadialInjective apex ∧ Q.chain = P.chain := by
  obtain ⟨P',⟨hret⟩,hs,hc⟩ := P.makeSimple
  obtain ⟨N,hf,hN,hG,hinj⟩ := PictureMap.normalize_radial apex P'.respects P'.genusZero
    (fun x => hr (P'.index x))
  let Q : WalkPicture.{u} T := {
    Dart := P'.Dart
    pairing := N
    index := P'.index
    closed := by unfold PictureMap.FaceClosed; rw [hf]; exact P'.closed
    kind := by unfold PictureMap.FaceKind; rw [hf]; exact P'.kind
    paired := hN.2
    genusZero := hG }
  have hRQ : P'.Retains Q := {
    map := id
    injective := Function.injective_id
    index := fun _ => rfl
    face := fun x _ => congrArg (fun p : Perm P'.Dart => p x) hf
    complete := fun x _ => ⟨x,rfl⟩ }
  refine ⟨Q,⟨Retains.trans P hret hRQ⟩,?_,hinj,hc⟩
  change ∀ a b, _ → N.face.SameCycle a b → _ → a = b
  rw [hf]; exact hs

/-- Simultaneous macro simplicity, top-side cancellation, and radial-label
injectivity. Cross-pairing radial sides may create new cancellable macro
adjacencies; the induction re-tests and removes them rather than silently
assuming old reducedness survives a switch. -/
theorem normalize_radial (apex : V → Bool)
    (hr : ∀ s, apex (T.start (T.label s)) = true →
      apex (T.start (T.rev (T.label s))) = false) :
    ∃ Q : WalkPicture.{u} T, Nonempty (P.Retains Q) ∧ Q.Simple ∧ Q.NoBigon ∧
      Q.Reduced ∧ Q.RadialInjective apex ∧ Q.chain = P.chain := by
  classical
  have produce : ∀ n, ∀ P : WalkPicture.{u} T, Fintype.card P.Dart = n →
      ∃ Q : WalkPicture.{u} T, Nonempty (P.Retains Q) ∧ Q.Simple ∧ Q.NoBigon ∧
        Q.Reduced ∧ Q.RadialInjective apex ∧ Q.chain = P.chain := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro P hn
      obtain ⟨P',⟨hret⟩,hs,hrad,hc⟩ := P.makeSimpleRadial apex hr
      have hle : Fintype.card P'.Dart ≤ n := by
        rw [← hn]
        exact Fintype.card_le_of_injective _ hret.injective
      by_cases hnb : P'.NoBigon
      · by_cases hred : P'.Reduced
        · exact ⟨P',⟨hret⟩,hs,hnb,hred,hrad,hc⟩
        · obtain ⟨a,ha⟩ := not_forall.mp hred
          have ha : T.free (T.kind (P'.index a)) = true ∧
              P'.index (P'.pairing.edge a) = T.opposite (P'.index a) := by
            simpa only [Classical.not_imp,not_not] using ha
          have hf := P'.opposite_distinct_faces hs hnb ha.1 ha.2
          let P₀ := P'.cancelledSide ha.1 ha.2 hf
          have hsmall : Fintype.card P₀.Dart < n := by
            apply lt_of_lt_of_le _ hle
            exact Fintype.card_subtype_lt (x := a) (by intro h; exact h.1 rfl)
          obtain ⟨Q,⟨hq⟩,hqs,hqn,hqr,hqd,hqc⟩ := ih _ hsmall P₀ rfl
          obtain ⟨hcancel⟩ := P'.cancelledSide_retains ha.1 ha.2 hf
          exact ⟨Q,⟨Retains.trans P hret (Retains.trans P' hcancel hq)⟩,hqs,hqn,hqr,hqd,
            hqc.trans ((P'.cancelledSide_chain ha.1 ha.2 hf).trans hc)⟩
      · obtain ⟨a,ha⟩ := not_forall.mp hnb
        have ha : T.free (T.kind (P'.index a)) = true ∧
            P'.pairing.face (P'.pairing.face a) = a := by
          simpa only [Classical.not_imp,not_not] using ha
        let P₀ := P'.deletedBigon ha.1 ha.2
        have hsmall : Fintype.card P₀.Dart < n := by
          apply lt_of_lt_of_le _ hle
          exact Fintype.card_subtype_lt (x := a) (by intro h; exact h.1 rfl)
        obtain ⟨Q,⟨hq⟩,hqs,hqn,hqr,hqd,hqc⟩ := ih _ hsmall P₀ rfl
        obtain ⟨hdel⟩ := P'.deletedBigon_retains ha.1 ha.2
        exact ⟨Q,⟨Retains.trans P hret (Retains.trans P' hdel hq)⟩,hqs,hqn,hqr,hqd,
          hqc.trans ((P'.deletedBigon_chain ha.1 ha.2).trans hc)⟩
  exact produce (Fintype.card P.Dart) P rfl

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
