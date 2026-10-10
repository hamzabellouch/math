import Mathlib
import OAI.Geometry.HyperbolicGroups.WalkCell
import OAI.Geometry.HyperbolicGroups.WalkCancel

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

lemma simple_front (hs : P.Simple) {a b : P.Dart}
    (ha : T.free (T.kind (P.index a)) = true)
    (hab : P.pairing.face.SameCycle a b)
    (he : T.front (P.index a) = T.front (P.index b)) : a = b := by
  apply P.pairing.face.symm.injective
  apply hs
  · have hk := P.kind (P.pairing.face.symm a)
    dsimp only [Function.comp_apply] at hk
    rw [Equiv.apply_symm_apply] at hk
    rw [← hk]; exact ha
  · exact hab.symm_apply_left.symm_apply_right
  · have hca := P.closed (P.pairing.face.symm a)
    have hcb := P.closed (P.pairing.face.symm b)
    dsimp only [Function.comp_apply] at hca hcb
    rw [Equiv.apply_symm_apply] at hca hcb
    exact hca.symm.trans (he.trans hcb)

lemma opposite_distinct_faces (hs : P.Simple) (hn : P.NoBigon) {a : P.Dart}
    (ha : T.free (T.kind (P.index a)) = true)
    (hop : P.index (P.pairing.edge a) = T.opposite (P.index a)) :
    ¬ P.pairing.face.SameCycle a (P.pairing.edge a) := by
  intro hf
  have h₁ : P.pairing.face a = P.pairing.edge a := by
    apply P.simple_front hs (P.free_face ha) hf.apply_left
    exact (P.closed a).trans (by change T.back (P.index a) = _; rw [hop,T.opposite_front])
  have h₂ : P.pairing.face (P.pairing.edge a) = a := by
    apply P.simple_front hs (P.free_face (P.free_of_opposite ha hop)) hf.symm.apply_left
    exact (P.closed (P.pairing.edge a)).trans (by change T.back (P.index (P.pairing.edge a)) = _; rw [hop,T.opposite_back])
  exact hn a ha (by rw [h₁,h₂])

/-- Top-walk surgery terminates on actual corner cardinality. It splits
repeated template vertices, removes free backtracks and cancels a shared
macro side of one occurrence even when the surrounding simple polygons
are different. There is no assumed minimality or desired normal form here.
All frozen faces and their individual side indices survive the surgery,
and the exact signed elementary cone chain is unchanged. -/
theorem normalize : ∃ Q : WalkPicture.{u} T,
    Nonempty (P.Retains Q) ∧ Q.Simple ∧ Q.NoBigon ∧ Q.Reduced ∧ Q.chain = P.chain := by
  classical
  have produce : ∀ n, ∀ P : WalkPicture.{u} T, Fintype.card P.Dart = n →
      ∃ Q : WalkPicture.{u} T,
        Nonempty (P.Retains Q) ∧ Q.Simple ∧ Q.NoBigon ∧ Q.Reduced ∧ Q.chain = P.chain := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro P hn
      obtain ⟨P',⟨hret⟩,hs,hc⟩ := P.makeSimple
      have hle : Fintype.card P'.Dart ≤ n := by
        rw [← hn]
        exact Fintype.card_le_of_injective _ hret.injective
      by_cases hnb : P'.NoBigon
      · by_cases hred : P'.Reduced
        · exact ⟨P',⟨hret⟩,hs,hnb,hred,hc⟩
        · obtain ⟨a,ha⟩ := not_forall.mp hred
          have ha : T.free (T.kind (P'.index a)) = true ∧
              P'.index (P'.pairing.edge a) = T.opposite (P'.index a) := by
            simpa only [Classical.not_imp,not_not] using ha
          have hf := P'.opposite_distinct_faces hs hnb ha.1 ha.2
          let P₀ := P'.cancelledSide ha.1 ha.2 hf
          have hsmall : Fintype.card P₀.Dart < n := by
            apply lt_of_lt_of_le _ hle
            exact Fintype.card_subtype_lt (x := a) (by intro h; exact h.1 rfl)
          obtain ⟨Q,⟨hq⟩,hqs,hqn,hqr,hqc⟩ := ih _ hsmall P₀ rfl
          obtain ⟨hcancel⟩ := P'.cancelledSide_retains ha.1 ha.2 hf
          exact ⟨Q,⟨Retains.trans P hret (Retains.trans P' hcancel hq)⟩,hqs,hqn,hqr,
            hqc.trans ((P'.cancelledSide_chain ha.1 ha.2 hf).trans hc)⟩
      · obtain ⟨a,ha⟩ := not_forall.mp hnb
        have ha : T.free (T.kind (P'.index a)) = true ∧
            P'.pairing.face (P'.pairing.face a) = a := by
          simpa only [Classical.not_imp,not_not] using ha
        let P₀ := P'.deletedBigon ha.1 ha.2
        have hsmall : Fintype.card P₀.Dart < n := by
          apply lt_of_lt_of_le _ hle
          exact Fintype.card_subtype_lt (x := a) (by intro h; exact h.1 rfl)
        obtain ⟨Q,⟨hq⟩,hqs,hqn,hqr,hqc⟩ := ih _ hsmall P₀ rfl
        obtain ⟨hdel⟩ := P'.deletedBigon_retains ha.1 ha.2
        exact ⟨Q,⟨Retains.trans P hret (Retains.trans P' hdel hq)⟩,hqs,hqn,hqr,
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
