import Mathlib
import OAI.Geometry.HyperbolicGroups.FrozenWalk
import OAI.Geometry.HyperbolicGroups.WalkRadial
import OAI.Geometry.HyperbolicGroups.FrozenCancel

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

/-- No adjacent sides are oppositely indexed pieces of the same target cell,
including both the free top occurrences and all genuine frozen cells. -/
def FullyReduced : Prop := ∀ a, P.index (P.pairing.edge a) ≠ T.opposite (P.index a)

/-- Simultaneous normal form for mixed macro walks and literal frozen cells.
Frozen dipoles may be exposed by top surgery or radial switches. The induction
therefore retests all these conditions, and preserves the full elementary
chain, rather than separately asserting that the operations commute. -/
theorem normalize_full (B : FrozenTarget T) (hm : P.FrozenMapped B)
    (apex : V → Bool)
    (hr : ∀ s, apex (T.start (T.label s)) = true →
      apex (T.start (T.rev (T.label s))) = false) :
    ∃ Q : WalkPicture.{u} T, Nonempty (P.Survives Q) ∧ Q.FrozenMapped B ∧
      Q.Simple ∧ Q.NoBigon ∧ Q.FullyReduced ∧ Q.RadialInjective apex ∧
      Q.chain = P.chain := by
  classical
  have produce : ∀ n, ∀ P : WalkPicture.{u} T, Fintype.card P.Dart = n →
      P.FrozenMapped B →
      ∃ Q : WalkPicture.{u} T, Nonempty (P.Survives Q) ∧ Q.FrozenMapped B ∧
        Q.Simple ∧ Q.NoBigon ∧ Q.FullyReduced ∧ Q.RadialInjective apex ∧
        Q.chain = P.chain := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro P hn hm
      obtain ⟨P',⟨hret⟩,hs,hnb,hred,hrad,hc⟩ := P.normalize_radial apex hr
      let hsur := hret.survives
      have hm' := hsur.frozenMapped P B hm
      by_cases hf : P'.FullyReduced
      · exact ⟨P',⟨hsur⟩,hm',hs,hnb,hf,hrad,hc⟩
      · obtain ⟨a,ha⟩ := not_forall.mp hf
        have hop : P'.index (P'.pairing.edge a) = T.opposite (P'.index a) := not_not.mp ha
        have hfree : T.free (T.kind (P'.index a)) = false := by
          cases hb : T.free (T.kind (P'.index a)) with
          | false => rfl
          | true => exact False.elim (hred a hb hop)
        obtain ⟨P₀,⟨hcan⟩,hm₀,hsmall,hchain⟩ := P'.cancel_frozen B hm' a hfree hop
        have hsmall' : Fintype.card P₀.Dart < n := by
          apply lt_of_lt_of_le hsmall
          rw [← hn]
          exact Fintype.card_le_of_injective _ hret.injective
        obtain ⟨Q,⟨hq⟩,hqm,hqs,hqb,hqr,hqd,hqc⟩ := ih _ hsmall' P₀ rfl hm₀
        exact ⟨Q,⟨Survives.trans P hsur (Survives.trans P' hcan hq)⟩,
          hqm,hqs,hqb,hqr,hqd,hqc.trans (hchain.trans hc)⟩
  exact produce (Fintype.card P.Dart) P rfl hm
end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
