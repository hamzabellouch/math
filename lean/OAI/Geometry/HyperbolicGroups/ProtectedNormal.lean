import Mathlib
import OAI.Geometry.HyperbolicGroups.FrozenWalk
import OAI.Geometry.HyperbolicGroups.DipoleStepChain
import OAI.Geometry.HyperbolicGroups.MappedCancellation
import OAI.Geometry.HyperbolicGroups.FullWalkNormal

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

/-- A protected indexed side has no oppositely indexed side anywhere in the
input. A single oriented exterior polygon satisfies this condition literally. -/
def Unopposed (keep : S → Prop) : Prop :=
  ∀ x y : P.Dart, keep (P.index x) → P.index y ≠ T.opposite (P.index x)

structure Preserves (keep : S → Prop) (Q : WalkPicture.{u} T) extends P.Survives Q where
  complete : ∀ x, keep (P.index x) → ∃ y, toSurvives.map y = x

variable {P}
def Preserves.trans {Q R : WalkPicture.{u} T} {keep : S → Prop}
    (hPQ : P.Preserves keep Q) (hQR : Q.Preserves keep R) : P.Preserves keep R := by
  refine ⟨Survives.trans P hPQ.toSurvives hQR.toSurvives,?_⟩
  intro x hx
  obtain ⟨y,hy⟩ := hPQ.complete x hx
  obtain ⟨z,hz⟩ := hQR.complete y (by rw [hPQ.index,hy]; exact hx)
  exact ⟨z,by change hPQ.map (hQR.map z) = x; rw [hz,hy]⟩

lemma Survives.unopposed {Q : WalkPicture.{u} T} {keep : S → Prop}
    (hPQ : P.Survives Q) (h : P.Unopposed keep) : Q.Unopposed keep := by
  intro x y hx hy
  apply h (hPQ.map x) (hPQ.map y)
  · rwa [← hPQ.index]
  · rw [← hPQ.index,← hPQ.index]
    exact hy

variable (P)
lemma cancel_frozen_protected (B : FrozenTarget T) (hm : P.FrozenMapped B)
    (keep : S → Prop) (hu : P.Unopposed keep)
    (a : P.Dart) (ha : T.free (T.kind (P.index a)) = false)
    (hop : P.index (P.pairing.edge a) = T.opposite (P.index a)) :
    ∃ Q : WalkPicture.{u} T, Nonempty (P.Preserves keep Q) ∧ Q.FrozenMapped B ∧
      Fintype.card Q.Dart < Fintype.card P.Dart ∧ Q.chain = P.chain := by
  let a' : P.FrozenDart := ⟨a,ha⟩
  let I := {x : P.FrozenDart // P.frozenFace.SameCycle a' x}
  obtain ⟨q,v,hF,hv,hmap⟩ := P.frozen_opposite_faces B hm a (P.pairing.edge a) ha hop
  let i₀ : I := ⟨a',SameCycle.rfl⟩
  obtain ⟨R,hRG,hRM,hRF,hRC,hRW,hRchain⟩ := P.pairing.cancel_mapped_dipole hF i₀ hv.symm
    P.respects P.genusZero T.rev_rev
    (fun i => by change T.label (P.index (v i)) = _; rw [hmap,T.opposite_label]; rfl)
    (fun _ : P.Dart => (0 : ℤ)) (fun _ => rfl) (by simp)
  let Q : WalkPicture.{u} T := {
    Dart := {x : P.Dart // ¬ PictureMap.InDipole (fun y : I => y.val.val) v x}
    pairing := R
    index := P.index ∘ Subtype.val
    closed := by
      intro x
      change T.front (P.index (R.face x).val) = T.back (P.index x.val)
      rw [hRF]
      exact P.closed x.val
    kind := by
      intro x
      change T.kind (P.index (R.face x).val) = T.kind (P.index x.val)
      rw [hRF]
      exact P.kind x.val
    paired := hRM.2
    genusZero := hRG }
  have hret : P.Preserves keep Q := {
    map := Subtype.val
    injective := Subtype.val_injective
    index := fun _ => rfl
    face := fun x _ => hRF x
    complete := by
      intro x hx
      refine ⟨⟨x,?_⟩,rfl⟩
      rintro (⟨i,hi⟩ | ⟨i,hi⟩)
      · subst x
        exact hu i.val.val (v i) hx (hmap i)
      · subst x
        apply hu (v i) i.val.val hx
        rw [hmap,← B.reverse_eq,← B.reverse_eq]
        have h := congrArg (fun p : Perm S => p (P.index i.val.val)) B.reverse_sq
        exact h.symm }
  refine ⟨Q,⟨hret⟩,hret.toSurvives.frozenMapped P B hm,?_,?_⟩
  · exact Fintype.card_subtype_lt (x := a) (by
      intro hh
      exact hh (Or.inl ⟨i₀,rfl⟩))
  · change (∑ x : {x : P.Dart // ¬ PictureMap.InDipole (fun y : I => y.val.val) v x},
        T.weight (P.index x.val)) = ∑ x : P.Dart, T.weight (P.index x)
    apply PictureMap.sum_not_inDipole hF (T.weight ∘ P.index)
    intro i
    change T.weight (P.index i.val.val) + T.weight (P.index (v i)) = 0
    rw [hmap,← B.reverse_eq]
    exact B.opposite_weight _

/-- Relative mixed normal form. Every protected frozen side, with its exact
cyclic successor and index, survives. In particular the operation does not
turn an exterior null-word into a fictitious target relator. -/
theorem normalize_protected (B : FrozenTarget T) (hm : P.FrozenMapped B)
    (keep : S → Prop) (hk : ∀ s, keep s → T.free (T.kind s) = false)
    (hu : P.Unopposed keep) (apex : V → Bool)
    (hr : ∀ s, apex (T.start (T.label s)) = true →
      apex (T.start (T.rev (T.label s))) = false) :
    ∃ Q : WalkPicture.{u} T, Nonempty (P.Preserves keep Q) ∧ Q.FrozenMapped B ∧
      Q.Simple ∧ Q.NoBigon ∧ Q.FullyReduced ∧ Q.RadialInjective apex ∧
      Q.chain = P.chain := by
  have produce : ∀ n, ∀ P : WalkPicture.{u} T, Fintype.card P.Dart = n →
      P.FrozenMapped B → P.Unopposed keep →
      ∃ Q : WalkPicture.{u} T, Nonempty (P.Preserves keep Q) ∧ Q.FrozenMapped B ∧
        Q.Simple ∧ Q.NoBigon ∧ Q.FullyReduced ∧ Q.RadialInjective apex ∧
        Q.chain = P.chain := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro P hn hm hu
      obtain ⟨P',⟨hret⟩,hs,hnb,hred,hrad,hc⟩ := P.normalize_radial apex hr
      let hsur : P.Preserves keep P' :=
        ⟨hret.survives,fun x hx => hret.complete x (hk _ hx)⟩
      have hm' := hsur.toSurvives.frozenMapped P B hm
      have hu' := hsur.toSurvives.unopposed hu
      by_cases hf : P'.FullyReduced
      · exact ⟨P',⟨hsur⟩,hm',hs,hnb,hf,hrad,hc⟩
      · obtain ⟨a,ha⟩ := not_forall.mp hf
        have hop : P'.index (P'.pairing.edge a) = T.opposite (P'.index a) := not_not.mp ha
        have hfree : T.free (T.kind (P'.index a)) = false := by
          cases hb : T.free (T.kind (P'.index a)) with
          | false => rfl
          | true => exact False.elim (hred a hb hop)
        obtain ⟨P₀,⟨hcan⟩,hm₀,hsmall,hchain⟩ := P'.cancel_frozen_protected B hm' keep hu' a hfree hop
        have hsmall' : Fintype.card P₀.Dart < n := by
          apply lt_of_lt_of_le hsmall
          rw [← hn]
          exact Fintype.card_le_of_injective _ hret.injective
        obtain ⟨Q,⟨hq⟩,hqm,hqs,hqb,hqr,hqd,hqc⟩ :=
          ih _ hsmall' P₀ rfl hm₀ (hcan.toSurvives.unopposed hu')
        exact ⟨Q,⟨hsur.trans (hcan.trans hq)⟩,hqm,hqs,hqb,hqr,hqd,hqc.trans (hchain.trans hc)⟩
  exact produce (Fintype.card P.Dart) P rfl hm hu

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
