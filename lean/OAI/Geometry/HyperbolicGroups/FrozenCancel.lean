import Mathlib
import OAI.Geometry.HyperbolicGroups.FrozenWalk
import OAI.Geometry.HyperbolicGroups.DipoleStepChain
import OAI.Geometry.HyperbolicGroups.MappedCancellation

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

/-- Frozen dipole cancellation in a picture which also has arbitrary free
macro faces. It removes complete opposite frozen cells, preserves every
surviving frozen face, and preserves the exact elementary signed chain. -/
theorem cancel_frozen (B : FrozenTarget T) (hm : P.FrozenMapped B)
    (a : P.Dart) (ha : T.free (T.kind (P.index a)) = false)
    (hop : P.index (P.pairing.edge a) = T.opposite (P.index a)) :
    ∃ Q : WalkPicture.{u} T, Nonempty (P.Survives Q) ∧ Q.FrozenMapped B ∧
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
  have hret : P.Survives Q :=
    ⟨Subtype.val,Subtype.val_injective,fun _ => rfl,fun x _ => hRF x⟩
  refine ⟨Q,⟨hret⟩,hret.frozenMapped P B hm,?_,?_⟩
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

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
