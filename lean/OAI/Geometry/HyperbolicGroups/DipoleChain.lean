import Mathlib
import OAI.Geometry.HyperbolicGroups.DipoleRemove
import OAI.Geometry.HyperbolicGroups.QuotientSum

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D A : Type*} [DecidableEq D] [Fintype D] [AddCommMonoid A]

/-- The total lifted cellular chain (or any additive face statistic). A face
is counted once, independent of its number of independently indexed sides. -/
def faceChain (f : Perm D) (w : D → A) (hw : ∀ x, w (f x) = w x) : A :=
  classSum (SameCycle.setoid f) w (sameCycle_le_of_apply (s := Setoid.ker w) (fun x => (hw x).symm))

omit [DecidableEq D] in
lemma faceChain_subtype (f : Perm D) (w : D → A) (hw : ∀ x, w (f x) = w x)
    (P : D → Prop) (hp : ∀ x, P (f x) ↔ P x) :
    faceChain (f.subtypePerm hp) (w ∘ Subtype.val) (fun x => hw x.val) =
      classSum ((SameCycle.setoid f).comap (Subtype.val : Subtype P → D)) (w ∘ Subtype.val)
        (fun _ _ h => (sameCycle_le_of_apply (s := Setoid.ker w) (fun x => (hw x).symm)) h) := by
  have hs : SameCycle.setoid (f.subtypePerm hp) =
      (SameCycle.setoid f).comap (Subtype.val : Subtype P → D) := by
    ext x y; exact sameCycle_subtypePerm_iff f hp x y
  unfold faceChain
  congr 1

omit [DecidableEq D] in
lemma faceChain_split (f : Perm D) (w : D → A) (hw : ∀ x, w (f x) = w x)
    (P : D → Prop) (hp : ∀ x, P (f x) ↔ P x) :
    faceChain f w hw =
      faceChain (f.subtypePerm hp) (w ∘ Subtype.val) (fun x => hw x.val) +
      faceChain (f.subtypePerm (p := fun x => ¬ P x) (fun x => not_congr (hp x)))
        (w ∘ Subtype.val) (fun x => hw x.val) := by
  classical
  convert classSum_split (SameCycle.setoid f) w
    (sameCycle_le_of_apply (s := Setoid.ker w) (fun x => (hw x).symm))
    P (invariant_of_sameCycle f hp) using 1
  · rfl
  · rw [faceChain_subtype]
    congr 1
    convert faceChain_subtype f w hw (fun x => ¬ P x) (fun x => not_congr (hp x)) using 1 <;> congr 1 <;> exact Subsingleton.elim _ _

namespace PictureMap
variable {I : Type*} [DecidableEq I] [Fintype I] {q : Perm I} {a b : I → D}

omit [DecidableEq D] [DecidableEq I] in
lemma OppositeFaces.faceChain_dipole {f : Perm D} (hF : OppositeFaces f q a b) (i₀ : I)
    (w : D → A) (hw : ∀ x, w (f x) = w x) :
    faceChain (f.subtypePerm hF.inDipole_face) (w ∘ Subtype.val) (fun x => hw x.val) =
      w (a i₀) + w (b i₀) := by
  classical
  rw [faceChain_subtype]
  let hs : (SameCycle.setoid f).comap (Subtype.val : {x // InDipole a b x} → D) ≤
      Setoid.ker (w ∘ Subtype.val) := fun _ _ h =>
    (sameCycle_le_of_apply (s := Setoid.ker w) (fun x => (hw x).symm)) h
  let v := Quotient.lift (w ∘ (Subtype.val : {x // InDipole a b x} → D)) (fun _ _ h => hs h)
  have hh := Fintype.sum_equiv (hF.dipoleClassesEquiv i₀)
    (fun t : Bool => if t then w (b i₀) else w (a i₀)) v (by intro t; cases t <;> rfl)
  rw [Fintype.sum_bool] at hh
  simp only [Bool.false_eq_true,ite_false,ite_true] at hh
  exact hh.symm.trans (add_comm _ _)

variable (M : PictureMap D)
omit [DecidableEq D] [DecidableEq I] in
/-- Cancellation preserves the exact signed chain in an arbitrary additive
coefficient group, not just its homology class or its unsigned face count. -/
theorem removeDipole_chain (hF : OppositeFaces M.face q a b) (hp : ∀ i, M.edge (a i) = b i)
    (i₀ : I) (w : D → A) (hw : ∀ x, w (M.face x) = w x)
    (hc : w (a i₀) + w (b i₀) = 0) :
    faceChain (M.removeDipole hF hp).face (w ∘ Subtype.val) (fun x => hw x.val) =
      faceChain M.face w hw := by
  have hh := faceChain_split M.face w hw (InDipole a b) hF.inDipole_face
  rw [hF.faceChain_dipole i₀ w hw,hc,zero_add] at hh
  exact hh.symm

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
