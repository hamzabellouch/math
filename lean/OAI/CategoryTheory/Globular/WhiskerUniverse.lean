import OAI.CategoryTheory.Globular.DiskRealization

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularSet

def ulift (X : GlobularSet.{0}) : GlobularSet.{v} where
  Cell j := ULift.{v} (X.Cell j)
  source j x := ⟨X.source j x.down⟩
  target j x := ⟨X.target j x.down⟩
  source_source j x := congrArg ULift.up (X.source_source j x.down)
  target_source j x := congrArg ULift.up (X.target_source j x.down)

theorem ulift_faceMap (X : GlobularSet.{0}) {j k : ℕ} (h : j < k) (ε : Bool)
    (x : (X.ulift.{v}).Cell k) :
    (X.ulift.{v}).faceMap h ε x = ⟨X.faceMap h ε x.down⟩ := by
  induction k, h using Nat.le_induction with
  | base => rw [faceMap_succ, faceMap_succ]; cases ε <;> rfl
  | succ k h ih =>
    rw [(X.ulift.{v}).faceMap_source h ε, X.faceMap_source h ε]
    exact ih _

theorem ulift_evalFace (X : GlobularSet.{0}) {j k : ℕ} (f : Globe.Face j k)
    (x : (X.ulift.{v}).Cell k) :
    (X.ulift.{v}).evalFace f x = ⟨X.evalFace f x.down⟩ := by
  cases f with
  | id => rfl
  | face h ε => exact X.ulift_faceMap h ε x

noncomputable def uliftPresheafIso (X : GlobularSet.{0}) :
    (X.ulift.{v}).presheaf ≅ GlobularPresheaf.liftSmall.obj X.presheaf :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro j k f
    apply ConcreteCategory.hom_ext
    intro x
    exact X.ulift_evalFace f.unop x)

def uliftWhiskerTo (X : GlobularSet.{0}) (n : ℕ) (ε : Bool) :
    Hom ((X.whisker n ε).ulift.{v}) ((X.ulift.{v}).whisker n ε) where
  app _ x := match x.down with
    | .base j x => .base j ⟨x⟩
    | .tip x => .tip ⟨x⟩
    | .edge x => .edge ⟨x⟩
  source_app j x := by
    rcases x with ⟨x⟩
    cases x with
    | base _ x => rfl
    | tip x => rfl
    | edge x => cases ε <;> rfl
  target_app j x := by
    rcases x with ⟨x⟩
    cases x with
    | base _ x => rfl
    | tip x => rfl
    | edge x => cases ε <;> rfl

def uliftWhiskerFrom (X : GlobularSet.{0}) (n : ℕ) (ε : Bool) :
    Hom ((X.ulift.{v}).whisker n ε) ((X.whisker n ε).ulift.{v}) where
  app _ x := match x with
    | .base j x => ⟨.base j x.down⟩
    | .tip x => ⟨.tip x.down⟩
    | .edge x => ⟨.edge x.down⟩
  source_app j x := by
    cases x with
    | base _ x => rfl
    | tip x => rfl
    | edge x => cases ε <;> rfl
  target_app j x := by
    cases x with
    | base _ x => rfl
    | tip x => rfl
    | edge x => cases ε <;> rfl

def uliftWhiskerIso (X : GlobularSet.{0}) (n : ℕ) (ε : Bool) :
    ((X.whisker n ε).ulift.{v}).presheaf ≅ ((X.ulift.{v}).whisker n ε).presheaf where
  hom := (X.uliftWhiskerTo n ε).presheafMap
  inv := (X.uliftWhiskerFrom n ε).presheafMap
  hom_inv_id := by
    have h : (X.uliftWhiskerTo n ε).comp (X.uliftWhiskerFrom n ε) =
        Hom.id ((X.whisker n ε).ulift.{v}) := by
      ext j x
      rcases x with ⟨x⟩
      cases x <;> rfl
    exact congrArg Hom.presheafMap h
  inv_hom_id := by
    have h : (X.uliftWhiskerFrom n ε).comp (X.uliftWhiskerTo n ε) =
        Hom.id ((X.ulift.{v}).whisker n ε) := by
      ext j x
      cases x <;> rfl
    exact congrArg Hom.presheafMap h
end GlobularSet
namespace GlobularPresheaf

noncomputable def liftSmallWhiskerIso (S : GlobularPresheaf.{0}) (n : ℕ) (ε : Bool) :
    liftSmall.{v}.obj ((whiskering n ε).obj S) ≅
      (whiskering n ε).obj (liftSmall.{v}.obj S) :=
  (S.underlying.whisker n ε).uliftPresheafIso.symm ≪≫ S.underlying.uliftWhiskerIso n ε
end GlobularPresheaf
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)
variable [HasColimitsOfSize.{0,v} (CutoffModels C q)]

theorem cutoffFrame_whisker_hasFillers (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1))
    (S : Shape) (ε : Bool) :
    ((cutoffDiskFrame hC q).realization.obj
      ((GlobularPresheaf.whiskering n ε).obj (GlobularPresheaf.liftSmall.obj S.realize))).obj.underlying.HasFillers := by
  let e := (cutoffFreeGlobular hC q).mapIso (GlobularPresheaf.liftSmallWhiskerIso S.realize n ε) ≪≫
    cutoffFrameFreeIso hC q _
  have h : ((smallFree hC q).obj ((GlobularPresheaf.whiskering n ε).obj S.realize)).obj.underlying.HasFillers := by
    cases ε
    · exact whiskerFree_hasFillers hC q n hnq H S
    · exact reverseWhiskerFree_hasFillers hC q n hnq H S
  exact h.retract (underlyingMap e.inv.hom) (underlyingMap e.hom.hom)
    (by
      have hh := congrArg (fun z : ((cutoffDiskFrame hC q).realization.obj
          ((GlobularPresheaf.whiskering n ε).obj (GlobularPresheaf.liftSmall.obj S.realize))) ⟶ _ =>
        underlyingMap z.hom) e.inv_hom_id
      exact hh)
end GlobularTheory.Model
end Grothendieck

end OAI
