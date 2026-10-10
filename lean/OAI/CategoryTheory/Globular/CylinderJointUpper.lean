import OAI.CategoryTheory.Globular.FrameJoint

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace CylinderNode
variable {K : Type u} [Category.{v} K] [HasPushouts K]
variable {D : GlobularFrame K} {j : ℕ}
noncomputable def twoSideMap (Z : CylinderNode D j) :
    TwoEndpoints.obj (D.inc j) Z.bdEnd ⟶ Z.obj :=
  TwoEndpoints.desc (D.inc j) Z.bdEnd Z.inc Z.endpoint Z.comm

theorem critical_twoSide_lifting (D : GlobularFrame K) (n : ℕ)
    {X Y : K} (p : X ⟶ Y) (h : HasLiftingProperty (D.inc (n+1)) p) :
    HasLiftingProperty ((critical D n).twoSideMap) p := by
  constructor
  intro a y sq
  let e : Bool → (D.bd n ⟶ D.bd n) := fun _ => 𝟙 _
  let ds (ε) := TwoEndpoints.endpoint (D.inc n) e ε ≫ a
  have hd : D.inc n ≫ ds false = D.inc n ≫ ds true := by
    have hx (ε) : D.inc n ≫ ds ε = TwoEndpoints.base (D.inc n) e ≫ a := by
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ a) ((TwoEndpoints.condition (D.inc n) e ε).symm.trans
          (Category.id_comp _))))
    exact (hx false).trans (hx true).symm
  let b := (D.square n).desc (ds false) (ds true) hd
  have hdp (ε) : ds ε ≫ p = (if ε then D.diagram.target n else D.diagram.source n) ≫ y := by
    have hh := congrArg (TwoEndpoints.endpoint (D.inc n) e ε ≫ ·) sq.w
    erw [← Category.assoc _ ((critical D n).twoSideMap), TwoEndpoints.endpoint_desc] at hh
    exact (Category.assoc _ _ _).trans hh
  have sq' : CommSq b (D.inc (n+1)) p y := by
    constructor
    apply (D.square n).hom_ext
    · erw [← Category.assoc, IsPushout.inl_desc]
      exact (hdp false).trans (Category.assoc _ _ _)
    · erw [← Category.assoc, IsPushout.inr_desc]
      exact (hdp true).trans (Category.assoc _ _ _)
  let : sq'.HasLift := h.sq_hasLift sq'
  have hs : D.diagram.source n ≫ sq'.lift = ds false := by
    change (D.left n ≫ D.inc (n+1)) ≫ sq'.lift = _
    rw [Category.assoc, sq'.fac_left]
    exact (D.square n).inl_desc _ _ _
  have ht : D.diagram.target n ≫ sq'.lift = ds true := by
    change (D.right n ≫ D.inc (n+1)) ≫ sq'.lift = _
    rw [Category.assoc, sq'.fac_left]
    exact (D.square n).inr_desc _ _ _
  refine CommSq.HasLift.mk' ⟨sq'.lift, ?_, sq'.fac_right⟩
  apply TwoEndpoints.hom_ext
  · erw [← Category.assoc, TwoEndpoints.base_desc]
    change (D.inc n ≫ D.diagram.source n) ≫ sq'.lift = _
    erw [Category.assoc, hs]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ a) ((TwoEndpoints.condition (D.inc n) e false).symm.trans
        (Category.id_comp _))))
  · intro ε
    erw [← Category.assoc, TwoEndpoints.endpoint_desc]
    cases ε
    · exact hs
    · exact ht
end CylinderNode
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)
variable [HasColimitsOfSize.{v,v} (CutoffModels C q)]

theorem completedCylinder_twoSide_upper (j : ℕ) (B : CutoffModels C q)
    (e : Bool → (cutoffBoundary hC q j ⟶ B)) :
    (boundaryClass hC q (n+1)).rlp.llp ((completedCylinder hC q n j B e).twoSideMap) := by
  let F := cylinderFactor hC q n j B e
  have he : (completedCylinder hC q n j B e).twoSideMap = F.i := by
    apply TwoEndpoints.hom_ext
    · exact TwoEndpoints.base_desc _ _ _ _ _
    · intro ε
      exact TwoEndpoints.endpoint_desc _ _ _ _ _ ε
  rw [he]
  exact F.hi

theorem cylinderFrame_twoEnded_upper {j : ℕ} (hj : n ≤ j) :
    (boundaryClass hC q (n+1)).rlp.llp
      (GlobularFrame.twoEndedMap (cylinderEndpoint hC q n) j) := by
  change (boundaryClass hC q (n+1)).rlp.llp ((cylinderNode hC q n j).twoSideMap)
  by_cases he : j = n
  · subst j
    rw [cylinderNode_critical]
    intro X Y p hp
    exact CylinderNode.critical_twoSide_lifting (cutoffDiskFrame hC q) n p
      (hp _ (MorphismProperty.ofHoms.mk (⟨n+1,le_rfl⟩ : {j : ℕ // n+1 ≤ j})))
  · cases j with
    | zero => omega
    | succ j =>
      rw [cylinderNode_high hC q n (by omega)]
      exact completedCylinder_twoSide_upper hC q n _ _ _

theorem cylinderFrame_jointSource_upper (k : ℕ) (hk : n ≤ k) :
    (boundaryClass hC q (n+1)).rlp.llp
      (GlobularFrame.jointSourceMap (cylinderEndpoint hC q n) k) := by
  intro X Y p hp
  exact GlobularFrame.jointSource_lifting (cylinderEndpoint hC q n) p k
    (cylinderFrame_twoEnded_upper hC q n hk p hp)
    (cylinderFrame_twoEnded_upper hC q n (by omega) p hp)
end GlobularTheory.Model
end Grothendieck

end OAI
