import OAI.CategoryTheory.Globular.WhiskerUniverse

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace CylinderNode
variable {K : Type u} [Category.{v} K] [HasPushouts K]
variable {D : GlobularFrame K} {j : ℕ}
noncomputable def oneSideMap (Z : CylinderNode D j) (ε : Bool) :
    pushout (Z.bdEnd ε) (D.inc j) ⟶ Z.obj := pushout.desc Z.inc (Z.endpoint ε) (Z.comm ε)
end CylinderNode
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)
variable [HasColimitsOfSize.{v,v} (CutoffModels C q)] [HasLimitsOfSize.{v,v} (CutoffModels C q)]

omit [HasLimitsOfSize.{v,v} (CutoffModels C q)] in
theorem completedCylinder_upper (j : ℕ) (hj : n < j)
    (B : CutoffModels C q) (e : Bool → (cutoffBoundary hC q j ⟶ B)) (ε : Bool) :
    (boundaryClass hC q (n+1)).rlp.llp
      ((completedCylinder hC q n j B e).oneSideMap ε) := by
  let := cutoff_hasColimits hC q
  intro X Y p hp
  exact TwoEndpoints.oneSide_lifting (cutoffI hC q j) e
    (cylinderFactor hC q n j B e).i p
    (hp _ (MorphismProperty.ofHoms.mk (⟨j,by omega⟩ : {j : ℕ // n+1 ≤ j})))
    ((cylinderFactor hC q n j B e).hi p hp) ε

omit [HasLimitsOfSize.{v,v} (CutoffModels C q)] in
theorem cylinderNode_upper {j : ℕ} (hj : n < j) (ε : Bool) :
    (boundaryClass hC q (n+1)).rlp.llp ((cylinderNode hC q n j).oneSideMap ε) := by
  cases j with
  | zero => omega
  | succ j =>
    rw [cylinderNode_high hC q n (by omega)]
    exact completedCylinder_upper hC q n (j+1) hj _ _ ε

omit [HasLimitsOfSize.{v,v} (CutoffModels C q)] in
theorem cylinderFrame_upper {j : ℕ} (hj : n < j) (ε : Bool) :
    (boundaryClass hC q (n+1)).rlp.llp
      (GlobularFrame.oneSidedMap (cylinderEndpoint hC q n ε) j) :=
  cylinderNode_upper hC q n hj ε

theorem cylinderNode_upper_fillers {j : ℕ} (hj : n < j) :
    (boundaryClass hC q (n+1)).rlp (terminal.from (cylinderNode hC q n j).obj) := by
  let := cutoff_hasLimits hC q
  cases j with
  | zero => omega
  | succ j =>
    rw [cylinderNode_high hC q n (by omega)]
    let F := cylinderFactor hC q n (j+1)
      (cylinderNode hC q n j).nextBoundary (cylinderNode hC q n j).nextBdEnd
    have e : terminal.from F.Z = F.p := terminal.hom_ext _ _
    exact e ▸ F.hp

end GlobularTheory.Model
namespace GlobularSet.LiftStage
variable {A : GlobularSet.{u}} {X Y : GlobularSet.{u}} {p : Hom X Y} {f : Hom A Y}

noncomputable def extendOne {n : ℕ} (a : LiftStage p f n) (hp : LiftsBoundary p (n+1)) :
    LiftStage p f (n+1) := by
  have h x : ∃ z, X.boundary (n+1) z = a.nextBoundary x ∧
      p.app (n+1) z = f.app (n+1) x := by
    apply hp
    apply Subtype.ext
    exact Prod.ext ((f.source_app n x).symm.trans (a.fac n le_rfl _).symm)
      ((f.target_app n x).symm.trans (a.fac n le_rfl _).symm)
  choose z hz hf using h
  exact a.extendTop z (fun x => congrArg (fun b => b.1.1) (hz x))
    (fun x => congrArg (fun b => b.1.2) (hz x)) hf

@[simp] theorem extendOne_old {n : ℕ} (a : LiftStage p f n) (hp : LiftsBoundary p (n+1))
    (k : ℕ) (hk : k ≤ n) (x : A.Cell k) :
    (a.extendOne hp).app k (by omega) x = a.app k hk x := by
  simp only [extendOne, extendTop, dite_eq_left hk]

noncomputable def extendBy {n : ℕ} (a : LiftStage p f n) :
    (d : ℕ) → (∀ j, n < j → j ≤ n+d → LiftsBoundary p j) → LiftStage p f (n+d)
  | 0, _ => a
  | d+1, h => (extendBy a d (fun j hj hj' => h j hj (by omega))).extendOne
      (h (n+d+1) (by omega) le_rfl)

theorem extendBy_old {n : ℕ} (a : LiftStage p f n) (d : ℕ)
    (h : ∀ j, n < j → j ≤ n+d → LiftsBoundary p j)
    (k : ℕ) (hk : k ≤ n) (x : A.Cell k) :
    (a.extendBy d h).app k (by omega) x = a.app k hk x := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [extendBy, extendOne_old _ _ k (by omega)]
    exact ih _

end GlobularSet.LiftStage
end Grothendieck

end OAI
