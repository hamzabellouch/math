import OAI.CategoryTheory.Globular.CylinderTheory

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)
variable [HasColimitsOfSize.{v,v} (CutoffModels C q)] [HasLimitsOfSize.{v,v} (CutoffModels C q)]
local instance smallColimitsExtension : HasColimitsOfSize.{0,v} (CutoffModels C q) :=
  hasColimitsOfSizeShrink.{0,v} (CutoffModels C q)

omit [HasLimitsOfSize.{v,v} (CutoffModels C q)] in
theorem cylinderShapeEndpoint_low (S : Shape) (hS : S.height < n) :
    (cylinderShapeEndpoint hC q n false).app S = (cylinderShapeEndpoint hC q n true).app S := by
  change (shapeFrameIso hC q S).hom ≫ (cylinderEndpoint hC q n false).shapeEndpoint.app S =
    (shapeFrameIso hC q S).hom ≫ (cylinderEndpoint hC q n true).shapeEndpoint.app S
  apply congrArg ((shapeFrameIso hC q S).hom ≫ ·)
  apply (cutoffDiskFrame hC q).hom_ext
  intro j x
  erw [GlobularFrame.Hom.cell_realization, GlobularFrame.Hom.cell_realization]
  change S.2.height < n at hS
  have hj : j < n := by
    by_contra h
    exact (S.2.bounded j (by omega)).false x.down
  have he : (cylinderEndpoint hC q n false).obj j = (cylinderEndpoint hC q n true).obj j := by
    change (cylinderNode hC q n j).endpoint false = (cylinderNode hC q n j).endpoint true
    rw [cylinderNode_low hC q n hj]
    rfl
  exact congrArg (· ≫ _) he

theorem completedCylinder_extend (j : ℕ) (B : CutoffModels C q)
    (e : Bool → (cutoffBoundary hC q j ⟶ B)) {Y : CutoffModels C q}
    (hY : Y.obj.underlying.HasFillers) (b : B ⟶ Y)
    (d : Bool → (cutoffDisk hC q j ⟶ Y))
    (hd : ∀ ε, e ε ≫ b = cutoffI hC q j ≫ d ε) :
    ∃ l : (completedCylinder hC q n j B e).obj ⟶ Y,
      (completedCylinder hC q n j B e).inc ≫ l = b ∧
      ∀ ε, (completedCylinder hC q n j B e).endpoint ε ≫ l = d ε := by
  let F := cylinderFactor hC q n j B e
  have hp : (boundaryClass hC q (n+1)).rlp (terminal.from Y) := by
    rintro A B f ⟨⟨k,hk⟩⟩
    exact (lifting_terminal_iff _ _).2 ((cutoff_hasFillers_iff hC q _).1 hY k)
  let a := TwoEndpoints.desc (cutoffI hC q j) e b d hd
  obtain ⟨l,hl⟩ := (lifting_terminal_iff F.i Y).1 (F.hi _ hp) a
  refine ⟨l, ?_, ?_⟩
  · change (TwoEndpoints.base _ _ ≫ F.i) ≫ l = b
    erw [Category.assoc, hl]
    exact TwoEndpoints.base_desc _ _ _ _ _
  · intro ε
    change (TwoEndpoints.endpoint _ _ ε ≫ F.i) ≫ l = d ε
    erw [Category.assoc, hl]
    exact TwoEndpoints.endpoint_desc _ _ _ _ _ _

omit [HasColimitsOfSize.{v,v} (CutoffModels C q)] [HasLimitsOfSize.{v,v} (CutoffModels C q)] in
theorem criticalCylinder_extend {Y : CutoffModels C q}
    (hY : Y.obj.underlying.HasFillers)
    (b : (cutoffDiskFrame hC q).bd n ⟶ Y)
    (d : Bool → ((cutoffDiskFrame hC q).obj n ⟶ Y))
    (hd : ∀ ε, b = (cutoffDiskFrame hC q).inc n ≫ d ε) :
    ∃ l : (CylinderNode.critical (cutoffDiskFrame hC q) n).obj ⟶ Y,
      (CylinderNode.critical (cutoffDiskFrame hC q) n).inc ≫ l = b ∧
      ∀ ε, (CylinderNode.critical (cutoffDiskFrame hC q) n).endpoint ε ≫ l = d ε := by
  let D := cutoffDiskFrame hC q
  let a := (D.square n).desc (d false) (d true) ((hd false).symm.trans (hd true))
  obtain ⟨l,hl⟩ := (cutoff_hasFillers_iff hC q Y).1 hY (n+1) a
  have hs : D.diagram.source n ≫ l = d false := by
    change (D.left n ≫ D.inc (n+1)) ≫ l = _
    erw [Category.assoc, hl]
    exact (D.square n).inl_desc _ _ _
  have ht : D.diagram.target n ≫ l = d true := by
    change (D.right n ≫ D.inc (n+1)) ≫ l = _
    erw [Category.assoc, hl]
    exact (D.square n).inr_desc _ _ _
  refine ⟨l, ?_, ?_⟩
  · change (D.inc n ≫ D.diagram.source n) ≫ l = b
    erw [Category.assoc, hs]
    exact (hd false).symm
  · intro ε
    cases ε
    · exact hs
    · exact ht

theorem cylinderNode_extend (j : ℕ) {Y : CutoffModels C q}
    (hY : Y.obj.underlying.HasFillers) (b : (cylinderNode hC q n j).bd ⟶ Y)
    (d : Bool → (cutoffDisk hC q j ⟶ Y))
    (hd : ∀ ε, (cylinderNode hC q n j).bdEnd ε ≫ b = cutoffI hC q j ≫ d ε)
    (hlow : j < n → d false = d true) :
    ∃ l : (cylinderNode hC q n j).obj ⟶ Y,
      (cylinderNode hC q n j).inc ≫ l = b ∧
      ∀ ε, (cylinderNode hC q n j).endpoint ε ≫ l = d ε := by
  revert b
  by_cases hj : j < n
  · erw [cylinderNode_low hC q n hj]
    intro b hd
    refine ⟨d false, ?_, ?_⟩
    · have h := hd false
      exact (Category.id_comp b).symm.trans h |>.symm
    · intro ε
      cases ε
      · exact Category.id_comp _
      · exact (Category.id_comp _).trans (hlow hj)
  · by_cases he : j = n
    · subst j
      erw [cylinderNode_critical]
      intro b hd
      exact criticalCylinder_extend hC q n hY b d (fun ε => (Category.id_comp b).symm.trans (hd ε))
    · cases j with
      | zero => omega
      | succ j =>
        erw [cylinderNode_high hC q n (by omega)]
        intro b hd
        exact completedCylinder_extend hC q n _ _ _ hY b d hd

end GlobularTheory.Model
end Grothendieck

end OAI
