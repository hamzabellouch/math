import OAI.CategoryTheory.Globular.CylinderSplitting

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularSet

theorem liftsBoundary_of_bijective {X Y : GlobularSet.{v}} (p : Hom X Y) (k : ℕ)
    (hp : ∀ j, j ≤ k → Function.Bijective (p.app j)) : LiftsBoundary p k := by
  intro bd y hy
  obtain ⟨x,hx⟩ := (hp k le_rfl).surjective y
  refine ⟨x, ?_, hx⟩
  apply (Hom.boundaryMap_bijective_of_low p k (fun j hj => hp j (by omega))).injective
  rw [p.boundary_app, hx, hy]

theorem LiftsBoundary.comp {X Y Z : GlobularSet.{v}} {f : Hom X Y} {g : Hom Y Z}
    {k : ℕ} (hf : LiftsBoundary f k) (hg : LiftsBoundary g k) : LiftsBoundary (f.comp g) k := by
  intro bd z hz
  obtain ⟨y,hy,hgz⟩ := hg (f.boundaryMap k bd) z
    (by simpa only [Hom.boundaryMap_comp] using hz)
  obtain ⟨x,hx,hfx⟩ := hf bd y hy
  exact ⟨x,hx,(congrArg (g.app k) hfx).trans hgz⟩

end GlobularSet
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] [HasPushouts K] {B D : GlobularFrame K}

theorem Hom.pre_liftsBoundary (e : Hom D B) (Y : K) (j : ℕ)
    (s : B.obj j ⟶ oneSided e j) (hs : oneSidedMap e j ≫ s = 𝟙 _) :
    GlobularSet.LiftsBoundary (e.pre Y) j := by
  intro bd y hy
  let a := (B.boundaryEquiv j).equiv Y |>.symm bd
  have ha : (B.boundaryEquiv j).equiv Y a = bd := Equiv.apply_symm_apply _ _
  have hab : e.bd j ≫ a = D.inc j ≫ y := by
    apply ((D.boundaryEquiv j).equiv Y).injective
    erw [e.boundary_naturality, ha, (D.boundaryEquiv j).inc_boundary]
    exact hy.symm
  let top := pushout.desc a y hab
  have hh : oneSidedMap e j ≫ s ≫ top = top := by rw [← Category.assoc, hs, Category.id_comp]
  have hb : B.inc j ≫ s ≫ top = a := by
    have h := congrArg (pushout.inl (e.bd j) (D.inc j) ≫ ·) hh
    dsimp only [oneSidedMap,top] at h
    erw [pushout.inl_desc_assoc, pushout.inl_desc] at h
    exact h
  have he : e.obj j ≫ s ≫ top = y := by
    have h := congrArg (pushout.inr (e.bd j) (D.inc j) ≫ ·) hh
    dsimp only [oneSidedMap,top] at h
    erw [pushout.inr_desc_assoc, pushout.inr_desc] at h
    exact h
  exact ⟨s ≫ top, ((B.boundaryEquiv j).inc_boundary _).symm.trans
    ((congrArg ((B.boundaryEquiv j).equiv Y) hb).trans ha), he⟩

theorem jointSource_lift (e : Bool → Hom D B) (Y : K) (k : ℕ)
    (s : B.obj (k+1) ⟶ jointSource e k) (hs : jointSourceMap e k ≫ s = 𝟙 _)
    (t : B.obj k ⟶ Y) (u : Bool → (D.obj (k+1) ⟶ Y))
    (hu : ∀ ε, (e ε).obj k ≫ t = D.diagram.source k ≫ u ε) :
    ∃ l : B.obj (k+1) ⟶ Y, B.diagram.source k ≫ l = t ∧
      ∀ ε, (e ε).obj (k+1) ≫ l = u ε := by
  let top := TwoEndpoints.desc (D.diagram.source k) (fun ε => (e ε).obj k) t u hu
  have hh : jointSourceMap e k ≫ s ≫ top = top := by rw [← Category.assoc, hs, Category.id_comp]
  refine ⟨s ≫ top, ?_, ?_⟩
  · have h := congrArg (TwoEndpoints.base (D.diagram.source k) (fun ε => (e ε).obj k) ≫ ·) hh
    dsimp only [jointSourceMap,top] at h
    erw [TwoEndpoints.base_desc_assoc, TwoEndpoints.base_desc] at h
    exact h
  · intro ε
    have h := congrArg (TwoEndpoints.endpoint (D.diagram.source k) (fun ε => (e ε).obj k) ε ≫ ·) hh
    dsimp only [jointSourceMap,top] at h
    erw [TwoEndpoints.endpoint_desc_assoc, TwoEndpoints.endpoint_desc] at h
    exact h
end GlobularFrame
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)
variable [HasColimitsOfSize.{v,v} (CutoffModels C q)] [HasLimitsOfSize.{v,v} (CutoffModels C q)]
variable (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1))

theorem fullCylinderEvaluation_bijective (Y : CutoffModels C q) (j : ℕ) :
    Function.Bijective ((fullCylinderEvaluation hC q n hnq H Y).app j) := by
  have h₁ : Function.LeftInverse ((fullCylinderCoevaluation hC q n hnq H Y).app j)
      ((fullCylinderEvaluation hC q n hnq H Y).app j) := by
    intro a
    exact congrFun (congrArg (fun f => f.app j) (fullCylinderEvaluation_coevaluation hC q n hnq H Y)) a
  have h₂ : Function.RightInverse ((fullCylinderCoevaluation hC q n hnq H Y).app j)
      ((fullCylinderEvaluation hC q n hnq H Y).app j) := by
    intro a
    exact congrFun (congrArg (fun f => f.app j) (fullCylinderCoevaluation_evaluation hC q n hnq H Y)) a
  exact ⟨h₁.injective,h₂.surjective⟩

theorem fullCylinderEndpoint_liftsBoundary (Y : CutoffModels C q) (ε : Bool) (j : ℕ) :
    GlobularSet.LiftsBoundary (underlyingMap (fullCylinderEndpoint hC q n hnq H Y ε)) j := by
  rw [fullCylinderEndpoint_evaluation]
  obtain ⟨s,hs⟩ := cylinder_oneSided_split hC q n hnq H j ε
  exact ((GlobularSet.liftsBoundary_of_bijective _ j (fun k _ =>
    fullCylinderEvaluation_bijective hC q n hnq H Y k)).comp
      ((cylinderEndpoint hC q n ε).pre_liftsBoundary Y j s hs)).comp
    (GlobularSet.liftsBoundary_of_bijective _ j (fun k _ => (cutoffCellEquiv hC q Y k).bijective))

theorem fullCylinder_joint (Y : CutoffModels C q) (k : ℕ) (hk : n ≤ k)
    (t : (fullCylinder hC q n hnq H Y).underlying.Cell k)
    (u : Bool → Y.obj.underlying.Cell (k+1))
    (hu : ∀ ε, (underlyingMap (fullCylinderEndpoint hC q n hnq H Y ε)).app k t =
      Y.obj.underlying.source k (u ε)) :
    ∃ l : (fullCylinder hC q n hnq H Y).underlying.Cell (k+1),
      (fullCylinder hC q n hnq H Y).underlying.source k l = t ∧
      ∀ ε, (underlyingMap (fullCylinderEndpoint hC q n hnq H Y ε)).app (k+1) l = u ε := by
  let E := fullCylinderEvaluation hC q n hnq H Y
  let D := cutoffDiskCoevaluation hC q Y
  have hh ε : (cylinderEndpoint hC q n ε).obj k ≫ E.app k t =
      (cutoffDiskFrame hC q).diagram.source k ≫ D.app (k+1) (u ε) := by
    apply (cutoffCellEquiv hC q Y k).injective
    have he := congrFun (congrArg (fun f => f.app k)
      (fullCylinderEndpoint_evaluation hC q n hnq H Y ε)) t
    change (underlyingMap (fullCylinderEndpoint hC q n hnq H Y ε)).app k t =
      cutoffCellEquiv hC q Y k ((cylinderEndpoint hC q n ε).obj k ≫ E.app k t) at he
    exact he.symm.trans ((hu ε).trans ((cutoffCellEquiv_source hC q k _).trans
      (congrArg (Y.obj.underlying.source k) (Equiv.apply_symm_apply _ _))).symm)
  obtain ⟨s,hs⟩ := cylinder_joint_split hC q n hnq H k hk
  obtain ⟨l,hl,he⟩ := GlobularFrame.jointSource_lift (cylinderEndpoint hC q n) Y k s hs
    (E.app k t) (fun ε => D.app (k+1) (u ε)) hh
  obtain ⟨z,hz⟩ := (fullCylinderEvaluation_bijective hC q n hnq H Y (k+1)).surjective l
  refine ⟨z, ?_, ?_⟩
  · apply (fullCylinderEvaluation_bijective hC q n hnq H Y k).injective
    rw [E.source_app, hz]
    exact hl
  · intro ε
    have h := congrFun (congrArg (fun f => f.app (k+1))
      (fullCylinderEndpoint_evaluation hC q n hnq H Y ε)) z
    change (underlyingMap (fullCylinderEndpoint hC q n hnq H Y ε)).app (k+1) z =
      cutoffCellEquiv hC q Y (k+1) ((cylinderEndpoint hC q n ε).obj (k+1) ≫ E.app (k+1) z) at h
    rw [hz] at h
    exact h.trans ((congrArg (cutoffCellEquiv hC q Y (k+1)) (he ε)).trans
      (Equiv.apply_symm_apply _ _))
end GlobularTheory.Model
end Grothendieck

end OAI
