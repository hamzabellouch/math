import OAI.CategoryTheory.Globular.FrameRealization

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularPresheaf

def homEquiv (S T : GlobularPresheaf.{v}) :
    (S ⟶ T) ≃ GlobularSet.Hom S.underlying T.underlying where
  toFun := underlyingMap
  invFun f := S.underlyingPresheafIso.inv ≫ f.presheafMap ≫ T.underlyingPresheafIso.hom
  left_inv f := by apply underlyingMap_injective; rfl
  right_inv f := by ext; rfl
end GlobularPresheaf
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] [HasColimitsOfSize.{0,v} K]
noncomputable def realizationHomEquiv (B : GlobularFrame K) (S : GlobularPresheaf.{v}) (Y : K) :
    (B.realization.obj S ⟶ Y) ≃ GlobularSet.Hom S.underlying (B.homGlob Y) where
  toFun := B.realizeHom
  invFun := B.desc
  left_inv := B.desc_realizeHom
  right_inv := B.realizeHom_desc
end GlobularFrame
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q : ℕ)

noncomputable def cutoffCellEquiv (Y : CutoffModels C q) (j : ℕ) :
    (cutoffDisk hC q j ⟶ Y) ≃ Y.obj.underlying.Cell j :=
  ((cutoffAdjunction hC q).homEquiv (disk C j) Y).trans (cellEquiv Y.obj j)

@[simp] theorem cutoffCellEquiv_comp {Y Z : CutoffModels C q} (j : ℕ)
    (a : cutoffDisk hC q j ⟶ Y) (f : Y ⟶ Z) :
    cutoffCellEquiv hC q Z j (a ≫ f) =
      (underlyingMap f.hom).app j (cutoffCellEquiv hC q Y j a) := by
  unfold cutoffCellEquiv
  dsimp only [Equiv.trans_apply]
  erw [Adjunction.homEquiv_naturality_right, cellEquiv_comp]
  rfl

@[simp] theorem cutoffDiskFrame_target (j : ℕ) :
    (cutoffDiskFrame hC q).diagram.target j = (cutoffFunctor hC q).map (targetDisk C j) := by
  change (cutoffFunctor hC q).map _ ≫ (cutoffFunctor hC q).map _ = _
  rw [← Functor.map_comp]
  exact congrArg (cutoffFunctor hC q).map (diskFrame_target C j)

@[simp] theorem cutoffCellEquiv_source {Y : CutoffModels C q} (j : ℕ)
    (a : cutoffDisk hC q (j+1) ⟶ Y) :
    cutoffCellEquiv hC q Y j ((cutoffDiskFrame hC q).diagram.source j ≫ a) =
      Y.obj.underlying.source j (cutoffCellEquiv hC q Y (j+1) a) := by
  rw [cutoffDiskFrame_source]
  unfold cutoffCellEquiv cutoffJ
  dsimp only [Equiv.trans_apply]
  erw [Adjunction.homEquiv_naturality_left, cellEquiv_J]

@[simp] theorem cutoffCellEquiv_target {Y : CutoffModels C q} (j : ℕ)
    (a : cutoffDisk hC q (j+1) ⟶ Y) :
    cutoffCellEquiv hC q Y j ((cutoffDiskFrame hC q).diagram.target j ≫ a) =
      Y.obj.underlying.target j (cutoffCellEquiv hC q Y (j+1) a) := by
  rw [cutoffDiskFrame_target]
  unfold cutoffCellEquiv
  dsimp only [Equiv.trans_apply]
  erw [Adjunction.homEquiv_naturality_left, cellEquiv_targetDisk]

noncomputable def cutoffDiskEvaluation (Y : CutoffModels C q) :
    GlobularSet.Hom ((cutoffDiskFrame hC q).homGlob Y) Y.obj.underlying where
  app j := cutoffCellEquiv hC q Y j
  source_app := cutoffCellEquiv_source hC q
  target_app := cutoffCellEquiv_target hC q

noncomputable def cutoffDiskCoevaluation (Y : CutoffModels C q) :
    GlobularSet.Hom Y.obj.underlying ((cutoffDiskFrame hC q).homGlob Y) where
  app j := (cutoffCellEquiv hC q Y j).symm
  source_app j x := by
    apply (cutoffCellEquiv hC q Y j).injective
    erw [Equiv.apply_symm_apply, cutoffCellEquiv_source, Equiv.apply_symm_apply]
  target_app j x := by
    apply (cutoffCellEquiv hC q Y j).injective
    erw [Equiv.apply_symm_apply, cutoffCellEquiv_target, Equiv.apply_symm_apply]

noncomputable def cutoffDiskHomEquiv (S : GlobularSet.{v}) (Y : CutoffModels C q) :
    GlobularSet.Hom S ((cutoffDiskFrame hC q).homGlob Y) ≃
      GlobularSet.Hom S Y.obj.underlying where
  toFun f := f.comp (cutoffDiskEvaluation hC q Y)
  invFun f := f.comp (cutoffDiskCoevaluation hC q Y)
  left_inv f := by ext j x; exact Equiv.symm_apply_apply _ _
  right_inv f := by ext j x; exact Equiv.apply_symm_apply _ _

variable [HasColimitsOfSize.{0,v} (CutoffModels C q)]
noncomputable def cutoffFrameHomEquiv (S : GlobularPresheaf.{v}) (Y : CutoffModels C q) :
    ((cutoffDiskFrame hC q).realization.obj S ⟶ Y) ≃
      (S ⟶ (cutoffForgetGlobular C q).obj Y) :=
  ((cutoffDiskFrame hC q).realizationHomEquiv S Y).trans
    ((cutoffDiskHomEquiv hC q S.underlying Y).trans
      (GlobularPresheaf.homEquiv S ((cutoffForgetGlobular C q).obj Y)).symm)

@[reassoc] theorem cutoffFrameHomEquiv_naturality (S : GlobularPresheaf.{v})
    {Y Z : CutoffModels C q} (a : (cutoffDiskFrame hC q).realization.obj S ⟶ Y) (b : Y ⟶ Z) :
    cutoffFrameHomEquiv hC q S Z (a ≫ b) =
      cutoffFrameHomEquiv hC q S Y a ≫ (cutoffForgetGlobular C q).map b := by
  apply GlobularPresheaf.underlyingMap_injective
  ext j x
  change cutoffCellEquiv hC q Z j ((cutoffDiskFrame hC q).cell S j x ≫ (a ≫ b)) =
    (underlyingMap b.hom).app j
      (cutoffCellEquiv hC q Y j ((cutoffDiskFrame hC q).cell S j x ≫ a))
  erw [← Category.assoc, cutoffCellEquiv_comp]

noncomputable def cutoffFrameFreeIso (S : GlobularPresheaf.{v}) :
    (cutoffFreeGlobular hC q).obj S ≅ (cutoffDiskFrame hC q).realization.obj S := by
  let U := cutoffForgetGlobular C q
  let A := cutoffGlobularAdjunction hC q
  let P := (cutoffDiskFrame hC q).realization.obj S
  let E (Y : CutoffModels C q) := cutoffFrameHomEquiv hC q S Y
  let f := (A.homEquiv S P).symm (E P (𝟙 P))
  let g := (E ((cutoffFreeGlobular hC q).obj S)).symm (A.unit.app S)
  have hf : A.homEquiv S P f = E P (𝟙 P) := (A.homEquiv S P).apply_symm_apply _
  have hg : E ((cutoffFreeGlobular hC q).obj S) g = A.unit.app S := (E _).apply_symm_apply _
  refine ⟨f, g, ?_, ?_⟩
  · apply (A.homEquiv S _).injective
    erw [Adjunction.homEquiv_naturality_right, hf, Adjunction.homEquiv_id]
    change E P (𝟙 P) ≫ U.map g = _
    erw [← cutoffFrameHomEquiv_naturality, Category.id_comp]
    exact hg
  · apply (E P).injective
    change E P (g ≫ f) = E P (𝟙 P)
    erw [cutoffFrameHomEquiv_naturality, hg]
    exact hf

theorem cutoffFrame_cofibrant (S : GlobularPresheaf.{v}) :
    Cofibrant hC q ((cutoffDiskFrame hC q).realization.obj S) := by
  let e := cutoffFrameFreeIso hC q S
  intro P Q p hp f
  exact Cofibrant.retract (cutoffFreeGlobular_cofibrant hC q S) e.inv e.hom e.inv_hom_id p hp f
end GlobularTheory.Model
end Grothendieck

end OAI
