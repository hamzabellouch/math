import OAI.Algebra.Finitistic.Selected.SelectedCohomologyAssembly
import OAI.Algebra.Finitistic.Localization.EvaluationVertexDiagram

namespace OAI
noncomputable section
open CategoryTheory HomologicalComplex
namespace LittleFinitistic.SelectedReferenceCohomology
open SelectedFixedDiagram SelectedRectification QuadraticEncoding

private lemma transfer_to_vertices {C : Type*} [Category C]
    {A₀ A₁ B₀ B₁ Y₀ Y₁ : C} (f : A₀ ⟶ A₁) (g : B₀ ⟶ B₁) (h : Y₀ ⟶ Y₁)
    (e₀ : A₀ ≅ Y₀) (e₁ : A₁ ≅ Y₁) (v₀ : B₀ ≅ Y₀) (v₁ : B₁ ≅ Y₁)
    (hf : f ≫ e₁.hom = e₀.hom ≫ h) (hg : g ≫ v₁.hom = v₀.hom ≫ h) :
    f ≫ (e₁ ≪≫ v₁.symm).hom = (e₀ ≪≫ v₀.symm).hom ≫ g := by
  apply (cancel_mono v₁.hom).1
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [hg, Iso.inv_hom_id_assoc]
  exact hf

variable (N : Type) [AddCommGroup N] [Module ℂ N] [Module (B P) N]
variable {Y : Type} [AddCommGroup Y] [Module ℂ Y] (X : Representation P Y)
variable (n : ℤ) (E : ∀ v : Fin 3,
  (SelectedTensor.source N v).homology n ≅ ModuleCat.of ℂ Y)

/-- Identify the full tensor cohomology with the actual evaluation module from
three coordinate models and their generator actions. -/
def iso
    (h01 : ∀ a,
      homologyMap (((BalancedTensor.tensorFunctor ℂ (B P) N).mapHomologicalComplex (.up ℤ)).map (f a)) n ≫
        (E 1).hom = (E 0).hom ≫ EvaluationVertexDiagram.action X a)
    (h12 : ∀ b,
      homologyMap (((BalancedTensor.tensorFunctor ℂ (B P) N).mapHomologicalComplex (.up ℤ)).map (g b)) n ≫
        (E 2).hom = (E 1).hom ≫ EvaluationVertexDiagram.action X b) :
    (SelectedTensor.complex N).homology n ≅ EvaluationVertexDiagram.module X := by
  apply SelectedCohomologyAssembly.iso N n (EvaluationVertexDiagram.module X)
    (fun v => E v ≪≫ (EvaluationVertexDiagram.vertexIso X v).symm)
  · intro a
    exact transfer_to_vertices _ _ _ (E 0) (E 1)
      (EvaluationVertexDiagram.vertexIso X 0) (EvaluationVertexDiagram.vertexIso X 1)
      (h01 a) (EvaluationVertexDiagram.arrow01_square X a (CanonicalArrowCompatibility.arrow01_target P a))
  · intro b
    exact transfer_to_vertices _ _ _ (E 1) (E 2)
      (EvaluationVertexDiagram.vertexIso X 1) (EvaluationVertexDiagram.vertexIso X 2)
      (h12 b) (EvaluationVertexDiagram.arrow12_square X b (CanonicalArrowCompatibility.arrow12_target P b))
end LittleFinitistic.SelectedReferenceCohomology

end

end OAI
