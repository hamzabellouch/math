import OAI.Algebra.Finitistic.Selected.SelectedTensor
import OAI.Algebra.Finitistic.Rectification.VertexCategoricalAssembly

namespace OAI
noncomputable section
open CategoryTheory HomologicalComplex
namespace LittleFinitistic.SelectedCohomologyAssembly
open SelectedFixedDiagram SelectedRectification QuadraticEncoding
section General
variable {C : Type*} [Category C]
variable {X0 X1 M0 M1 N0 N1 : C}
lemma transfer_square (f : X0 ⟶ X1) (m : M0 ⟶ M1) (n : N0 ⟶ N1)
    (c0 : X0 ≅ M0) (c1 : X1 ≅ M1) (e0 : X0 ≅ N0) (e1 : X1 ≅ N1)
    (hc : f ≫ c1.hom = c0.hom ≫ m) (he : f ≫ e1.hom = e0.hom ≫ n) :
    m ≫ (c1.symm ≪≫ e1).hom = (c0.symm ≪≫ e0).hom ≫ n := by
  apply (cancel_epi c0.hom).1
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  calc
    c0.hom ≫ m ≫ c1.inv ≫ e1.hom = (c0.hom ≫ m) ≫ c1.inv ≫ e1.hom := by simp only [Category.assoc]
    _ = (f ≫ c1.hom) ≫ c1.inv ≫ e1.hom := by rw [← hc]
    _ = f ≫ e1.hom := by simp
    _ = e0.hom ≫ n := he
    _ = c0.hom ≫ (c0.inv ≫ e0.hom) ≫ n := by simp
end General

variable (N : Type) [AddCommGroup N] [Module ℂ N] [Module (B P) N]
variable (n : ℤ) (R : ModuleCat (B P))
variable (E : ∀ v : Fin 3, (SelectedTensor.source N v).homology n ≅
  (LeftVertexHomology.vertex ℂ (B P) (ThreeVertexAlgebra.vertex (composition P) v)).obj R)

/-- Convert an identified evaluated-representative cohomology diagram into the
full cohomology B-module of the one fixed selecting tensor. Only the reference
diagram identification is an input; the tensor vertex comparisons are proved. -/
def iso
    (h01 : ∀ a,
      homologyMap (((BalancedTensor.tensorFunctor ℂ (B P) N).mapHomologicalComplex (.up ℤ)).map (f a)) n ≫
        (E 1).hom = (E 0).hom ≫
        (LeftVertexHomology.arrow ℂ (B P) (ThreeVertexAlgebra.vertex (composition P) 0)
          (ThreeVertexAlgebra.vertex (composition P) 1) (arrow01 P a)
          (CanonicalArrowCompatibility.arrow01_target P a)).app R)
    (h12 : ∀ b,
      homologyMap (((BalancedTensor.tensorFunctor ℂ (B P) N).mapHomologicalComplex (.up ℤ)).map (g b)) n ≫
        (E 2).hom = (E 1).hom ≫
        (LeftVertexHomology.arrow ℂ (B P) (ThreeVertexAlgebra.vertex (composition P) 1)
          (ThreeVertexAlgebra.vertex (composition P) 2) (arrow12 P b)
          (CanonicalArrowCompatibility.arrow12_target P b)).app R) :
    (SelectedTensor.complex N).homology n ≅ R :=
  VertexCategoricalAssembly.iso P _ R
    (fun v => (SelectedTensor.comparisonIso N v n).symm ≪≫ E v)
    (fun a => transfer_square _ _ _ (SelectedTensor.comparisonIso N 0 n)
      (SelectedTensor.comparisonIso N 1 n) (E 0) (E 1)
      (TensorCohomologyDiagram.arrow01_square P D0 D1 D2 f g relations N a n) (h01 a))
    (fun b => transfer_square _ _ _ (SelectedTensor.comparisonIso N 1 n)
      (SelectedTensor.comparisonIso N 2 n) (E 1) (E 2)
      (TensorCohomologyDiagram.arrow12_square P D0 D1 D2 f g relations N b n) (h12 b))
end LittleFinitistic.SelectedCohomologyAssembly

end

end OAI
