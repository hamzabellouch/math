import OAI.Algebra.Finitistic.Selected.SelectedPDDetection
import OAI.Algebra.Finitistic.Dimension.PDResidueProjection

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedPDDetection
open SelectedOrdinaryAlgebra SelectedOrdinaryModules

theorem augmentation_surjective : Function.Surjective augmentation :=
  fun d => ⟨TrivSqZeroExt.inl d, rfl⟩

theorem augmentation_kernel_square_zero :
    ∀ a ∈ RingHom.ker augmentation.toRingHom, ∀ b ∈ RingHom.ker augmentation.toRingHom, a*b=0 :=
  fun a ha b hb => PDSquareZero.kernel_square_zero X a b ha hb

/-- The detector's canonical residue is the right D-residue inflated along A → D. -/
def rightResidueEquiv : PDTensor.Residue (A := A) ≃ₗ[Aᵐᵒᵖ]
    PDResidueProjection.InflatedResidue augmentation :=
  PDResidueProjection.rightEquiv augmentation augmentation_surjective augmentation_kernel_square_zero

def residueTorIso (Y : FiniteSelectionFamily.S.{0}) (n : ℕ) :
    PDTensor.Tor (k := ℂ) (PDTensor.Residue (A := A)) (module Y) n ≅
      PDTensor.Tor (k := ℂ) (PDResidueProjection.InflatedResidue augmentation) (module Y) n :=
  PDResidueProjection.torIso augmentation augmentation_surjective augmentation_kernel_square_zero
    (module Y) (SelectedBarResolution.resolution Y) n

theorem pdLE_iff_inflated_D_residueTor (Y : FiniteSelectionFamily.S.{0}) (n : ℕ) :
    HasProjectiveDimensionLE (module Y) n ↔ IsZero
      (PDTensor.Tor (k := ℂ) (PDResidueProjection.InflatedResidue augmentation) (module Y) (n+1)) :=
  (PDTensor.pdLE_iff_residueTor_zero (SelectedMinimalResolution.finiteModule Y) n).trans
    (residueTorIso Y (n+1)).isZero_iff
end LittleFinitistic.SelectedPDDetection

end

end OAI
