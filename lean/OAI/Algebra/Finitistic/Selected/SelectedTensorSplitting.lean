import OAI.Algebra.Finitistic.Selected.SelectedCohomologyVanishing
import OAI.Algebra.Finitistic.Localization.TwoDegreeFormalityNaturality

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard HasExt.standard
namespace LittleFinitistic.SelectedTensorSplitting
open SelectedFixedDiagram QuadraticEncoding
variable (N : Type) [AddCommGroup N] [Module ℂ N] [Module (B P) N]

/-- The actual derived object represented by the full B-valued fixed tensor complex. -/
abbrev object : DerivedCategory (ModuleCat (B P)) := DerivedCategory.Q.obj (SelectedTensor.complex N)

def homologyIso (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat (B P)) n).obj (object N) ≅
      (SelectedTensor.complex N).homology n :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat (B P)) n).app (SelectedTensor.complex N)

/-- Support of the evaluated representative diagram implies actual derived
cohomological support of the full tensor object. -/
theorem twoDegrees
    (h : ∀ n : ℤ, n ≠ 0 → n ≠ -3 → ∀ v : Fin 3,
      IsZero ((SelectedTensor.source N v).homology n)) :
    DerivedTruncation.TwoDegrees (object N) := by
  intro n hn0 hn3
  exact (homologyIso N n).isZero_iff.mpr
    (SelectedCohomologyVanishing.cohomology_isZero N n (h n hn0 hn3))

/-- Apply the proved B-linear truncation splitting to the actual fixed tensor,
using full module cohomology models and source-diagram support. -/
def split (R : ModuleCat (B P))
    (h0 : (SelectedTensor.complex N).homology 0 ≅ R)
    (h3 : (SelectedTensor.complex N).homology (-3) ≅ R)
    (hz : ∀ n : ℤ, n ≠ 0 → n ≠ -3 → ∀ v : Fin 3,
      IsZero ((SelectedTensor.source N v).homology n)) :
    object N ≅ (DerivedCategory.singleFunctor (ModuleCat (B P)) 0).obj R ⊞
      ((DerivedCategory.singleFunctor (ModuleCat (B P)) 0).obj R)⟦(3 : ℤ)⟧ :=
  TwoDegreeFormality.splitIsoWithModels P (object N) (twoDegrees N hz) R R
    (homologyIso N 0 ≪≫ h0) (homologyIso N (-3) ≪≫ h3)
end LittleFinitistic.SelectedTensorSplitting

end

end OAI
