import OAI.Algebra.Finitistic.Dimension.PDAllSimples
import OAI.Algebra.Finitistic.Dimension.PDResolutionDetection
import OAI.Algebra.Finitistic.Bar.Bar

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.PDBar
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (M : PDMinimal.FiniteModule k A)
variable (U : Type u) [AddCommGroup U] [Module k U] [Module Aᵐᵒᵖ U]

abbrev tensorComplex (P : ProjectiveResolution M.cat) : ChainComplex (ModuleCat k) ℕ :=
  ((PDTensor.tensorFunctor k A U).mapHomologicalComplex _).obj P.complex

/-- Any actual projective resolution computes the same Tor, including the
constructed absolute bar resolution. -/
def torIsoResolution (P : ProjectiveResolution M.cat) (n : ℕ) :
    PDTensor.Tor (k := k) U M.cat n ≅ (tensorComplex M U P).homology n :=
  P.isoLeftDerivedObj (PDTensor.tensorFunctor k A U) n

abbrev resolution : ProjectiveResolution M.cat := DerivedBar.projectiveResolution k A M

/-- No extra identification between the bar augmentation and M is assumed. -/
def torIsoBar (n : ℕ) :
    PDTensor.Tor (k := k) U M.cat n ≅ (tensorComplex M U (resolution M)).homology n :=
  torIsoResolution M U (resolution M) n

variable {U}
theorem pdLE_iff_residue_resolution (P : ProjectiveResolution M.cat) (n : ℕ) :
    HasProjectiveDimensionLE M.cat n ↔
      IsZero ((tensorComplex M (PDTensor.Residue (A := A)) P).homology (n+1)) := by
  rw [PDTensor.pdLE_iff_residueTor_zero M n]
  exact (torIsoResolution M _ P (n+1)).isZero_iff

theorem pdLE_iff_simple_resolution (P : ProjectiveResolution M.cat) (n : ℕ) :
    HasProjectiveDimensionLE M.cat n ↔
      ∀ S : Submodule Aᵐᵒᵖ (PDTensor.Residue (A := A)), IsSimpleModule Aᵐᵒᵖ S →
        IsZero ((tensorComplex M S P).homology (n+1)) := by
  rw [PDTensor.pdLE_iff_simpleTor_zero M n]
  exact forall_congr' fun S => imp_congr_right fun _ =>
    (torIsoResolution M S P (n+1)).isZero_iff
end LittleFinitistic.PDBar

end

end OAI
