import OAI.Analysis.IrrationalRotation.Spectral.QuasinilpotentSeries
import OAI.Analysis.IrrationalRotation.Spectral.TracialInvertibleDeterminant

namespace OAI

noncomputable section
namespace Invariant233
open scoped ENNReal

theorem NormQuasinilpotent.isUnit_one_sub_smul
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    {T : A} (hT : NormQuasinilpotent T) (z : ℂ) : IsUnit (1 - z • T) := by
  have hi := hT.geometric_inverse_identities z
  exact ⟨⟨1 - z • T, (∑' n : ℕ, z ^ n • T ^ n), hi.2, hi.1⟩, rfl⟩

theorem fugledeKadisonDeterminant_one_sub_smul_of_normQuasinilpotent
    {A : Type*} [CStarAlgebra A] (τ : TracialState A) {T : A}
    (hT : NormQuasinilpotent T) (z : ℂ) :
    fugledeKadisonDeterminant τ (1 - z • T) =
      ENNReal.ofReal (Real.exp ((τ (CFC.log
        (star (1 - z • T) * (1 - z • T)))).re / 2)) :=
  fugledeKadisonDeterminant_of_isUnit τ _ (hT.isUnit_one_sub_smul z)

theorem vectorFugledeKadisonDeterminant_one_sub_smul_of_normQuasinilpotent
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ξ : H) {T : H →L[ℂ] H} (hT : NormQuasinilpotent T) (z : ℂ) :
    vectorFugledeKadisonDeterminant ξ (1 - z • T) =
      ENNReal.ofReal (Real.exp ((vectorTrace ξ (CFC.log
        (star (1 - z • T) * (1 - z • T)))).re / 2)) :=
  vectorFugledeKadisonDeterminant_of_isUnit ξ _ (hT.isUnit_one_sub_smul z)

end Invariant233

end

end OAI
