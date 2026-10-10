import OAI.Analysis.IrrationalRotation.Spectral.VectorSpectral
import OAI.Analysis.IrrationalRotation.Spectral.DeterminantWeightBridge
import OAI.Analysis.IrrationalRotation.Rotation.Rotation
import OAI.Analysis.IrrationalRotation.Rotation.RotationDiagonalState

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Invariant233.Rotation.SpectralCompatibility

theorem vectorDeterminant_representation (θ : ℝ) (a : C(Circle, ℂ)) :
    vectorFugledeKadisonDeterminant vacuum (representation θ a) =
      ⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal
        (Real.exp ((∫ x, Real.log (‖a x‖ ^ 2 + ε.val) ∂circleMeasure) / 2)) := by
  exact vectorFugledeKadisonDeterminant_of_continuous_integration circleMeasure
    (representationStarAlgHom θ) vacuum (vacuumFunctional_representation θ) a

theorem vectorDeterminant_weightedReal_eq_zero (θ : ℝ) (f : C(Circle, ℝ))
    (hf : IsContinuousCircleWeight f) :
    vectorFugledeKadisonDeterminant vacuum (weightedReal θ f) = 0 := by
  unfold weightedReal weighted
  rw [vectorFugledeKadisonDeterminant_isometry_mul vacuum U
    (representation θ (complexWeight f)) (Unitary.star_mul_self_of_mem U_mem_unitary)]
  rw [vectorDeterminant_representation]
  have hn : ∀ x, ‖complexWeight f x‖ = f x := by
    intro x
    simp only [complexWeight, ContinuousMap.coe_mk, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (hf.2.1 x).1]
  simp_rw [hn]
  exact hf.regularized_determinant_eq_zero

end Invariant233.Rotation.SpectralCompatibility

end

end OAI
