import OAI.Probability.StrongRayleigh.MatrixStability
import OAI.Probability.StrongRayleigh.MixedDeterminant
import OAI.Probability.StrongRayleigh.FiniteDPPWeights

namespace OAI

universe u_1

noncomputable section
open MeasureTheory
open scoped ComplexOrder

namespace Problem336AdditiveD139

theorem PositiveContractionFinite.exists_finiteDPP {F : Type u_1} [Fintype F]
    {K : F → F → ℂ} (hK : PositiveContractionFinite K) :
    ∃ μ : ProbabilityMeasure (F → Bool), IsFiniteDeterminantalLaw μ K := by
  classical
  apply finiteDPP_exists_of_weights_nonneg K
  intro x
  exact mixedRowMatrix_det_nonneg K x hK.posSemidef hK.one_sub_posSemidef

end Problem336AdditiveD139

end

end OAI
