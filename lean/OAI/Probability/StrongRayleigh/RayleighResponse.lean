import OAI.Probability.StrongRayleigh.RayleighOffDiagonal
import OAI.Probability.StrongRayleigh.GeneratingSlice
import OAI.Probability.StrongRayleigh.StableWronskian
import OAI.Probability.StrongRayleigh.FiniteResponseAssembly

namespace OAI

universe u_1

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Problem336AdditiveD139

theorem StronglyRayleighFinite.tiltCovariance_row_nonneg
    {F : Type u_1} [Fintype F] {μ : ProbabilityMeasure (F → Bool)}
    (hμ : StronglyRayleighFinite μ) (h : F → ℝ) (i : F) :
    0 ≤ ∑ j : F, tiltCovariance μ h i j := by
  classical
  apply GeneratingSlice.covariance_row_nonneg_of_slice_bound μ h i
  exact stable_affine_wronskian_bound
    (GeneratingSlice.slice (GeneratingSlice.weight μ h) i false)
    (GeneratingSlice.slice (GeneratingSlice.weight μ h) i true)
    (GeneratingSlice.slice_coeff_nonneg _ (GeneratingSlice.weight_nonneg μ h) i false)
    (GeneratingSlice.slice_coeff_nonneg _ (GeneratingSlice.weight_nonneg μ h) i true)
    (GeneratingSlice.slice_stable μ hμ h i)

end Problem336AdditiveD139

end

end OAI
