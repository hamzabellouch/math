import Mathlib
import OAI.Probability.SKRatio.Matrices.NormalizedIncrement
import OAI.Probability.SKRatio.Matrices.FiniteTimeMesh
import OAI.Probability.SKRatio.Matrices.DetMultilinear
import OAI.Probability.SKRatio.Matrices.RealSymmetricResolventUnit
import OAI.Probability.SKRatio.Matrices.ScaledDiagonalExpectedMargin
import OAI.Probability.SKRatio.Gaussian.EmpiricalIntervals
import OAI.Probability.SKRatio.Variational.ScalarTransfer
import OAI.Probability.SKRatio.Certificates.FinalScalar

namespace OAI

section
noncomputable section
open scoped Topology
open MeasureTheory Filter
namespace SKRatio

theorem ratio_cutoff (β ε η : ℝ)
    (hβ0 : 0 ≤ β) (hβhalf : β < 1 / 2)
    (hε0 : 0 < ε) (hεhalf : ε < 1 / 2) (hη : 0 < η) :
    Tendsto
      (fun n : ℕ => disorderLaw β n
        {g : Disorder n | 1 + η <
          (mixingTime g ε : ℝ) / (mixingTime g (1 - ε) : ℝ)})
      atTop (𝓝 0) ∧
    (∀ᶠ n : ℕ in atTop, ∀ g : Disorder n, 0 < mixingTime g (1 - ε)) := by
  by_cases hsmall : β ≤ 7/20
  · exact ratio_cutoff_small_temperature β ε η hβ0 hsmall hε0 hεhalf hη
  · exact Planted.ratio_cutoff_of_scalar β ε η (9969/10000)
      (by linarith) hβhalf hε0 hεhalf hη (by norm_num)
      (fun _ _ hb hr hn => Certificate.variational_bound
        (by linarith) hβhalf.le hb hr hn)

end SKRatio

end
end

end OAI
