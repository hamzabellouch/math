import OAI.Analysis.IrrationalRotation.Sampling.CharacterSamplingTests
import OAI.Analysis.IrrationalRotation.Model.TrialSampling

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Invariant233.CharacterSampling

theorem kernel_eq_parameter_orientedKernel (endpoint : Bool) (m : ℕ) (z v : ℝ) :
    kernel endpoint m z v =
      CircleParameterData.orientedKernel endpoint m z (Int.fract v) := by
  cases endpoint <;>
    simp only [kernel, CircleParameterData.orientedKernel, Bool.false_eq_true,
      ↓reduceIte, ScalarSampling.manuscriptEndpointKernel,
      ScalarSampling.manuscriptKernel, ScalarSampling.circleKernel,
      ScalarSampling.rawKernel, ScalarSampling.delta, CircleParameterData.kernel,
      CircleParameterData.delta, CircleParameterData.kernelWidth,
      Set.indicator_apply, Set.mem_Ioo, one_div, fract_sub_fract, ite_and]

theorem average_eq_trialAverage (m : ℕ) (samples : Finset ℕ) (endpoint : Bool)
    (phase : Fin m → ℝ) (z : UnitAddTorus (Fin m)) :
    average m samples endpoint phase z = TrialSampling.average m samples endpoint phase z := by
  unfold average TrialSampling.average
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.prod_congr rfl
  intro i hi
  exact kernel_eq_parameter_orientedKernel endpoint m _ _

theorem trialSpatialLaw_eq_volume (m : ℕ) :
    TrialSampling.spatialLaw m = (volume : Measure (UnitAddTorus (Fin m))) := rfl

theorem trialSquaredError_eq_ofReal_integral {m : ℕ} (hm : 200 ≤ m)
    (samples : Finset ℕ) (endpoint : Bool) (phase : Fin m → ℝ) :
    TrialSampling.squaredError m samples endpoint phase =
      ENNReal.ofReal (∫ z : UnitAddTorus (Fin m),
        squaredError m samples endpoint (phase, z)) := by
  rw [TrialSampling.squaredError, trialSpatialLaw_eq_volume]
  simp_rw [← average_eq_trialAverage]
  exact lintegral_squaredError_eq hm samples endpoint
    (F := fun z : UnitAddTorus (Fin m) => (phase,z))
    (measurable_const.prodMk measurable_id)

theorem trialSquaredError_lt_iff {m : ℕ} (hm : 200 ≤ m)
    (samples : Finset ℕ) (endpoint : Bool) (phase : Fin m → ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    TrialSampling.squaredError m samples endpoint phase < ENNReal.ofReal δ ↔
      (∫ z : UnitAddTorus (Fin m),
        squaredError m samples endpoint (phase, z)) < δ := by
  rw [trialSquaredError_eq_ofReal_integral hm, ENNReal.ofReal_lt_ofReal_iff hδ]

end Invariant233.CharacterSampling

end

end OAI
