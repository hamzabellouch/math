import OAI.Probability.FreeIsing.Estimates.FiniteIsingZeroField
import OAI.Probability.FreeIsing.Gaussian.FiniteIsingGaussianTesting
import OAI.Probability.FreeIsing.Posterior.GaussianEnergy

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Problem367

local instance finiteIsingGaussianEnergyNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

theorem HasFreeIsingLaw.hasDerivAt_finiteIsingGaussianEnergy
    {d : ℕ} {beta : ℝ} {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw (Real.tanh beta) mu)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D)
    {t : ℝ} (ht : 0 < t) :
    let spin : (D → IsingSpin) → D → ℝ := fun eta w => spinSign (eta w)
    let rho := (mu.map D.restrict).prod (Measure.pi (fun _ : D => gaussianReal 0 1))
    HasDerivAt
      (fun r => ∫ x, FinitePosterior.fieldMean (finiteIsingEnergy beta D) spin
        (fun eta => spinSign (eta v))
        (FinitePosterior.finiteStandardObservation spin r x) ^ 2 ∂rho)
      (∫ x, ∑ w, FinitePosterior.fieldCovariance (finiteIsingEnergy beta D) spin
        (fun eta => spinSign (eta v))
        (FinitePosterior.finiteStandardObservation spin t x) w ^ 2 ∂rho) t := by
  classical
  let : IsProbabilityMeasure mu := hmu.isProbabilityMeasure
  apply FinitePosterior.hasDerivAt_finiteStandardEnergy
    (mu.map D.restrict) (finiteIsingEnergy beta D)
    (hmu.restrict_real_eq_normalized_exp D hD)
    (fun eta w => spinSign (eta w)) (fun eta => spinSign (eta v)) 1
  · intro eta
    cases eta v <;> norm_num [spinSign]
  · intro eta w
    cases eta w <;> simp [spinSign]
  · exact ht

theorem finiteIsingGaussianEnergy_zero
    {d : ℕ} (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (rho : Measure ((D → IsingSpin) × (D → ℝ))) :
    (∫ x, FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) w => spinSign (eta w))
      (fun eta => spinSign (eta v))
      (FinitePosterior.finiteStandardObservation
        (fun (eta : D → IsingSpin) w => spinSign (eta w)) 0 x) ^ 2 ∂rho) = 0 := by
  have hz := finiteIsingPosterior_spin_zero beta D v
  change FinitePosterior.fieldMean (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) w => spinSign (eta w))
    (fun eta => spinSign (eta v)) 0 = 0 at hz
  simp [FinitePosterior.finiteStandardObservation, FinitePosterior.gaussianObservationCurve, hz]

end Problem367

end

end OAI
