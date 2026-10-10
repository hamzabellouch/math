import OAI.Probability.FreeIsing.Ising.GaussianPosterior
import OAI.Probability.FreeIsing.Posterior.GaussianTesting

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Problem367

local instance : Nonempty IsingSpin := ⟨.neg⟩

theorem HasFreeIsingLaw.restrict_real_eq_normalized_exp
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (eta : D → IsingSpin) :
    (μ.map D.restrict).real {eta} =
      Real.exp (finiteIsingEnergy beta D eta) /
        ∑ xi, Real.exp (finiteIsingEnergy beta D xi) := by
  rw [Measure.real, hμ.restrict_atom D hD eta, freeCylinderWeight_tanh_eq_exp]
  rw [ENNReal.toReal_ofReal (by positivity)]
  rw [show (∑ xi, Real.exp (finiteIsingEnergy beta D xi)) =
    2 * (2 * Real.cosh beta) ^ (inducedEdges D).card from
      finiteIsing_partitionFunction beta D hD]
  rfl

theorem HasFreeIsingLaw.integral_standardGaussian_test_restrict_fieldMean
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (t : ℝ) (ht : 0 ≤ t) (q : (D → IsingSpin) → ℝ)
    (h : (D → ℝ) → ℝ) (hh : Measurable h) (C : ℝ)
    (hbound : ∀ x, ‖h x‖ ≤ C) :
    let ρ := (μ.map D.restrict).prod (Measure.pi (fun _ : D => gaussianReal 0 1))
    let Y : (D → IsingSpin) × (D → ℝ) → D → ℝ :=
      fun z v => t * spinSign (z.1 v) + Real.sqrt t * z.2 v
    (∫ z, h (Y z) * q z.1 ∂ρ) =
      ∫ z, h (Y z) * FinitePosterior.fieldMean (finiteIsingEnergy beta D)
        (fun eta v => spinSign (eta v)) q (Y z) ∂ρ := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  exact finiteStandardGaussianPlanted_integral_test_fieldMean
    (μ.map D.restrict) (finiteIsingEnergy beta D)
    (hμ.restrict_real_eq_normalized_exp D hD) t ht
    (fun eta v => spinSign (eta v)) (fun eta v => spinSign_sq (eta v))
    q h hh C hbound

end Problem367

end

end OAI
