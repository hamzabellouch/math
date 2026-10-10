import OAI.Probability.FreeIsing.Gaussian.FiniteGaussianPosterior
import OAI.Probability.FreeIsing.Gibbs.Weights
import OAI.Probability.FreeIsing.Posterior.Smooth
import OAI.Probability.FreeIsing.Spins.Moments

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace Problem367

local instance gaussianPosteriorNonemptyIsingSpin : Nonempty IsingSpin := ⟨.neg⟩

def finiteIsingEnergy {d : ℕ} (beta : ℝ) (D : Finset (TreeVertex d))
    (eta : D → IsingSpin) : ℝ :=
  beta * ∑ e ∈ inducedEdges D,
    spinSign (extendFiniteSpin D eta e.1) * spinSign (extendFiniteSpin D eta e.2)

theorem HasFreeIsingLaw.gaussian_restrict_posterior_mean
    {d : ℕ} {beta : ℝ} {mu : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure mu]
    (hmu : HasFreeIsingLaw (Real.tanh beta) mu)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (t : ℝ≥0) (observable : (D → IsingSpin) → ℝ) :
    ∀ᵐ x ∂finiteGaussianObservationKernel t (fun (eta : D → IsingSpin) (v : D) => spinSign (eta v)) ∘ₘ
        (mu.map D.restrict),
      (∫ eta, observable eta ∂(posterior
        (finiteGaussianObservationKernel t (fun (eta : D → IsingSpin) (v : D) => spinSign (eta v)))
        (mu.map D.restrict)) x) =
      FinitePosterior.fieldMean (finiteIsingEnergy beta D)
        (fun (eta : D → IsingSpin) (v : D) => spinSign (eta v)) observable x := by
  classical
  let : IsProbabilityMeasure mu := hmu.isProbabilityMeasure
  let : IsProbabilityMeasure (mu.map D.restrict) := inferInstance
  let : Nonempty (D → IsingSpin) := ⟨fun _ => .neg⟩
  let c : ℝ := (2 * (2 * Real.cosh beta) ^ (inducedEdges D).card)⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  have hprior (eta : D → IsingSpin) :
      (mu.map D.restrict).real {eta} = c * Real.exp (finiteIsingEnergy beta D eta) := by
    rw [Measure.real, hmu.restrict_atom D hD eta, freeCylinderWeight_tanh_eq_exp]
    rw [ENNReal.toReal_ofReal (by positivity)]
    dsimp [c, finiteIsingEnergy]
    ring
  have hpost := finiteGaussianObservation_posterior_mean (mu.map D.restrict) t
    (fun (eta : D → IsingSpin) (v : D) => spinSign (eta v)) (fun eta v => spinSign_sq (eta v)) observable
  filter_upwards [hpost] with x hx
  rw [hx]
  simp_rw [hprior]
  have heq (eta : D → IsingSpin) :
      c * Real.exp (finiteIsingEnergy beta D eta) *
          Real.exp (∑ v, spinSign (eta v) * x v) =
      c * Real.exp (FinitePosterior.fieldEnergy (finiteIsingEnergy beta D)
        (fun (eta : D → IsingSpin) (v : D) => spinSign (eta v)) x eta) := by
    have hd : (∑ v, spinSign (eta v) * x v) = ∑ v, x v * spinSign (eta v) := by
      apply Finset.sum_congr rfl
      intro v _
      ring
    rw [hd, FinitePosterior.fieldEnergy, Real.exp_add]
    ring
  simp_rw [heq]
  have hnum : (∑ eta, c * Real.exp (FinitePosterior.fieldEnergy
        (finiteIsingEnergy beta D) (fun (eta : D → IsingSpin) (v : D) => spinSign (eta v)) x eta) * observable eta) =
      c * ∑ eta, observable eta * Real.exp (FinitePosterior.fieldEnergy
        (finiteIsingEnergy beta D) (fun (eta : D → IsingSpin) (v : D) => spinSign (eta v)) x eta) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro eta _
    ring
  rw [hnum, ← Finset.mul_sum, mul_div_mul_left _ _ (ne_of_gt hc)]
  rfl

theorem contDiff_finiteIsingPosteriorMean {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (observable : (D → IsingSpin) → ℝ) (n : ℕ∞ω) :
    ContDiff ℝ n (FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) (v : D) => spinSign (eta v)) observable) := by
  let : Nonempty (D → IsingSpin) := ⟨fun _ => .neg⟩
  exact FinitePosterior.contDiff_fieldMean_all _ _ _ n

end Problem367

end

end OAI
