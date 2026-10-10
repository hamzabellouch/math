import OAI.Probability.InvariantIsing.Fields.FieldSpinSampling

namespace OAI

/-! A separable scalar cavity tilt preserves independence of the Gaussian
site coordinates. This identifies the actual vector transition law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators NNReal

namespace InvariantIsing

theorem fieldGaussian_product_tilt {N : ℕ} (ζ : ℝ) (v : ℝ≥0)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (z : Fin N → ℝ) :
    (Measure.pi (fun i => gaussianReal (z i) v)).tilted
      (fun y => ζ * ∑ i, F (y i)) =
      Measure.pi (fun i => fieldTransitionKernel ζ v F hF (z i)) := by
  let μ := fun i : Fin N => gaussianReal (z i) v
  let Z := fun i : Fin N => ∫ u, Real.exp (ζ * F u) ∂μ i
  have hZpos (i : Fin N) : 0 < Z i := integral_exp_pos
    (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments (z i) v) hF hG ζ)
  have hZ : (∫ y, Real.exp (ζ * ∑ i, F (y i)) ∂Measure.pi μ) = ∏ i, Z i := by
    simp_rw [Finset.mul_sum, Real.exp_sum]
    exact integral_fintype_prod_eq_prod (fun _ u => Real.exp (ζ * F u))
  have hS (s : Fin N → Set ℝ) :
      (∫ y in univ.pi s, Real.exp (ζ * ∑ i, F (y i)) ∂Measure.pi μ) =
        ∏ i, ∫ u in s i, Real.exp (ζ * F u) ∂μ i := by
    simp_rw [Finset.mul_sum, Real.exp_sum]
    rw [Measure.restrict_pi_pi]
    exact integral_fintype_prod_eq_prod (fun _ u => Real.exp (ζ * F u))
  apply (Measure.pi_eq (μ := fun i => fieldTransitionKernel ζ v F hF (z i)) ?_).symm
  intro s hs
  change ((Measure.pi μ).tilted (fun y => ζ * ∑ i, F (y i))) (univ.pi s) = _
  rw [tilted_apply_eq_ofReal_integral' _ (MeasurableSet.univ_pi hs), integral_div, hS, hZ]
  rw [← Finset.prod_div_distrib, ENNReal.ofReal_prod_of_nonneg
    (fun i _ => div_nonneg (integral_nonneg (fun u => (Real.exp_pos _).le)) (hZpos i).le)]
  apply Finset.prod_congr rfl
  intro i _
  rw [fieldTransitionKernel_eq_tilted ζ v F hF hG,
    tilted_apply_eq_ofReal_integral' _ (hs i), integral_div]

end InvariantIsing

end

end OAI
