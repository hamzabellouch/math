import OAI.Probability.InvariantIsing.Fields.FieldGaussianAmplitude

namespace OAI

/-! The positive-variance Gaussian generator for the actual linearly
growing scalar field payoff. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

theorem hasDerivAt_gaussianOperator_variance (ζ z : ℝ) {v : ℝ} (hv : 0 < v)
    {F D DD : ℝ → ℝ} (hF : Measurable F) (hFg : HasLinearGrowth F)
    (hD : Measurable D) (hDD : Measurable DD) {K C : ℝ}
    (hK : 0 ≤ K) (hDb : ∀ u, |D u| ≤ K) (hDDb : ∀ u, |DD u| ≤ C)
    (hd : ∀ u, HasDerivAt F (D u) u) (hdd : ∀ u, HasDerivAt D (DD u) u) :
    HasDerivAt (fun w => gaussianOperator ζ w F z)
      (fieldSpinTransition ζ (NNReal.mk v hv.le) F
        (fun u => DD u + ζ * (D u) ^ 2) z / 2) v := by
  have ha := hasDerivAt_fieldGaussianAmplitude ζ z (Real.sqrt v) hF hFg hD hK hDb hd
  have hc := ha.comp v (Real.hasDerivAt_sqrt hv.ne')
  have hQQ : Measurable (fun u => DD u + ζ * (D u) ^ 2) :=
    hDD.add ((hD.pow_const 2).const_mul ζ)
  have ht := fieldSpinTransition_eq_standard ζ (NNReal.mk v hv.le) hF hQQ z
  change fieldSpinTransition ζ (NNReal.mk v hv.le) F
      (fun u => DD u + ζ * (D u) ^ 2) z =
    ∫ u, DD (z + Real.sqrt v * u) + ζ * (D (z + Real.sqrt v * u)) ^ 2
      ∂(gaussianReal 0 1).tilted (fun u => ζ * F (z + Real.sqrt v * u)) at ht
  have hibp := field_gaussian_tilted_ibp hF hFg hD hDD hDb hDDb hd hdd (Real.sqrt v) ζ z
  have hm : (∫ u, D (z + Real.sqrt v * u) * u
      ∂(gaussianReal 0 1).tilted (fun u => ζ * F (z + Real.sqrt v * u))) =
      Real.sqrt v * fieldSpinTransition ζ (NNReal.mk v hv.le) F
        (fun u => DD u + ζ * (D u) ^ 2) z := by
    rw [ht]
    exact (integral_congr_ae (ae_of_all _ (fun u => mul_comm _ _))).trans hibp
  have heq : (fun w => gaussianOperator ζ w F z) =ᶠ[𝓝 v]
      (fun w => fieldGaussianAmplitude ζ F z (Real.sqrt w)) := by
    filter_upwards [Ioi_mem_nhds hv] with w hw
    rw [fieldGaussianAmplitude_eq_operator ζ F z (Real.sqrt_nonneg w), Real.sq_sqrt hw.le]
  have hc' := hc.congr_of_eventuallyEq heq
  convert hc' using 1
  rw [hm]
  field_simp [(Real.sqrt_pos.mpr hv).ne']

end InvariantIsing

end

end OAI
