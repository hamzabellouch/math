import Mathlib
import OAI.Geometry.CAT0Fillings.Slicing.IntegralBoundary
import OAI.Geometry.CAT0Fillings.Mass.Convolution
import OAI.Geometry.CAT0Fillings.Mass.Gradient

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SmoothCutoff

lemma dprofile_nonneg (a : ℝ≥0) (t x : ℝ) : 0 ≤ dprofile a t x :=
  mul_nonneg a.coe_nonneg Real.smoothTransition.monotone.deriv_nonneg

lemma ae_density_smul_le (γ μ : Measure ℝ) [IsFiniteMeasure γ] [IsFiniteMeasure μ]
    (c : ℝ≥0) (hle : γ ≤ c • μ) :
    ∀ᵐ t : ℝ, (γ.rnDeriv volume t).toReal ≤ (c:ℝ)*(μ.rnDeriv volume t).toReal := by
  filter_upwards [ae_tendsto_dprofile_measure γ,ae_tendsto_dprofile_measure μ] with t hγ hμ
  apply le_of_tendsto_of_tendsto hγ (hμ.const_mul (c:ℝ))
  apply Eventually.of_forall
  intro n
  have h := integral_mono_measure hle
    (Eventually.of_forall fun x => dprofile_nonneg ((n:ℝ≥0)+1) t x)
    (dprofile_integrable_measure (c • μ) _ _)
  simpa only [integral_smul_nnreal_measure,NNReal.smul_def,smul_eq_mul] using h

lemma quadratic_implies_cauchy {g a e : ℝ} (hg : 0 ≤ g) (ha : 0 ≤ a) (he : 0 ≤ e)
    (h : ∀ c : ℝ≥0, 2*(c:ℝ)*g ≤ (c:ℝ)^2*a+e) : g^2 ≤ a*e := by
  by_cases hz : a = 0
  · simp only [hz,mul_zero,zero_mul,zero_add] at h ⊢
    by_contra hpos
    have hgp : 0 < g := lt_of_le_of_ne hg (by intro hh; simp [←hh] at hpos)
    have hh := h ⟨(e+1)/(2*g),by positivity⟩
    change 2*((e+1)/(2*g))*g ≤ e at hh
    have heq : 2*((e+1)/(2*g))*g = e+1 := by field_simp
    linarith
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
    have hh := h ⟨g/a,div_nonneg hg ha⟩
    change 2*(g/a)*g ≤ (g/a)^2*a+e at hh
    have hi := mul_le_mul_of_nonneg_right hh hap.le
    field_simp [hz] at hi
    nlinarith

lemma ae_density_cauchy (γ μ ζ : Measure ℝ) [IsFiniteMeasure γ]
    [IsFiniteMeasure μ] [IsFiniteMeasure ζ]
    (hle : ∀ c : ℝ≥0, (2*c) • γ ≤ c^2 • μ + ζ) :
    ∀ᵐ t : ℝ, (γ.rnDeriv volume t).toReal^2 ≤
      (μ.rnDeriv volume t).toReal*(ζ.rnDeriv volume t).toReal := by
  filter_upwards [ae_tendsto_dprofile_measure γ,ae_tendsto_dprofile_measure μ,
    ae_tendsto_dprofile_measure ζ] with t hγ hμ hζ
  apply quadratic_implies_cauchy ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  intro c
  apply le_of_tendsto_of_tendsto (hγ.const_mul (2*(c:ℝ)))
    ((hμ.const_mul ((c:ℝ)^2)).add hζ)
  apply Eventually.of_forall
  intro n
  have hb := integral_mono_measure (hle c)
    (Eventually.of_forall fun x => dprofile_nonneg ((n:ℝ≥0)+1) t x)
    (dprofile_integrable_measure (c^2 • μ + ζ) _ _)
  rw [integral_add_measure (dprofile_integrable_measure (c^2 • μ) _ _)
    (dprofile_integrable_measure ζ _ _)] at hb
  simpa only [integral_smul_nnreal_measure,NNReal.smul_def,smul_eq_mul,NNReal.coe_mul,
    NNReal.coe_ofNat,NNReal.coe_pow] using hb

end CAT0Fillings.SmoothCutoff
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal BigOperators

namespace CAT0Fillings
namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma ae_distribution_gradient_bounds {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) :
    ∀ᵐ t : ℝ,
      (((q.gradientMeasure u).map u).rnDeriv volume t).toReal^2 ≤
        (((MassMeasure.currentMassMeasure hT).map u).rnDeriv volume t).toReal *
        (((q.energyMeasure u).map u).rnDeriv volume t).toReal ∧
      (((q.gradientMeasure u).map u).rnDeriv volume t).toReal ≤
        (K:ℝ)*(((MassMeasure.currentMassMeasure hT).map u).rnDeriv volume t).toReal := by
  let := q.gradientMeasure_finite hu
  let := q.energyMeasure_finite hu
  have hlin : (q.gradientMeasure u).map u ≤ K • (MassMeasure.currentMassMeasure hT).map u := by
    have h := Measure.map_mono (q.gradientMeasure_le hu) hu.continuous.measurable
    simpa only [Measure.map_smul _ hu.continuous.measurable.aemeasurable] using h
  have hquad (c : ℝ≥0) : (2*c) • (q.gradientMeasure u).map u ≤
      c^2 • (MassMeasure.currentMassMeasure hT).map u + (q.energyMeasure u).map u := by
    have h := Measure.map_mono (q.gradient_quadratic_le hu c) hu.continuous.measurable
    simpa only [Measure.map_smul _ hu.continuous.measurable.aemeasurable,
      Measure.map_add _ _ hu.continuous.measurable] using h
  exact (SmoothCutoff.ae_density_cauchy _ _ _ hquad).and
    (SmoothCutoff.ae_density_smul_le _ _ K hlin)

theorem ae_intrinsic_coarea (hI : IsIntegral (k+1) T) (hz : boundarySucc T = 0)
    (hX : IsCAT0 X) {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ∀ᵐ t : ℝ,
      IsIntegral (k+1) (BorelRestriction.restrictCurrent hT {x | t < u x}) ∧
      (mass (boundarySucc (BorelRestriction.restrictCurrent hT {x | t < u x})))^2 ≤
        (((MassMeasure.currentMassMeasure hT).map u).rnDeriv volume t).toReal *
        (((q.energyMeasure u).map u).rnDeriv volume t).toReal ∧
      mass (boundarySucc (BorelRestriction.restrictCurrent hT {x | t < u x})) ≤
        (K:ℝ)*(((MassMeasure.currentMassMeasure hT).map u).rnDeriv volume t).toReal := by
  have hub : BoundedLip u := ⟨⟨K,hu⟩,by
    obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hu.continuous.continuousOn
    exact ⟨M,fun x => by simpa only [Real.norm_eq_abs] using hM x (mem_univ _)⟩⟩
  obtain ⟨S,G,hG,hG0,hS,hGI,hact,hweight⟩ := integerRectifiable_scalar_coarea hT hI.2.1 hX hu
  have hSm := hS.mono (fun _ ht => ht.1)
  have hmass := q.ae_coarea_mass_le_gradient hu hSm hact hweight
  have heq := Slicing.ae_superlevelSlice_eq_coarea hT hI.2.1 hI.2.2.1 hub hSm hact hweight
  obtain ⟨H,hH,hH0,hHI,hR⟩ := Slicing.ae_integral_restrict hI hX hu
  filter_upwards [hmass,heq,hR,q.ae_distribution_gradient_bounds hu] with t hm he hr hd
  have hE : MeasurableSet {x | t < u x} := measurableSet_lt measurable_const hu.continuous.measurable
  have he' : BorelRestriction.restrictCurrent hI.2.2.1 {x | t < u x} -
      boundarySucc (BorelRestriction.restrictCurrent hT {x | t < u x}) = S t := he
  rw [Slicing.restrictCurrent_zero_of_eq_zero hI.2.2.1 hz hE,zero_sub] at he'
  have hp : mass (boundarySucc (BorelRestriction.restrictCurrent hT {x | t < u x})) =
      mass (S t) := by rw [←he',mass_neg]
  refine ⟨hr.1,?_,?_⟩
  · rw [hp]
    nlinarith [mass_nonneg (S t), ENNReal.toReal_nonneg
      (a := ((q.gradientMeasure u).map u).rnDeriv volume t)]
  · rw [hp]
    exact hm.trans hd.2

end ChartGeometry
end CAT0Fillings
end

end OAI
