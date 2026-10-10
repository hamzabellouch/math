import OAI.Geometry.RCD.Transport.DimensionalCutoff
import OAI.Geometry.RCD.Sobolev.DimensionalCutoffLimit
import OAI.Geometry.RCD.Sobolev.RealCutoffConvergence

namespace OAI

/-! # The dimensional evolution slope for the actual heat flow

The exact dimensional rate survives radial cutoff approximation.
Both entropy and transport cost converge, including at zero distance.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]

theorem NoncollapsedRCD.bounded_heat_frequent_dimensional_slope
    (K : ℝ) (n : ℕ) [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (hK : K ≤ 0) {N : ℝ} (hN : (n:ℝ) ≤ N) (p : X)
    (f : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0) (hf0 : 0 ≤ f)
    (hfC : ∀ᵐ x ∂hausdorff n X, f x ≤ C)
    (hfm : ∫x, f x ∂hausdorff n X = 1)
    {r : ℝ} (hfs : ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r)
    (ν : Measure X) [IsProbabilityMeasure ν] (hν : ν ≤ ENNReal.ofReal C • hausdorff n X)
    {rν : ℝ} (hνS : ∀ᵐ x ∂ν, dist x p ≤ rν) {t : ℝ} (ht : 0 < t) :
    ∀ z, entropyPowerRate N
      (-(K*(wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic t f) ν).toReal/N))
      (Real.exp (-boltzmannEntropy (hausdorff n X) (heatMeasure (hausdorff n X) hX.quadratic t f)/N))
      (Real.exp (-boltzmannEntropy (hausdorff n X) ν/N)) < z →
      ∃ᶠ s in 𝓝[>] t, slope (fun q =>
        (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic q f) ν).toReal/2) t s < z := by
  let μ := hausdorff n X
  obtain ⟨A,B,hA,hB,hvol⟩ := hX.exponential_volume K n hn p
  have hfi := lp_integrable_of_bounded_support μ f p hfs
  have hνac : ν ≪ μ := (Measure.absolutelyContinuous_of_le hν).trans Measure.smul_absolutelyContinuous
  have hν2 := finiteSecondMoment_of_ae_dist_le ν p hνS
  have hfabs : ∀ᵐ x ∂μ, |f x| ≤ C := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr hf0,hfC] with x hl hu
    simpa only [abs_of_nonneg hl] using hu
  let b := 12*B+4
  have hb : 0 ≤ b := by dsimp [b]; positivity
  let a := 2*b+4
  have ha : 0 ≤ a := by dsimp [a]; positivity
  obtain ⟨H,R₀,hH,hR₀,hNorm⟩ := heat_normalized_cutoff_exponential μ hX.quadratic p hA hB hvol
    f C hf0 hfC hfi hfm hfs (a := a) (T := t+1) ha ht
  obtain ⟨J,hJ,hEnt⟩ := radialHeatMeasure_entropy_exponential μ hX.quadratic p hA hB hvol
    f hf0 hfi hfm hfs (a := a) (T := t+1) ha
  obtain ⟨L,hL,hCost⟩ := hX.radial_heat_cost_exponential K n hn p hA hB hvol f C hf0 hfC hfi hfm hfs
    ν hνac hν2 (a := a) (T := t+1) ha ht
  let D : ℝ → ℝ := fun s => (wassersteinSq (heatMeasure μ hX.quadratic s f) ν).toReal
  let E : ℝ → ℝ := fun s => boltzmannEntropy μ (heatMeasure μ hX.quadratic s f)
  let Q : ℝ → ℝ := fun R => (wassersteinSq (radialHeatMeasure μ hX.quadratic p R
    (t+Real.exp (-(b+1)*R)) f) ν).toReal
  let F : ℝ → ℝ := fun R => boltzmannEntropy μ (radialHeatMeasure μ hX.quadratic p R
    (t+Real.exp (-(b+1)*R)) f)
  have hDt : ContinuousAt D t :=
    hX.heat_wassersteinSq_continuousAt K n hn p f hf0 ⟨r,hfs⟩ hfm C hfabs ν hνac hν2 ht
  have hEt : ContinuousAt E t := hX.heat_entropy_continuousAt K n hn p f hf0 ⟨r,hfs⟩ ht
  have htime : ∀ᶠ R : ℝ in atTop, Real.exp (-(b+1)*R) ≤ 1 :=
    (exp_neg_mul_tendsto_zero (by linarith : 0 < b+1)).eventually_le_const (by norm_num)
  have hbounds : ∀ᶠ R : ℝ in atTop,
      |Q R-D (t+Real.exp (-(b+1)*R))| ≤ L*Real.exp (-(2*b+4)*R) ∧
      |F R-E (t+Real.exp (-(b+1)*R))| ≤ J*Real.exp (-(2*b+4)*R) := by
    filter_upwards [eventually_ge_atTop (max R₀ (max 1 rν)),htime] with R hR htime
    have hRR : R₀ ≤ R := (le_max_left _ _).trans hR
    have hR1 : 1 ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hR)
    have hRp : 0 < R := zero_lt_one.trans_le hR1
    have hs : t ≤ t+Real.exp (-(b+1)*R) := le_add_of_nonneg_right (Real.exp_pos _).le
    have hst : t+Real.exp (-(b+1)*R) ≤ t+1 := by linarith only [htime]
    have hm := (hNorm _ hs hst R hRp hRR).1
    exact ⟨hCost _ hs hst R hR1 hm,hEnt _ (add_pos ht (Real.exp_pos _)).le hst R hRp hm⟩
  have hstep : Tendsto (fun R : ℝ => t+Real.exp (-(b+1)*R)) atTop (𝓝 t) := by
    simpa using (exp_neg_mul_tendsto_zero (by linarith : 0 < b+1)).const_add t
  have htail : Tendsto (fun R : ℝ => Real.exp (-(2*b+4)*R)) atTop (𝓝 0) :=
    exp_neg_mul_tendsto_zero (by linarith)
  have hQl : Tendsto Q atTop (𝓝 (D t)) := tendsto_of_abs_cutoff_error
    (hDt.tendsto.comp hstep) (by simpa using htail.const_mul L) (hbounds.mono fun _ h => h.1)
  have hFl : Tendsto F atTop (𝓝 (E t)) := tendsto_of_abs_cutoff_error
    (hEt.tendsto.comp hstep) (by simpa using htail.const_mul J) (hbounds.mono fun _ h => h.2)
  let G : ℝ → ℝ := fun R => entropyPowerRate N (-(K*Q R/N))
    (Real.exp (-F R/N)) (Real.exp (-boltzmannEntropy μ ν/N))
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have hnn (w : ℝ) (hw : 0 ≤ w) : 0 ≤ -(K*w/N) :=
    neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hK hw) hN0.le)
  have hGl : Tendsto G atTop (𝓝 (entropyPowerRate N (-(K*D t/N))
      (Real.exp (-E t/N)) (Real.exp (-boltzmannEntropy μ ν/N)))) :=
    tendsto_entropyPowerRate (fun R => hnn (Q R) ENNReal.toReal_nonneg)
      (hnn (D t) ENNReal.toReal_nonneg) (Real.exp_ne_zero _)
      ((hQl.const_mul K).div_const N).neg
      (Real.continuous_exp.tendsto _ |>.comp (hFl.neg.div_const N)) tendsto_const_nhds
  apply frequent_slope_of_dimensional_cutoffs (D := D) (Q := Q) (G := G)
    (C := 1000*(A+1)) (A := (2*(1+1/(t/2)))^2*‖f‖) (H := H) hb hGl
  have htime : ∀ᶠ R : ℝ in atTop, Real.exp (-(b+1)*R) ≤ 1 :=
    (exp_neg_mul_tendsto_zero (by linarith : 0 < b+1)).eventually_le_const (by norm_num)
  filter_upwards [eventually_ge_atTop (max R₀ (max 1 rν)),htime] with R hR htime
  have hRR : R₀ ≤ R := (le_max_left _ _).trans hR
  have hR1 : 1 ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hR)
  have hRν : rν ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans hR)
  have hRp : 0 < R := zero_lt_one.trans_le hR1
  let h := Real.exp (-(b+1)*R)
  have hh : 0 < h := Real.exp_pos _
  have hs : t ≤ t+h := le_add_of_nonneg_right hh.le
  have hst : t+h ≤ t+1 := by dsimp only [h]; linarith only [htime]
  have hn := hNorm (t+h) hs hst R hRp hRR
  refine ⟨hCost (t+h) hs hst R hR1 hn.1,?_⟩
  have hv : ∀ᵐ x ∂ν, dist x p ≤ 2*R := hνS.mono fun x hx => hx.trans (by linarith)
  have hsec := hX.dimensional_cutoff_heat_secant K n ‹2 ≤ n› hK hN p hA hB hvol f C hf0 hfC hfi hfm hfs ν hν
    hR1 ht hh hv hn.1
  have hnorm : ‖radialHeatSobolev μ hX.quadratic p hRp (add_pos ht hh) f C-
      heatSobolev μ hX.quadratic (t+h) (add_pos ht hh) f‖ ≤ H*Real.exp (-(2*b+4)*R) := by
    simpa only [radialHeatSobolev,norm_sub_rev,a] using hn.2
  apply hsec.trans
  apply add_le_add le_rfl
  change (1000*(A+1)*Real.exp (b*R))*_ ≤ (1000*(A+1)*Real.exp (b*R))*_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left hnorm (by positivity)


end RegularPointCoordinates

end

end OAI
