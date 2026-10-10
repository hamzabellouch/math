import OAI.Geometry.RCD.Heat.DimensionalEVI
import OAI.Geometry.RCD.Metric.DimensionalRateIntegralLimit

namespace OAI

/-! # Dimensional EVI against another actual heat law

The bounded reference laws converge in entropy and uniformly in transport
cost on each compact time interval. The continuous dimensional rate passes
through the interval integral, including at zero transport distance.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]

theorem NoncollapsedRCD.heat_reference_dimensional_EVI
    (K : ℝ) (n : ℕ) [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (hK : K ≤ 0) {N : ℝ} (hN : (n:ℝ) ≤ N) (p : X)
    (f g : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0)
    (hf0 : 0 ≤ f) (hfC : ∀ᵐ x ∂hausdorff n X, f x ≤ C)
    (hfm : ∫x, f x ∂hausdorff n X = 1)
    {rf : ℝ} (hfs : ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ rf)
    (hg0 : 0 ≤ g) (hgC : ∀ᵐ x ∂hausdorff n X, g x ≤ C)
    (hgm : ∫x, g x ∂hausdorff n X = 1)
    {rg : ℝ} (hgs : ∀ᵐ x ∂hausdorff n X, g x ≠ 0 → dist p x ≤ rg)
    {s a b : ℝ} (hs : 0 < s) (ha : 0 < a) (hab : a ≤ b) :
    ((wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic b f)
        (heatMeasure (hausdorff n X) hX.quadratic s g)).toReal-
      (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic a f)
        (heatMeasure (hausdorff n X) hX.quadratic s g)).toReal)/2 ≤
      ∫t in a..b, entropyPowerRate N
        (-(K*(wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic t f)
          (heatMeasure (hausdorff n X) hX.quadratic s g)).toReal/N))
        (Real.exp (-boltzmannEntropy (hausdorff n X) (heatMeasure (hausdorff n X) hX.quadratic t f)/N))
        (Real.exp (-boltzmannEntropy (hausdorff n X) (heatMeasure (hausdorff n X) hX.quadratic s g)/N)) := by
  let μ := hausdorff n X
  obtain ⟨A,B,hA,hB,hvol⟩ := hX.exponential_volume K n hn p
  have hgi := lp_integrable_of_bounded_support μ g p hgs
  have hdg := hX.heat_law K n hn p g hg0 ⟨rg,hgs⟩ hgm s hs.le
  let ν := heatMeasure μ hX.quadratic s g
  let : IsProbabilityMeasure ν := hdg.1
  let D : ℝ → ℝ := fun t => (wassersteinSq (heatMeasure μ hX.quadratic t f) ν).toReal
  let P : ℝ → ℝ := fun t => boltzmannEntropy μ (heatMeasure μ hX.quadratic t f)
  let E := boltzmannEntropy μ ν
  let η := fun R : ℝ => radialHeatMeasure μ hX.quadratic p R s g
  let W := fun R t : ℝ => (wassersteinSq (heatMeasure μ hX.quadratic t f) (η R)).toReal
  let F := fun R : ℝ => boltzmannEntropy μ (η R)
  have hfabs : ∀ᵐ x ∂μ, |f x| ≤ C := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr hf0,hfC] with x hl hu
    simpa only [abs_of_nonneg hl] using hu
  have hDc {t : ℝ} (ht : 0 < t) : ContinuousAt D t :=
    hX.heat_wassersteinSq_continuousAt K n hn p f hf0 ⟨rf,hfs⟩ hfm C hfabs ν hdg.2.1 hdg.2.2.1 ht
  have hPc {t : ℝ} (ht : 0 < t) : ContinuousAt P t :=
    hX.heat_entropy_continuousAt K n hn p f hf0 ⟨rf,hfs⟩ ht
  have hDcont : ContinuousOn D (Icc a b) := fun t ht => (hDc (ha.trans_le ht.1)).continuousWithinAt
  have hPcont : ContinuousOn P (Icc a b) := fun t ht => (hPc (ha.trans_le ht.1)).continuousWithinAt
  obtain ⟨H,R₀,hH,hR₀,hNorm⟩ := heat_normalized_cutoff_exponential μ hX.quadratic p hA hB hvol
    g C hg0 hgC hgi hgm hgs (a := 1) (T := s) (by norm_num) hs
  obtain ⟨J,hJ,hEnt⟩ := radialHeatMeasure_entropy_exponential μ hX.quadratic p hA hB hvol
    g hg0 hgi hgm hgs (a := 1) (T := s) (by norm_num)
  obtain ⟨L,hL,hCost⟩ := hX.heat_competitor_cutoff_cost K n hn p hA hB hvol
    f g C hf0 hfC hfm hfs hg0 hgC hgi hgm hgs (b := b) hs ha
  have hcost : ∀ᶠ R : ℝ in atTop, ∀ t ∈ Icc a b, |W R t-D t| ≤ L*Real.exp (-R) := by
    filter_upwards [eventually_ge_atTop R₀] with R hR
    have hR1 := hR₀.trans hR
    exact hCost R hR1 ((hNorm s le_rfl le_rfl R (zero_lt_one.trans_le hR1) hR).1)
  have hent : ∀ᶠ R : ℝ in atTop, |F R-E| ≤ J*Real.exp (-R) := by
    filter_upwards [eventually_ge_atTop R₀] with R hR
    have hRp := zero_lt_one.trans_le (hR₀.trans hR)
    simpa only [neg_mul,one_mul] using hEnt s hs.le le_rfl R hRp ((hNorm s le_rfl le_rfl R hRp hR).1)
  have he0 : Tendsto (fun R : ℝ => Real.exp (-R)) atTop (𝓝 0) := by
    simpa only [neg_mul,one_mul] using exp_neg_mul_tendsto_zero (by norm_num : (0:ℝ) < 1)
  have hwl (t : ℝ) (ht : t ∈ Icc a b) : Tendsto (fun R => W R t) atTop (𝓝 (D t)) :=
    tendsto_of_abs_cutoff_error tendsto_const_nhds (by simpa using he0.const_mul L)
      (hcost.mono fun R hR => hR t ht)
  have hfl : Tendsto F atTop (𝓝 E) :=
    tendsto_of_abs_cutoff_error tendsto_const_nhds (by simpa using he0.const_mul J) hent
  have hWcont : ∀ᶠ R : ℝ in atTop, ContinuousOn (W R) (Icc a b) := by
    filter_upwards [eventually_ge_atTop R₀] with R hR
    have hRp := zero_lt_one.trans_le (hR₀.trans hR)
    have hd := radialHeatMeasure_data μ hX.quadratic p hA hB hvol g C hg0 hgC hgi hgm hRp hs
      ((hNorm s le_rfl le_rfl R hRp hR).1)
    let : IsProbabilityMeasure (η R) := hd.1
    intro t ht
    exact (hX.heat_wassersteinSq_continuousAt K n hn p f hf0 ⟨rf,hfs⟩ hfm C hfabs (η R)
      (withDensity_absolutelyContinuous _ _) (finiteSecondMoment_of_ae_dist_le _ p hd.2.2)
      (ha.trans_le ht.1)).continuousWithinAt
  obtain ⟨D₀,hD₀⟩ := isCompact_Icc.bddAbove_image hDcont.abs
  obtain ⟨P₀,hP₀⟩ := isCompact_Icc.bddAbove_image hPcont.abs
  let M := |D₀|+|P₀|+|E|+L+J+1
  have hbound : ∀ᶠ R : ℝ in atTop, ∀ t ∈ Icc a b,
      |W R t| ≤ M ∧ |P t| ≤ M ∧ |F R| ≤ M := by
    filter_upwards [hcost,hent,eventually_ge_atTop R₀] with R hc he hR
    intro t ht
    have hd0 : |D t| ≤ D₀ := hD₀ (mem_image_of_mem _ ht)
    have hp0 : |P t| ≤ P₀ := hP₀ (mem_image_of_mem _ ht)
    have hex : Real.exp (-R) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hR₀.trans hR])
    have hc' := (abs_sub_abs_le_abs_sub (W R t) (D t)).trans (hc t ht)
    have he' := (abs_sub_abs_le_abs_sub (F R) E).trans he
    have hl := mul_le_of_le_one_right hL hex
    have hj := mul_le_of_le_one_right hJ hex
    dsimp only [M]
    exact ⟨by linarith [le_abs_self D₀,abs_nonneg P₀,abs_nonneg E],
      by linarith [le_abs_self P₀,abs_nonneg D₀,abs_nonneg E],
      by linarith [abs_nonneg D₀,abs_nonneg P₀]⟩
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have hIntegral := integral_dimensionalEntropyRate_tendsto hK hN0 hab hWcont hPcont hwl hfl hbound
  have hvi : ∀ᶠ R : ℝ in atTop, (W R b-W R a)/2 ≤
      ∫t in a..b, dimensionalEntropyRate K N (W R t,P t,F R) := by
    filter_upwards [eventually_ge_atTop R₀] with R hR
    have hRp := zero_lt_one.trans_le (hR₀.trans hR)
    have hd := radialHeatMeasure_data μ hX.quadratic p hA hB hvol g C hg0 hgC hgi hgm hRp hs
      ((hNorm s le_rfl le_rfl R hRp hR).1)
    let : IsProbabilityMeasure (η R) := hd.1
    have hf2C : ∀ᵐ x ∂μ, f x ≤ (2*C:ℝ≥0) := hfC.mono fun x hx => by
      exact hx.trans (by simp only [NNReal.coe_mul,NNReal.coe_ofNat]; nlinarith [C.property])
    have hv := hX.bounded_heat_dimensional_EVI K n hn hK hN p f (2*C) hf0 hf2C hfm hfs (η R)
      (by simpa only [NNReal.coe_mul,NNReal.coe_ofNat] using hd.2.1) hd.2.2 ha hab
    simpa only [dimensionalEntropyRate, W,P,F,max_eq_left ENNReal.toReal_nonneg] using hv
  have hleft : Tendsto (fun R => (W R b-W R a)/2) atTop (𝓝 ((D b-D a)/2)) :=
    ((hwl b ⟨hab,le_rfl⟩).sub (hwl a ⟨le_rfl,hab⟩)).div_const 2
  have hout := le_of_tendsto_of_tendsto hleft hIntegral hvi
  simpa only [dimensionalEntropyRate,D,P,E,max_eq_left ENNReal.toReal_nonneg] using hout

end RegularPointCoordinates

end

end OAI
