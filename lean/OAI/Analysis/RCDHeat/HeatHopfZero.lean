import Mathlib
import OAI.Analysis.RCDHeat.HeatFisherSqrt
import OAI.Analysis.RCDHeat.InnerPath
import OAI.Analysis.RCDHeat.SqrtPairSlope

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: HeatHopfZero, HeatKuwadaZero, RCDHeatTransportZero, HeatWasserstein, ActionDescentSqueeze. -/



namespace RegularPointCoordinates

section
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] [μ.Regular] hQ in
 theorem integral_mulLp_continuous {φ : X → ℝ} (hφ : MemLp φ 2 μ) :
    Continuous (fun F : Lp ℝ 2 μ => ∫x, φ x*F x ∂μ) := by
  have he : (fun F : Lp ℝ 2 μ => ∫x, φ x*F x ∂μ) =
      fun F => inner ℝ (hφ.toLp φ) F := by
    funext F
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hφ.coeFn_toLp] with x hx
    rw [Real.inner_apply,hx]
  rw [he]
  exact continuous_const.inner continuous_id

variable [SigmaFinite μ]
 theorem heat_hopf_entropy_dual_zero {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (hgeo : IsGeodesicSpace X) (p : X) (R : ℝ) (h0 : ∀x, R < dist p x → φ x = 0)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) (hfi : Integrable f μ)
    {r : ℝ} (hfr : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    (C : ℝ≥0) (hfC : ∀ᵐ x ∂μ, |f x| ≤ C) {t : ℝ} (ht : 0 < t) :
    (∫x, hopfLax φ t x*heatAt μ hQ t f x ∂μ) - (∫x, φ x*f x ∂μ) ≤
      ((∫x, f x*Real.log (f x) ∂μ)-
        ∫x, heatAt μ hQ t f x*Real.log (heatAt μ hQ t f x) ∂μ)/2 := by
  let a : ℕ → ℝ := fun k => (t/2)*entropyScale k
  have ha (k : ℕ) : 0 < a k := mul_pos (half_pos ht) (entropyScale_pos k)
  have hat (k : ℕ) : a k ≤ t/2 := by
    have hs := entropyScale_antitone (Nat.zero_le k)
    have hs0 : entropyScale 0 = 1 := by norm_num [entropyScale]
    rw [hs0] at hs
    dsimp only [a]
    nlinarith
  have haz : Tendsto a atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (entropyScale_tendsto.mono_right nhdsWithin_le_nhds).const_mul (t/2)
  have haI (k : ℕ) : a k ∈ Icc 0 t := ⟨(ha k).le,(hat k).trans (by linarith)⟩
  have ha_sub (k : ℕ) : t-a k ∈ Icc (t/2) (2*t) := by
    constructor <;> linarith [hat k,ha k]
  have hpath := heatAt_entropy_absolutelyContinuous_nonneg μ hQ p hA hB hvol f hf0 hfi hfr
    (show (0:ℝ) ≤ 0 from le_rfl) ht.le
  have hEnt := (hpath.continuousOn 0 left_mem_uIcc).tendsto.comp
    (show Tendsto a atTop (𝓝[uIcc 0 t] 0) from by
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨haz,Eventually.of_forall (fun k => by simpa [uIcc_of_le ht.le] using haI k)⟩)
  simp only [heatAt_zero] at hEnt
  have hφS : HasCompactSupport φ := by
    apply HasCompactSupport.intro (isCompact_closedBall p R)
    intro x hx
    exact h0 x (by simpa only [mem_closedBall,not_le,dist_comm] using hx)
  have hφ2 : MemLp φ 2 μ := hφ.continuous.memLp_of_hasCompactSupport hφS
  have hφlim := (integral_mulLp_continuous μ hφ2).tendsto (heatAt μ hQ 0 f) |>.comp
    ((heatAt_continuous μ hQ f).tendsto 0 |>.comp haz)
  simp only [heatAt_zero] at hφlim
  have h2 : t/2 ≤ 2*t := by linarith
  obtain ⟨J,hJ⟩ := hopfPathSobolev_lipschitz μ hQ hφ hgeo p R h0 (half_pos ht) h2
  have hH := ((show Continuous (fun _ : ℝ => heatAt μ hQ t f) from continuous_const).inner (𝕜 := ℝ) hJ.continuous).tendsto t |>.comp
    (show Tendsto (fun k => t-a k) atTop (𝓝 t) from by simpa using tendsto_const_nhds.sub haz)
  have hHeq (q : ℝ) (hq : q ∈ Icc (t/2) (2*t)) :=
    inner_hopfPathSobolev μ hQ hφ hgeo p R h0 (heatAt μ hQ t f) (half_pos ht) h2 hq
  have hH' : Tendsto (fun k => ∫x, hopfLax φ (t-a k) x*heatAt μ hQ t f x ∂μ) atTop
      (𝓝 (∫x, hopfLax φ t x*heatAt μ hQ t f x ∂μ)) := by
    convert hH using 1
    · funext k
      exact (hHeq _ (ha_sub k)).symm
    · congr 1
      exact (hHeq _ ⟨by linarith,by linarith⟩).symm
  apply le_of_tendsto_of_tendsto (hH'.sub hφlim) ((hEnt.sub_const _).div_const 2)
  apply Eventually.of_forall
  intro k
  apply heat_hopf_entropy_dual μ hQ hφ hgeo p R h0 f hf0 C hfC (ha k) (by linarith [hat k])
    (heatAt_integrable_of_nonneg μ hQ (a k) f hf0 hfi)
    (heatAt_integrable_of_nonneg μ hQ t f hf0 hfi)
    (heatAt_entropy_integrable μ hQ p hA hB hvol f hf0 hfr (ha k).le)
    (heatAt_entropy_integrable μ hQ p hA hB hvol f hf0 hfr ht.le)
  rw [heatAt_integral_eq_of_exponential_volume μ hQ p hA hB hvol f hf0 hfi (ha k).le,
    heatAt_integral_eq_of_exponential_volume μ hQ p hA hB hvol f hf0 hfi ht.le]

end

 
section
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
variable (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ) [SigmaFinite μ]
 theorem heat_coupling_entropy_zero (hgeo : IsGeodesicSpace X) (p : X) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) (hfi : Integrable f μ)
    (hfm : (∫x, f x ∂μ) = 1) {r : ℝ} (hfr : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    (C : ℝ≥0) (hfC : ∀ᵐ x ∂μ, |f x| ≤ C) {t : ℝ} (ht : 0 < t) :
    ∃ π : Measure (X×X), IsProbabilityMeasure π ∧
      π.map Prod.fst = heatMeasure μ hQ 0 f ∧ π.map Prod.snd = heatMeasure μ hQ t f ∧
      transportCost π ≤ ENNReal.ofReal (t*
        ((∫x, heatAt μ hQ 0 f x*Real.log (heatAt μ hQ 0 f x) ∂μ)-
          ∫x, heatAt μ hQ t f x*Real.log (heatAt μ hQ t f x) ∂μ)) := by
  let := heatMeasure_probability μ hQ p hA hB hvol f hf0 hfi hfm (le_refl 0)
  let := heatMeasure_probability μ hQ p hA hB hvol f hf0 hfi hfm ht.le
  have hE := coupling_of_compact_hopf_bound (heatMeasure μ hQ 0 f) (heatMeasure μ hQ t f)
    p hgeo ht
    (((∫x, heatAt μ hQ 0 f x*Real.log (heatAt μ hQ 0 f x) ∂μ)-
      ∫x, heatAt μ hQ t f x*Real.log (heatAt μ hQ t f x) ∂μ)/2)
  obtain ⟨π,hp,hF,hS,hc⟩ := hE (fun φ L hφ R hR => by
    rw [integral_heatMeasure μ hQ f hf0,integral_heatMeasure μ hQ f hf0]
    simpa only [heatAt_zero, one_apply_eq_self] using
      heat_hopf_entropy_dual_zero μ hQ hφ hgeo p R hR hA hB hvol f hf0 hfi hfr C hfC ht)
  refine ⟨π,hp,hF,hS,?_⟩
  convert transportCost_le_of_scaled π ht hc using 2; ring

 theorem heat_coupling_fisher_action_nonneg (hgeo : IsGeodesicSpace X) (p : X) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) (hfi : Integrable f μ)
    (hfm : (∫x, f x ∂μ) = 1) {r : ℝ} (hfr : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    (C : ℝ≥0) (hfC : ∀ᵐ x ∂μ, |f x| ≤ C) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    ∃ π : Measure (X×X), IsProbabilityMeasure π ∧
      π.map Prod.fst = heatMeasure μ hQ s f ∧ π.map Prod.snd = heatMeasure μ hQ t f ∧
      transportCost π ≤ ENNReal.ofReal (t-s)*(∫⁻r in Ioc s t, fisherInformation μ hQ f r) := by
  rw [heatAt_entropy_dissipation_nonneg μ hQ p hA hB hvol f hf0 hfi hfr hs hst.le,
    ← ENNReal.ofReal_mul (sub_pos.mpr hst).le]
  rcases eq_or_lt_of_le hs with rfl | hs
  · simpa only [sub_zero] using
      heat_coupling_entropy_zero μ hQ hgeo p hA hB hvol f hf0 hfi hfm hfr C hfC hst
  · exact heat_coupling_entropy μ hQ hgeo p hA hB hvol f hf0 hfi hfm hfr C hfC hs hst

end

 
section
open Set Metric Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace
 theorem NoncollapsedRCD.heat_optimal_transport_action_nonneg (K : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (p : X) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ (f : Lp ℝ 2 (hausdorff n X)), 0 ≤ f →
      (∃ r : ℝ, ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r) →
      (∫x, f x ∂hausdorff n X) = 1 → ∀ C : ℝ≥0,
      (∀ᵐ x ∂hausdorff n X, |f x| ≤ C) → ∀ s t : ℝ, 0 ≤ s → s < t →
      ∃ plan : Measure C(Time,X), IsProbabilityMeasure plan ∧
        (∀ᵐ γ ∂plan, IsGeodesic γ) ∧
        IsOptimalCoupling (heatMeasure (hausdorff n X) hX.quadratic s f)
          (heatMeasure (hausdorff n X) hX.quadratic t f)
          (plan.map (fun γ => (γ 0,γ 1))) ∧
        transportCost (plan.map (fun γ => (γ 0,γ 1))) ≤
          ENNReal.ofReal (t-s)*(∫⁻r in Ioc s t, fisherInformation (hausdorff n X) hX.quadratic f r) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  intro f hf0 hfs hfm C hfC s t hs hst
  obtain ⟨Hsp,Hsa,Hsm,_⟩ := hX.heat_law K n hn p f hf0 hfs hfm s hs
  obtain ⟨Htp,Hta,Htm,_⟩ := hX.heat_law K n hn p f hf0 hfs hfm t (hs.trans hst.le)
  obtain ⟨plan,hp,hg,hopt,_⟩ := hX.cd _ _ Hsp Htp Hsa Hta Hsm Htm
  refine ⟨plan,hp,hg,hopt,?_⟩
  obtain ⟨r,hfr⟩ := hfs
  obtain ⟨A,B,hA,hB,hvol⟩ := hX.exponential_volume K n hn p
  have hi := lp_integrable_of_bounded_support (hausdorff n X) f p hfr
  obtain ⟨π,_,hF,hS,hc⟩ := heat_coupling_fisher_action_nonneg (hausdorff n X) hX.quadratic
    hX.geodesic p hA hB hvol f hf0 hi hfm hfr C hfC hs hst
  exact (hopt.2.2 π hF hS).trans hc
end

 
section
open Set Metric Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
 theorem boltzmannEntropy_heatMeasure_eq [ProperSpace X] (μ : Measure X) [μ.Regular]
    (hQ : QuadraticCheegerEnergy μ) [SigmaFinite μ] (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) (t : ℝ) :
    boltzmannEntropy μ (heatMeasure μ hQ t f) =
      ∫x, heatAt μ hQ t f x*Real.log (heatAt μ hQ t f x) ∂μ := by
  apply integral_congr_ae
  filter_upwards [heatMeasure_rnDeriv μ hQ t f hf0] with x hx
  rw [hx]
attribute [local instance] pathBorel pathBorelSpace
 

 theorem NoncollapsedRCD.heat_wasserstein_HWI (K : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (p : X) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ (f : Lp ℝ 2 (hausdorff n X)), 0 ≤ f →
      (∃ r : ℝ, ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r) →
      (∫x, f x ∂hausdorff n X) = 1 → ∀ C : ℝ≥0,
      (∀ᵐ x ∂hausdorff n X, |f x| ≤ C) → ∀ s t : ℝ, 0 < s → 0 ≤ t →
      fisherInformation (hausdorff n X) hX.quadratic f s ≠ ∞ →
      let μ := hausdorff n X
      let ρ := fun r => heatMeasure μ hX.quadratic r f
      boltzmannEntropy μ (ρ s)-boltzmannEntropy μ (ρ t) ≤
        Real.sqrt (fisherInformation μ hX.quadratic f s).toReal*
          Real.sqrt (wassersteinSq (ρ s) (ρ t)).toReal+
          (|K|/2)*(wassersteinSq (ρ s) (ρ t)).toReal := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  let μ := hausdorff n X
  intro f hf0 hfs hfm C hfC s t hs ht hI
  change boltzmannEntropy μ _-boltzmannEntropy μ _ ≤ _
  let : NeZero μ := ⟨by
    intro hz
    have hfz : ∫x, f x ∂μ = 0 := by rw [hz]; simp
    exact (by norm_num : (1:ℝ) ≠ 0) (hfm.symm.trans hfz)⟩
  obtain ⟨Hsp,Hsa,Hsm,_⟩ := hX.heat_law K n hn p f hf0 hfs hfm s hs.le
  obtain ⟨Htp,Hta,Htm,Hte⟩ := hX.heat_law K n hn p f hf0 hfs hfm t ht
  let := Hsp
  let := Htp
  obtain ⟨plan,hp,_,hopt,_⟩ := hX.cd _ _ Hsp Htp Hsa Hta Hsm Htm
  let π := plan.map (fun γ => (γ 0,γ 1))
  obtain ⟨r,hfr⟩ := hfs
  obtain ⟨A,B,hA,hB,hvol⟩ := hX.exponential_volume K n hn p
  have hsd := heatMeasure_dist_sq_integrable μ hX.quadratic p hA hB hvol f hf0 hfr hs.le
  have htd := heatMeasure_dist_sq_integrable μ hX.quadratic p hA hB hvol f hf0 hfr ht
  have hcfin : transportCost π ≠ ∞ := coupling_transportCost_ne_top hopt.1 hopt.2.1 p hsd htd
  have hh := hX.cd.heat_HWI μ hX.quadratic K n p hA hB hvol f hf0 hfm hfr C
    (hfC.mono fun x hx => (le_abs_self _).trans hx) hs hI _ Hta Hte
    (heatMeasure_exp_dist_integrable μ hX.quadratic p hA hB hvol f hf0 hfr (by positivity) ht)
    htd π hopt.1 hopt.2.1
  have hpowfin : (transportCost π)^(1/(2:ℝ)) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hcfin
  have h1fin : ENNReal.ofReal (Real.sqrt (fisherInformation μ hX.quadratic f s).toReal)*
      (transportCost π)^(1/(2:ℝ)) ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpowfin
  have h2fin : ENNReal.ofReal (|K|/2)*transportCost π ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hcfin
  have hr := (ENNReal.ofReal_le_iff_le_toReal (ENNReal.add_ne_top.mpr ⟨h1fin,h2fin⟩)).mp hh
  rw [ENNReal.toReal_add h1fin h2fin,ENNReal.toReal_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _),ENNReal.toReal_ofReal (by positivity : 0 ≤ |K|/2),
    ← ENNReal.toReal_rpow,← Real.sqrt_eq_rpow] at hr
  rw [wassersteinSq_eq_cost hopt]
  exact hr

 

 theorem NoncollapsedRCD.heat_wasserstein_entropy_action (K : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (p : X) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ (f : Lp ℝ 2 (hausdorff n X)), 0 ≤ f →
      (∃ r : ℝ, ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r) →
      (∫x, f x ∂hausdorff n X) = 1 → ∀ C : ℝ≥0,
      (∀ᵐ x ∂hausdorff n X, |f x| ≤ C) → ∀ s t : ℝ, 0 ≤ s → s < t →
      let μ := hausdorff n X
      let ρ := fun r => heatMeasure μ hX.quadratic r f
      wassersteinSq (ρ s) (ρ t) ≠ ∞ ∧
      (wassersteinSq (ρ s) (ρ t)).toReal ≤
        (t-s)*(boltzmannEntropy μ (ρ s)-boltzmannEntropy μ (ρ t)) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  let μ := hausdorff n X
  intro f hf0 hfs hfm C hfC s t hs hst
  change wassersteinSq _ _ ≠ ∞ ∧ _
  obtain ⟨r,hfr⟩ := hfs
  obtain ⟨A,B,hA,hB,hvol⟩ := hX.exponential_volume K n hn p
  have hfi := lp_integrable_of_bounded_support μ f p hfr
  obtain ⟨π,_,h0,h1,hc⟩ := heat_coupling_fisher_action_nonneg μ hX.quadratic hX.geodesic
    p hA hB hvol f hf0 hfi hfm hfr C hfC hs hst
  rw [heatAt_entropy_dissipation_nonneg μ hX.quadratic p hA hB hvol f hf0 hfi hfr hs hst.le,
    ← ENNReal.ofReal_mul (sub_pos.mpr hst).le,
    ← boltzmannEntropy_heatMeasure_eq μ hX.quadratic f hf0 s,
    ← boltzmannEntropy_heatMeasure_eq μ hX.quadratic f hf0 t] at hc
  have hw := (wassersteinSq_le_cost h0 h1).trans hc
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hw,?_⟩
  apply ENNReal.toReal_le_of_le_ofReal _ hw
  apply mul_nonneg (sub_pos.mpr hst).le
  rw [boltzmannEntropy_heatMeasure_eq μ hX.quadratic f hf0 s,
    boltzmannEntropy_heatMeasure_eq μ hX.quadratic f hf0 t,
    ← heatAt_fisher_integral_entropy_nonneg μ hX.quadratic p hA hB hvol f hf0 hfi hfr hs hst.le]
  exact intervalIntegral.integral_nonneg_of_forall hst.le (fun _ => ENNReal.toReal_nonneg)
end

 
open Set Filter
open scoped Topology
 

 theorem tendsto_speed_of_action_descent {α : Type*} {l : Filter α}
    {δ e q : α → ℝ} {I c : ℝ} (hI : 0 ≤ I) (hc : 0 ≤ c)
    (hδ : ∀ᶠ a in l, 0 ≤ δ a) (hδL : Tendsto δ l (𝓝 0))
    (heL : Tendsto e l (𝓝 I)) (hq : ∀ᶠ a in l, 0 ≤ q a)
    (hA : ∀ᶠ a in l, q a^2 ≤ e a)
    (hD : ∀ᶠ a in l, e a ≤ Real.sqrt I*q a+c*δ a*q a^2) :
    Tendsto q l (𝓝 (Real.sqrt I)) := by
  have hupper : ∀ᶠ a in l, q a ≤ Real.sqrt (e a) := hA.mono fun _ ha => Real.le_sqrt_of_sq_le ha
  have hupL := Real.continuous_sqrt.continuousAt.tendsto.comp heL
  rcases eq_or_lt_of_le hI with hi | hi
  · rw [← hi,Real.sqrt_zero] at hupL ⊢
    exact squeeze_zero' hq hupper hupL
  · have hpos := Real.sqrt_pos.mpr hi
    have hlow : ∀ᶠ a in l, (e a-c*δ a*e a)/Real.sqrt I ≤ q a := by
      filter_upwards [hδ,hA,hD] with a hδ hA hD
      apply (div_le_iff₀ hpos).mpr
      have hh := mul_le_mul_of_nonneg_left hA (mul_nonneg hc hδ)
      nlinarith
    have hlowL : Tendsto (fun a => (e a-c*δ a*e a)/Real.sqrt I) l (𝓝 (Real.sqrt I)) := by
      have hh := (heL.sub (((hδL.const_mul c).mul heL))).div_const (Real.sqrt I)
      have hid : I/Real.sqrt I = Real.sqrt I := by
        apply (div_eq_iff (ne_of_gt hpos)).mpr
        nlinarith [Real.sq_sqrt hI]
      simpa only [mul_zero,zero_mul,sub_zero,hid] using hh
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowL hupL hlow hupper
 

 theorem entropy_action_descent_right_speed {E W : ℝ → ℝ} {s I c : ℝ}
    (hI : 0 ≤ I) (hc : 0 ≤ c) (hE : HasDerivAt E (-I) s)
    (hW : ∀ᶠ t in 𝓝[>] s, 0 ≤ W t)
    (hA : ∀ᶠ t in 𝓝[>] s, W t ≤ (t-s)*(E s-E t))
    (hD : ∀ᶠ t in 𝓝[>] s, E s-E t ≤ Real.sqrt I*Real.sqrt (W t)+c*W t) :
    Tendsto (fun t => Real.sqrt (W t)/(t-s)) (𝓝[>] s) (𝓝 (Real.sqrt I)) := by
  have ht : ∀ᶠ t in 𝓝[>] s, s < t := self_mem_nhdsWithin
  have heL : Tendsto (fun t => (E s-E t)/(t-s)) (𝓝[>] s) (𝓝 I) := by
    have hh := (hasDerivAt_iff_tendsto_slope_left_right.mp hE).2.neg
    convert! hh using 1
    · ext t
      simp only [slope_def_field]
      ring
    · simp
  apply tendsto_speed_of_action_descent (δ := fun t => t-s)
    (e := fun t => (E s-E t)/(t-s)) hI hc
  · exact ht.mono fun _ hx => (sub_pos.mpr hx).le
  · simpa only [id_eq, sub_self] using
      ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 s) (𝓝 s)).mono_left nhdsWithin_le_nhds).sub_const s
  · exact heL
  · filter_upwards [hW,ht] with t hw ht
    exact div_nonneg (Real.sqrt_nonneg _) (sub_pos.mpr ht).le
  · filter_upwards [hW,hA,ht] with t hw ha ht
    have hne : t-s ≠ 0 := (sub_pos.mpr ht).ne'
    have hh := div_le_div_of_nonneg_right ha (sq_nonneg (t-s))
    convert! hh using 1
    · rw [div_pow,Real.sq_sqrt hw]
    · field_simp
  · filter_upwards [hW,hD,ht] with t hw hd ht
    have hne : t-s ≠ 0 := (sub_pos.mpr ht).ne'
    have hh := div_le_div_of_nonneg_right hd (sub_pos.mpr ht).le
    convert! hh using 1
    rw [div_pow,Real.sq_sqrt hw]
    field_simp

end RegularPointCoordinates

end OAI
