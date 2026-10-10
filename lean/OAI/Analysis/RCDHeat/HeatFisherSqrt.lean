import Mathlib
import OAI.Analysis.RCDHeat.HeatEntropyPath
import OAI.Analysis.RCDHeat.NormalizedCutoff
import OAI.Analysis.RCDHeat.WeightedPlan

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: HeatFisherSqrt, RCDHeatConvexity, HeatHWI, WassersteinCost, HeatDissipationZero, HeatEntropyZeroPath. -/



namespace RegularPointCoordinates

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ) [SigmaFinite μ]

 theorem heat_fisher_eq_eight_sqrt_energy (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f)
    (hfi : Integrable f μ) {C : ℝ} (hC : 0 ≤ C) (hfC : ∀ᵐ x ∂μ, f x ≤ C)
    {t : ℝ} (ht : 0 < t) :
    fisherInformation μ hQ f t = 8*energyLp μ
      ((integrable_sqrt_memLp μ (heatAt_integrable_of_nonneg μ hQ t f hf0 hfi)
        ((Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ t f hf0))).toLp
          (fun x => Real.sqrt (heatAt μ hQ t f x))) := by
  have h0 : 0 ≤ SobolevSpace.toLp μ hQ (heatSobolev μ hQ t ht f) := by
    rw [heatSobolev_toLp]
    exact heatAt_nonneg μ hQ t f hf0
  have hI : Integrable (SobolevSpace.toLp μ hQ (heatSobolev μ hQ t ht f)) μ := by
    rw [heatSobolev_toLp]
    exact heatAt_integrable_of_nonneg μ hQ t f hf0 hfi
  have hB : ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ (heatSobolev μ hQ t ht f) x ≤ C := by
    rw [heatSobolev_toLp]
    exact heatAt_le_const μ hQ t hC f hfC
  have he := SobolevSpace.fisher_eq_eight_sqrt_energy μ hQ
    (heatSobolev μ hQ t ht f) h0 hI hC hB
  simp only [heatSobolev_toLp] at he
  rw [← he,fisherInformation_eq_integral μ hQ f ht]
  apply lintegral_congr_ae
  filter_upwards [(Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ t f hf0)] with x hx
  rw [abs_of_nonneg hx]

end

 
section
open Set Metric Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
section Moments
variable [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
 theorem heatMeasure_dist_sq_integrable (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) {r : ℝ} (hf : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    {t : ℝ} (ht : 0 ≤ t) : Integrable (fun x => dist p x^2) (heatMeasure μ hQ t f) := by
  rw [heatMeasure,integrable_withDensity_iff_integrable_smul₀'
    (Lp.aestronglyMeasurable (heatAt μ hQ t f)).aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply (heatAt_dist_pow_integrable μ hQ p hA hB hvol f hf 2 ht).congr
  filter_upwards [(Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ t f hf0)] with x hx
  rw [ENNReal.toReal_ofReal hx,smul_eq_mul,mul_comm]
end Moments

attribute [local instance] pathBorel pathBorelSpace
 

 theorem NoncollapsedRCD.heat_entropy_convex_plan (K : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (p : X) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ (f g : Lp ℝ 2 (hausdorff n X)), 0 ≤ f → 0 ≤ g →
      (∃ r : ℝ, ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r) →
      (∃ r : ℝ, ∀ᵐ x ∂hausdorff n X, g x ≠ 0 → dist p x ≤ r) →
      (∫x, f x ∂hausdorff n X) = 1 → (∫x, g x ∂hausdorff n X) = 1 →
      ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      let μ := hausdorff n X
      let ν₀ := heatMeasure μ hX.quadratic s f
      let ν₁ := heatMeasure μ hX.quadratic t g
      ∃ plan : Measure C(Time,X), IsProbabilityMeasure plan ∧
        (∀ᵐ γ ∂plan, IsGeodesic γ) ∧
        IsOptimalCoupling ν₀ ν₁ (plan.map (fun γ => (γ 0,γ 1))) ∧
        ∀ τ : Time, let ν := plan.map (fun γ => γ τ)
          ν.AbsolutelyContinuous μ ∧
          Integrable (fun x => (ν.rnDeriv μ x).toReal*Real.log (ν.rnDeriv μ x).toReal) μ ∧
          (∫x, (ν.rnDeriv μ x).toReal*Real.log (ν.rnDeriv μ x).toReal ∂μ) ≤
            (1-(τ:ℝ))*(∫x, (ν₀.rnDeriv μ x).toReal*Real.log (ν₀.rnDeriv μ x).toReal ∂μ) +
            (τ:ℝ)*(∫x, (ν₁.rnDeriv μ x).toReal*Real.log (ν₁.rnDeriv μ x).toReal ∂μ) +
            ((-K)*(τ:ℝ)*(1-(τ:ℝ))/2)*(∫γ, dist (γ 0) (γ 1)^2 ∂plan) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  intro f g hf0 hg0 hfs hgs hfm hgm s t hs ht
  obtain ⟨Hsp,Hsa,Hsm,Hse⟩ := hX.heat_law K n hn p f hf0 hfs hfm s hs
  obtain ⟨Htp,Hta,Htm,Hte⟩ := hX.heat_law K n hn p g hg0 hgs hgm t ht
  let := Hsp
  let := Htp
  obtain ⟨rf,hfr⟩ := hfs
  obtain ⟨rg,hgr⟩ := hgs
  obtain ⟨A,B,hA,hB,hvol⟩ := hX.exponential_volume K n hn p
  exact hX.cd.exists_finite_entropy_exp_plan _ K n _ _ Hsa Hta Hsm Htm Hse Hte p
    (show 0 ≤ B+1 by linarith)
    (integrable_exp_neg_dist_of_volume _ p hA hB (by linarith) hvol)
    (heatMeasure_exp_dist_integrable _ hX.quadratic p hA hB hvol f hf0 hfr (by positivity) hs)
    (heatMeasure_exp_dist_integrable _ hX.quadratic p hA hB hvol g hg0 hgr (by positivity) ht)
    (heatMeasure_dist_sq_integrable _ hX.quadratic p hA hB hvol f hf0 hfr hs)
    (heatMeasure_dist_sq_integrable _ hX.quadratic p hA hB hvol g hg0 hgr ht)
end

 
section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]
 

 theorem FullCD.heat_HWI (μ : Measure X) [μ.Regular]
    [NeZero μ] [SigmaFinite μ]
    (hQ : QuadraticCheegerEnergy μ) (K : ℝ) (n : ℕ) (hcd : FullCD μ K n)
    (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (Metric.closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) (hfM : ∫x, f x ∂μ = 1)
    {r : ℝ} (hfS : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    (C : ℝ≥0) (hfC : ∀ᵐ x ∂μ, f x ≤ C)
    {t : ℝ} (ht : 0 < t) (hI : fisherInformation μ hQ f t ≠ ∞)
    (ν : Measure X) [IsProbabilityMeasure ν] (hν : ν ≪ μ)
    (hνE : Integrable (fun x => (ν.rnDeriv μ x).toReal*Real.log (ν.rnDeriv μ x).toReal) μ)
    (hνExp : Integrable (fun x => Real.exp ((3*(B+1))*dist p x)) ν)
    (hνDist : Integrable (fun x => dist p x^2) ν)
    (π : Measure (X×X))
    (hπ₀ : π.map Prod.fst = heatMeasure μ hQ t f) (hπ₁ : π.map Prod.snd = ν) :
    ENNReal.ofReal (boltzmannEntropy μ (heatMeasure μ hQ t f)-boltzmannEntropy μ ν) ≤
      ENNReal.ofReal (Real.sqrt (fisherInformation μ hQ f t).toReal)*
        (transportCost π)^(1/(2:ℝ))+
      ENNReal.ofReal (|K|/2)*transportCost π := by
  have hfi := lp_integrable_of_bounded_support μ f p hfS
  have hU0 := (Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ t f hf0)
  have hUi := heatAt_integrable_of_nonneg μ hQ t f hf0 hfi
  let hm := integrable_sqrt_memLp μ hUi hU0
  let v := hm.toLp (fun x => Real.sqrt (heatAt μ hQ t f x))
  have hv : ⇑v =ᵐ[μ] fun x => Real.sqrt (heatAt μ hQ t f x) := hm.coeFn_toLp
  have hvsq : (fun x => v x^2) =ᵐ[μ] fun x => heatAt μ hQ t f x := by
    filter_upwards [hv,hU0] with x hx hn
    rw [hx,Real.sq_sqrt hn]
  have hE := heat_fisher_eq_eight_sqrt_energy μ hQ f hf0 hfi C.coe_nonneg hfC ht
  change fisherInformation μ hQ f t = 8*energyLp μ v at hE
  have hvfin : energyLp μ v ≠ ∞ := by
    intro hz
    rw [hE,hz] at hI
    norm_num at hI
  let V : SobolevSpace μ hQ := ⟨v,hvfin⟩
  let G := SobolevSpace.minimalSlope μ hQ V
  have hG : IsRelaxedSlope μ v G := SobolevSpace.minimalSlope_isRelaxed μ hQ V
  have hvM : ‖v‖ = 1 := by
    have he : ‖v‖^2 = 1 := by
      rw [← integral_sq_Lp]
      rw [integral_congr_ae hvsq,heatAt_integral_eq_of_exponential_volume μ hQ p hA hB hvol f hf0 hfi ht.le,hfM]
    nlinarith [norm_nonneg v]
  have hvB : ∀ᵐx ∂μ, 0 ≤ v x ∧ v x ≤ (⟨Real.sqrt C,Real.sqrt_nonneg _⟩:ℝ≥0) := by
    filter_upwards [hv,heatAt_le_const μ hQ t C.coe_nonneg f hfC] with x hx hc
    rw [hx]
    exact ⟨Real.sqrt_nonneg _,Real.sqrt_le_sqrt hc⟩
  have hvE : Integrable (fun x => v x^2*Real.log (v x^2)) μ := by
    apply (heatAt_entropy_integrable μ hQ p hA hB hvol f hf0 hfS ht.le).congr
    filter_upwards [hvsq] with x hx
    rw [hx]
  have hρ : μ.withDensity (fun x => ENNReal.ofReal (v x^2)) = heatMeasure μ hQ t f := by
    apply withDensity_congr_ae
    exact hvsq.mono fun x hx => congrArg ENNReal.ofReal hx
  have hvDist : Integrable (fun x => dist p x^2) (μ.withDensity (fun x => ENNReal.ofReal (v x^2))) := by
    rw [hρ]
    exact heatMeasure_dist_sq_integrable μ hQ p hA hB hvol f hf0 hfS ht.le
  have hEnt : (∫x, v x^2*Real.log (v x^2) ∂μ) = boltzmannEntropy μ (heatMeasure μ hQ t f) := by
    apply integral_congr_ae
    filter_upwards [hvsq,heatMeasure_rnDeriv μ hQ t f hf0] with x hx he
    rw [hx,he]
  have hnorm : 2*‖G‖ = Real.sqrt (fisherInformation μ hQ f t).toReal := by
    have hn := SobolevSpace.minimalSlope_norm_sq μ hQ V
    change ‖G‖^2 = 2*(energyLp μ v).toReal at hn
    have hi : (fisherInformation μ hQ f t).toReal = 8*(energyLp μ v).toReal := by
      rw [hE,ENNReal.toReal_mul]
      norm_num
    have he : (fisherInformation μ hQ f t).toReal = (2*‖G‖)^2 := by nlinarith
    rw [he,Real.sqrt_sq (by positivity : 0 ≤ 2*‖G‖)]
  have hh := hcd.bounded_sobolev_HWI μ K n p hA hB hvol v G hG hvM
    ⟨Real.sqrt C,Real.sqrt_nonneg _⟩ hvB hvE hvDist ν hν hνE hνExp hνDist π
    (hπ₀.trans hρ.symm) hπ₁
  rw [hEnt,hnorm] at hh
  exact hh
end

 
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
 

noncomputable def wassersteinSq (ν₀ ν₁ : Measure X) : ℝ≥0∞ :=
  sInf {c | ∃ π : Measure (X×X), π.map Prod.fst = ν₀ ∧
    π.map Prod.snd = ν₁ ∧ transportCost π = c}
 theorem wassersteinSq_le_cost {ν₀ ν₁ : Measure X} {π : Measure (X×X)}
    (h0 : π.map Prod.fst = ν₀) (h1 : π.map Prod.snd = ν₁) :
    wassersteinSq ν₀ ν₁ ≤ transportCost π :=
  sInf_le ⟨π,h0,h1,rfl⟩
 theorem wassersteinSq_eq_cost {ν₀ ν₁ : Measure X} {π : Measure (X×X)}
    (hπ : IsOptimalCoupling ν₀ ν₁ π) : wassersteinSq ν₀ ν₁ = transportCost π := by
  apply le_antisymm (wassersteinSq_le_cost hπ.1 hπ.2.1)
  apply le_sInf
  rintro c ⟨κ,h0,h1,rfl⟩
  exact hπ.2.2 κ h0 h1
 theorem wassersteinSq_ne_top {ν₀ ν₁ : Measure X} {π : Measure (X×X)}
    (h0 : π.map Prod.fst = ν₀) (h1 : π.map Prod.snd = ν₁)
    (hπ : transportCost π ≠ ∞) : wassersteinSq ν₀ ν₁ ≠ ∞ :=
  ne_top_of_le_ne_top hπ (wassersteinSq_le_cost h0 h1)
end

 
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

 theorem regularizedFisher_aemeasurable_Ioc {ε : ℝ} (hε : 0 < ε) (f : Lp ℝ 2 μ)
    {a b : ℝ} (ha : 0 ≤ a) :
    AEMeasurable (fun s => ENNReal.ofReal (regularizedFisher μ hQ hε f s))
      (volume.restrict (Ioc a b)) := by
  apply ContinuousOn.aemeasurable _ measurableSet_Ioc
  apply ContinuousOn.comp ENNReal.continuous_ofReal.continuousOn
    ((heatDissipation_continuousOn μ hQ (regularizedLog_lipschitz hε)
      (regularizedLog_zero ε) f).mono (fun s hs => ha.trans_lt hs.1))
  exact fun _ _ => mem_univ _

 theorem heatAt_regularizedFisher_lintegral_zero {ε : ℝ} (hε : 0 < ε)
    (f : Lp ℝ 2 μ) {b : ℝ} (hb : 0 ≤ b) :
    (∫⁻ s in Ioc 0 b, ENNReal.ofReal (regularizedFisher μ hQ hε f s)) =
      ENNReal.ofReal (integralPotential μ (regularizedEntropy ε) f -
        integralPotential μ (regularizedEntropy ε) (heatAt μ hQ b f)) := by
  rcases eq_or_lt_of_le hb with rfl | hb
  · simp [heatAt_zero]
  let a : ℕ → ℝ := fun k => b*entropyScale k
  have ha (k : ℕ) : 0 < a k := mul_pos hb (entropyScale_pos k)
  have hab (k : ℕ) : a k ≤ b := by
    have hs := entropyScale_antitone (Nat.zero_le k)
    have hs0 : entropyScale 0 = 1 := by norm_num [entropyScale]
    dsimp only [a]
    rw [hs0] at hs
    nlinarith
  have hm : Antitone a := fun i j hij => mul_le_mul_of_nonneg_left
    (entropyScale_antitone hij) hb.le
  have hz : Tendsto a atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (entropyScale_tendsto.mono_right nhdsWithin_le_nhds).const_mul b
  have hsets : Monotone (fun k => Ioc (a k) b) := fun i j hij x hx =>
    ⟨(hm hij).trans_lt hx.1,hx.2⟩
  have hu : (⋃ k, Ioc (a k) b) = Ioc 0 b := by
    ext x
    constructor
    · intro hx
      obtain ⟨k,hk⟩ := mem_iUnion.mp hx
      exact ⟨(ha k).trans hk.1,hk.2⟩
    · intro hx
      obtain ⟨k,hk⟩ := ((tendsto_order.mp hz).2 x hx.1).exists
      exact mem_iUnion.mpr ⟨k,hk,hx.2⟩
  have hi : Monotone (fun k => ∫⁻ s in Ioc (a k) b,
      ENNReal.ofReal (regularizedFisher μ hQ hε f s)) := fun i j hij =>
        lintegral_mono_set (hsets hij)
  have ht := tendsto_atTop_iSup hi
  rw [← setLIntegral_iUnion_of_directed _ hsets.directed_le,hu] at ht
  have heq (k : ℕ) : (∫⁻ s in Ioc (a k) b, ENNReal.ofReal (regularizedFisher μ hQ hε f s)) =
      ENNReal.ofReal (integralPotential μ (regularizedEntropy ε) (heatAt μ hQ (a k) f) -
        integralPotential μ (regularizedEntropy ε) (heatAt μ hQ b f)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (regularizedFisher_intervalIntegrable μ hQ hε f (ha k) (hab k)).1
      (show ∀ᵐ s ∂volume.restrict (Ioc (a k) b), 0 ≤ regularizedFisher μ hQ hε f s from by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact regularizedFisher_nonneg μ hQ hε f s ((ha k).trans hs.1)),
      ← intervalIntegral.integral_of_le (hab k),
      heatAt_regularizedEntropy_dissipation μ hQ hε f (a k) b (ha k) (hab k)]
  simp_rw [heq] at ht
  have hp := (integralPotential_continuous μ (regularizedEntropy_hasDerivAt ε)
    (regularizedEntropy_zero ε) (regularizedLog_lipschitz hε) (regularizedLog_zero ε)).tendsto
      (heatAt μ hQ 0 f)
  have hf := hp.comp ((heatAt_continuous μ hQ f).tendsto 0 |>.comp hz)
  rw [heatAt_zero μ hQ] at hf
  exact tendsto_nhds_unique ht (ENNReal.tendsto_ofReal (hf.sub_const _))

 theorem heatAt_entropy_dissipation_zero_of_finite (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f)
    {b : ℝ} (hb : 0 ≤ b) (hfi : Integrable f μ) (hBi : Integrable (heatAt μ hQ b f) μ)
    (hfe : Integrable (fun x => f x*Real.log (f x)) μ)
    (hBe : Integrable (fun x => heatAt μ hQ b f x*Real.log (heatAt μ hQ b f x)) μ)
    (hm : (∫ x, f x ∂μ) = ∫ x, heatAt μ hQ b f x ∂μ) :
    (∫⁻ s in Ioc 0 b, fisherInformation μ hQ f s) = ENNReal.ofReal
      ((∫ x, f x*Real.log (f x) ∂μ)-
        ∫ x, heatAt μ hQ b f x*Real.log (heatAt μ hQ b f x) ∂μ) := by
  have he := (integral_normalizedEntropy_sub_tendsto μ f (heatAt μ hQ b f)
    hf0 (heatAt_nonneg μ hQ b f hf0) hfi hBi hfe hBe hm).comp entropyScale_tendsto
  have hmct := lintegral_tendsto_of_tendsto_of_monotone
    (μ := volume.restrict (Ioc 0 b))
    (fun k => regularizedFisher_aemeasurable_Ioc μ hQ (entropyScale_pos k) f le_rfl)
    (show ∀ᵐ s ∂volume.restrict (Ioc 0 b), Monotone
      (fun k => ENNReal.ofReal (regularizedFisher μ hQ (entropyScale_pos k) f s)) from by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact fun i j hij => ENNReal.ofReal_le_ofReal
        (regularizedFisher_monotone μ hQ f hs.1 hij))
    (show ∀ᵐ s ∂volume.restrict (Ioc 0 b), Tendsto
      (fun k => ENNReal.ofReal (regularizedFisher μ hQ (entropyScale_pos k) f s)) atTop
        (𝓝 (fisherInformation μ hQ f s)) from by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact tendsto_atTop_iSup (fun i j hij => ENNReal.ofReal_le_ofReal
        (regularizedFisher_monotone μ hQ f hs.1 hij)))
  simp_rw [heatAt_regularizedFisher_lintegral_zero μ hQ _ f hb] at hmct
  exact tendsto_nhds_unique hmct (ENNReal.tendsto_ofReal he)

 theorem heatAt_entropy_dissipation_nonneg_of_finite (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hAi : Integrable (heatAt μ hQ a f) μ) (hBi : Integrable (heatAt μ hQ b f) μ)
    (hAe : Integrable (fun x => heatAt μ hQ a f x*Real.log (heatAt μ hQ a f x)) μ)
    (hBe : Integrable (fun x => heatAt μ hQ b f x*Real.log (heatAt μ hQ b f x)) μ)
    (hm : (∫ x, heatAt μ hQ a f x ∂μ) = ∫ x, heatAt μ hQ b f x ∂μ) :
    (∫⁻ s in Ioc a b, fisherInformation μ hQ f s) = ENNReal.ofReal
      ((∫ x, heatAt μ hQ a f x*Real.log (heatAt μ hQ a f x) ∂μ)-
        ∫ x, heatAt μ hQ b f x*Real.log (heatAt μ hQ b f x) ∂μ) := by
  rcases eq_or_lt_of_le ha with rfl | ha
  · simp only [heatAt_zero] at hAi hAe hm ⊢
    exact heatAt_entropy_dissipation_zero_of_finite μ hQ f hf0 hab hAi hBi hAe hBe hm
  · exact heatAt_entropy_dissipation_of_finite μ hQ f hf0 ha hab hAi hBi hAe hBe hm

 theorem heatAt_entropy_dissipation_nonneg (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (Metric.closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) (hfi : Integrable f μ) {r : ℝ}
    (hf : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫⁻ s in Ioc a b, fisherInformation μ hQ f s) = ENNReal.ofReal
      ((∫ x, heatAt μ hQ a f x*Real.log (heatAt μ hQ a f x) ∂μ)-
        ∫ x, heatAt μ hQ b f x*Real.log (heatAt μ hQ b f x) ∂μ) := by
  apply heatAt_entropy_dissipation_nonneg_of_finite μ hQ f hf0 ha hab
    (heatAt_integrable_of_nonneg μ hQ a f hf0 hfi) (heatAt_integrable_of_nonneg μ hQ b f hf0 hfi)
    (heatAt_entropy_integrable μ hQ p hA hB hvol f hf0 hf ha)
    (heatAt_entropy_integrable μ hQ p hA hB hvol f hf0 hf (ha.trans hab))
  rw [heatAt_integral_eq_of_exponential_volume μ hQ p hA hB hvol f hf0 hfi ha,
    heatAt_integral_eq_of_exponential_volume μ hQ p hA hB hvol f hf0 hfi (ha.trans hab)]

end

 
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

 theorem fisherInformation_aemeasurable_nonneg (f : Lp ℝ 2 μ) {a b : ℝ} (ha : 0 ≤ a) :
    AEMeasurable (fisherInformation μ hQ f) (volume.restrict (Ioc a b)) :=
  AEMeasurable.iSup fun k => regularizedFisher_aemeasurable_Ioc μ hQ (entropyScale_pos k) f ha

 theorem heatAt_fisher_time_finite_nonneg (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) (hfi : Integrable f μ) {r : ℝ}
    (hf : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫⁻ s in Ioc a b, fisherInformation μ hQ f s) < ∞ := by
  rw [heatAt_entropy_dissipation_nonneg μ hQ p hA hB hvol f hf0 hfi hf ha hab]
  exact ENNReal.ofReal_lt_top

 theorem heatAt_fisher_intervalIntegrable_nonneg (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) (hfi : Integrable f μ) {r : ℝ}
    (hf : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun s => (fisherInformation μ hQ f s).toReal) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
  exact integrable_toReal_of_lintegral_ne_top (fisherInformation_aemeasurable_nonneg μ hQ f ha)
    (heatAt_fisher_time_finite_nonneg μ hQ p hA hB hvol f hf0 hfi hf ha hab).ne

 theorem heatAt_fisher_integral_entropy_nonneg (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) (hfi : Integrable f μ) {r : ℝ}
    (hf : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫s in a..b, (fisherInformation μ hQ f s).toReal) =
      (∫x, heatAt μ hQ a f x*Real.log (heatAt μ hQ a f x) ∂μ)-
        ∫x, heatAt μ hQ b f x*Real.log (heatAt μ hQ b f x) ∂μ := by
  have hm := fisherInformation_aemeasurable_nonneg μ hQ f (b := b) ha
  have hfin := heatAt_fisher_time_finite_nonneg μ hQ p hA hB hvol f hf0 hfi hf ha hab
  rw [intervalIntegral.integral_of_le hab,integral_toReal hm (ae_lt_top' hm hfin.ne),
    heatAt_entropy_dissipation_nonneg μ hQ p hA hB hvol f hf0 hfi hf ha hab,ENNReal.toReal_ofReal]
  apply sub_nonneg.mpr
  apply heatAt_entropy_mono_of_finite μ hQ f hf0 ha hab
    (heatAt_integrable_of_nonneg μ hQ a f hf0 hfi)
    (heatAt_integrable_of_nonneg μ hQ b f hf0 hfi)
    (heatAt_entropy_integrable μ hQ p hA hB hvol f hf0 hf ha)
    (heatAt_entropy_integrable μ hQ p hA hB hvol f hf0 hf (ha.trans hab))
  rw [heatAt_integral_eq_of_exponential_volume μ hQ p hA hB hvol f hf0 hfi ha,
    heatAt_integral_eq_of_exponential_volume μ hQ p hA hB hvol f hf0 hfi (ha.trans hab)]

 theorem heatAt_entropy_ae_hasDerivAt_nonneg (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) (hfi : Integrable f μ) {r : ℝ}
    (hf : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ᵐ s : ℝ, s ∈ Ioo a b → HasDerivAt
      (fun t => ∫x, heatAt μ hQ t f x*Real.log (heatAt μ hQ t f x) ∂μ)
      (-(fisherInformation μ hQ f s).toReal) s := by
  have hI := heatAt_fisher_intervalIntegrable_nonneg μ hQ p hA hB hvol f hf0 hfi hf ha hab
  filter_upwards [hI.ae_hasDerivAt_integral] with s hs
  intro hsa
  have ht := (hs (by simpa [uIcc_of_le hab] using ⟨hsa.1.le,hsa.2.le⟩)
    a left_mem_uIcc).const_sub
      (∫x, heatAt μ hQ a f x*Real.log (heatAt μ hQ a f x) ∂μ)
  apply ht.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hsa.1 hsa.2] with t ht
  have he := heatAt_fisher_integral_entropy_nonneg μ hQ p hA hB hvol f hf0 hfi hf ha ht.1.le
  linarith

 theorem heatAt_entropy_absolutelyContinuous_nonneg (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) (hfi : Integrable f μ) {r : ℝ}
    (hf : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval
      (fun t => ∫x, heatAt μ hQ t f x*Real.log (heatAt μ hQ t f x) ∂μ) a b := by
  have hI := heatAt_fisher_intervalIntegrable_nonneg μ hQ p hA hB hvol f hf0 hfi hf ha hab
  have hD := hI.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ =>
      ∫x, heatAt μ hQ a f x*Real.log (heatAt μ hQ a f x) ∂μ) a b :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  apply absolutelyContinuousOnInterval_congr (hc.sub hD)
  intro t ht
  rw [uIcc_of_le hab] at ht
  have he := heatAt_fisher_integral_entropy_nonneg μ hQ p hA hB hvol f hf0 hfi hf ha ht.1
  simp only [Pi.sub_apply]
  linarith


end RegularPointCoordinates

end OAI
