import Mathlib
import OAI.Analysis.RCDHeat.EntropyPlanExtension

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: EVIConvexity, StrongEntropySegment, DensityEntropyBounds, StrongEntropyPlan. -/



namespace RegularPointCoordinates

section

 

open Set Filter MeasureTheory
open scoped Topology

theorem nonneg_of_boundary_min_integrated_bound
    {D G : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hD : ContinuousWithinAt D (Icc 0 T) 0)
    (hG : ContinuousOn G (Icc 0 T))
    (hmin : ∀ b ∈ Ioc 0 T, D 0 ≤ D b)
    (hI : ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ T →
      D b-D a ≤ ∫ t in a..b, G t) : 0 ≤ G 0 := by
  by_contra hn
  have hn : G 0 < 0 := lt_of_not_ge hn
  have hDc : ContinuousWithinAt D (Ioi 0) 0 :=
    (hD.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hT)).mono Ioi_subset_Ici_self
  have hGc : ContinuousWithinAt G (Ici 0) 0 :=
    (hG 0 ⟨le_rfl,hT.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hT)
  have hev : ∀ᶠ t in 𝓝[≥] (0:ℝ), G t < G 0/2 ∧ t ∈ Icc 0 T :=
    (hGc.tendsto.eventually (Iio_mem_nhds (by linarith))).and (Icc_mem_nhdsGE hT)
  obtain ⟨b,hb,hbound⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp hev
  have hbT : b ≤ T := (hbound ⟨hb.le,le_rfl⟩).2.2
  have he : ∀ᶠ a in 𝓝[>] (0:ℝ), D b-D a ≤ (b-a)*(G 0/2) := by
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds hb)] with a ha hab
    have hab : a ≤ b := le_of_lt hab
    have hgi : IntervalIntegrable G volume a b := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hab]
      exact hG.mono (fun t ht => ⟨ha.le.trans ht.1,ht.2.trans hbT⟩)
    have hle := intervalIntegral.integral_mono_on hab hgi
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => G 0/2) volume a b)
      (fun t ht => (hbound ⟨ha.le.trans ht.1,ht.2⟩).1.le)
    simp only [intervalIntegral.integral_const,smul_eq_mul] at hle
    exact (hI a b ha hab hbT).trans hle
  have hl := le_of_tendsto_of_tendsto
    (tendsto_const_nhds.sub hDc.tendsto)
    ((tendsto_const_nhds.sub (show Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) from
      nhdsWithin_le_nhds)).mul_const (G 0/2)) he
  simp only [sub_zero] at hl
  have hm := hmin b ⟨hb,hbT⟩
  nlinarith

 

theorem weighted_dist_sq_lower {Y : Type*} [PseudoMetricSpace Y]
    (x y z : Y) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    s*(1-s)*dist x y^2 ≤ (1-s)*dist z x^2+s*dist z y^2 := by
  have hd := dist_triangle x z y
  rw [dist_comm x z] at hd
  have hp : dist x y^2 ≤ (dist z x+dist z y)^2 :=
    pow_le_pow_left₀ dist_nonneg hd 2
  have hh := mul_le_mul_of_nonneg_left hp (mul_nonneg hs (sub_nonneg.mpr hs1))
  nlinarith [sq_nonneg ((1-s)*dist z x-s*dist z y)]

 

theorem metric_segment_convexity_of_integrated_evi
    {Y : Type*} [MetricSpace Y] (x y : Y) (c : ℝ → Y) (E : ℝ → ℝ)
    {s K ex ey T : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hT : 0 < T)
    (hc : ContinuousOn c (Icc 0 T)) (hE : ContinuousOn E (Icc 0 T))
    (hx : dist (c 0) x = s*dist x y) (hy : dist (c 0) y = (1-s)*dist x y)
    (hvi : ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ T →
      (dist (c b) x^2-dist (c a) x^2)/2 ≤
        ∫ t in a..b, ex-E t-(K/2)*dist (c t) x^2)
    (hvj : ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ T →
      (dist (c b) y^2-dist (c a) y^2)/2 ≤
        ∫ t in a..b, ey-E t-(K/2)*dist (c t) y^2) :
    E 0 ≤ (1-s)*ex+s*ey-(K/2)*s*(1-s)*dist x y^2 := by
  let D : ℝ → ℝ := fun t => ((1-s)*dist (c t) x^2+s*dist (c t) y^2)/2
  let G : ℝ → ℝ := fun t => (1-s)*ex+s*ey-E t-K*D t
  have hDc : ContinuousOn D (Icc 0 T) :=
    (((continuous_dist.comp_continuousOn (hc.prodMk continuousOn_const)).pow 2).const_mul (1-s) |>.add
      (((continuous_dist.comp_continuousOn (hc.prodMk continuousOn_const)).pow 2).const_mul s)).div_const 2
  have hGc : ContinuousOn G (Icc 0 T) :=
    (continuousOn_const.sub hE).sub (hDc.const_mul K)
  have hd0 : D 0 = s*(1-s)*dist x y^2/2 := by dsimp [D]; rw [hx,hy]; ring
  have hm : ∀ b ∈ Ioc 0 T, D 0 ≤ D b := by
    intro b _
    rw [hd0]
    exact (div_le_div_iff_of_pos_right (by norm_num : (0:ℝ)<2)).mpr
      (weighted_dist_sq_lower x y (c b) hs hs1)
  have hi : ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ T →
      D b-D a ≤ ∫ t in a..b, G t := by
    intro a b ha hab hb
    have hsub : Icc a b ⊆ Icc 0 T := fun t ht => ⟨ha.le.trans ht.1,ht.2.trans hb⟩
    have hxi : IntervalIntegrable (fun t => ex-E t-(K/2)*dist (c t) x^2) volume a b := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hab]
      exact ((continuousOn_const.sub hE).sub (((continuous_dist.comp_continuousOn (hc.prodMk continuousOn_const)).pow 2).const_mul (K/2))).mono hsub
    have hyi : IntervalIntegrable (fun t => ey-E t-(K/2)*dist (c t) y^2) volume a b := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hab]
      exact ((continuousOn_const.sub hE).sub (((continuous_dist.comp_continuousOn (hc.prodMk continuousOn_const)).pow 2).const_mul (K/2))).mono hsub
    have he : (∫ t in a..b, G t) =
        (1-s)*(∫ t in a..b, ex-E t-(K/2)*dist (c t) x^2)+
        s*(∫ t in a..b, ey-E t-(K/2)*dist (c t) y^2) := by
      rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add (hxi.const_mul (1-s)) (hyi.const_mul s)]
      congr 1
      funext t
      dsimp [G,D]
      ring
    rw [he]
    have hxv := mul_le_mul_of_nonneg_left (hvi a b ha hab hb) (sub_nonneg.mpr hs1)
    have hyv := mul_le_mul_of_nonneg_left (hvj a b ha hab hb) hs
    dsimp [D]
    linarith only [hxv,hyv]
  have hn := nonneg_of_boundary_min_integrated_bound hT (hDc 0 ⟨le_rfl,hT.le⟩) hGc hm hi
  dsimp only [G] at hn
  rw [hd0] at hn
  linarith

end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.entropy_convexity_bounded_segment
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ ν : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure ν] (C : ℝ≥0)
    (h0 : ν₀ ≤ ENNReal.ofReal C • hausdorff n X)
    (h1 : ν₁ ≤ ENNReal.ofReal C • hausdorff n X)
    (hm : ν ≤ ENNReal.ofReal C • hausdorff n X)
    (p : X) (R : ℝ)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (hsm : ∀ᵐ x ∂ν, dist x p ≤ R) (s : Time)
    (hd0 : wassersteinEDist ν ν₀ = ENNReal.ofReal (s:ℝ) * wassersteinEDist ν₀ ν₁)
    (hd1 : wassersteinEDist ν ν₁ = ENNReal.ofReal (1-(s:ℝ)) * wassersteinEDist ν₀ ν₁) :
    boltzmannEntropy (hausdorff n X) ν ≤
      (1-(s:ℝ))*boltzmannEntropy (hausdorff n X) ν₀+
      (s:ℝ)*boltzmannEntropy (hausdorff n X) ν₁-
      (K/2)*(s:ℝ)*(1-(s:ℝ))*(wassersteinSq ν₀ ν₁).toReal := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let := ACWassersteinProbability.metric μ K n hX.cd
  have hac0 : ν₀ ≪ μ := Measure.absolutelyContinuous_of_le_smul h0
  have hac1 : ν₁ ≪ μ := Measure.absolutelyContinuous_of_le_smul h1
  have hacm : ν ≪ μ := Measure.absolutelyContinuous_of_le_smul hm
  let v0 : ACWassersteinProbability μ := ⟨ν₀,inferInstance,hac0,finiteSecondMoment_of_ae_dist_le ν₀ p hs0⟩
  let v1 : ACWassersteinProbability μ := ⟨ν₁,inferInstance,hac1,finiteSecondMoment_of_ae_dist_le ν₁ p hs1⟩
  obtain ⟨f,hf0,hfC,hfm,hfs,hfe⟩ := bounded_density_lp_realization μ ν C.coe_nonneg hm
    measurableSet_closedBall (isCompact_closedBall p R).measure_lt_top.ne hsm
  have hfs' : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ R := by
    simpa only [mem_closedBall,dist_comm] using hfs
  let c := hX.heatProbability K n hn p f hf0 ⟨R,hfs'⟩ hfm
  let E : ℝ → ℝ := fun t => boltzmannEntropy μ (heatMeasure μ hX.quadratic t f)
  have hfabs : ∀ᵐ x ∂μ, |f x| ≤ C := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr hf0,hfC] with x hx hy
    simpa only [abs_of_nonneg hx] using hy
  have hc : ContinuousOn c (Icc 0 1) := by
    have h := metricAC_uniformContinuousOn
      (hX.heat_probability_absolutelyContinuous K n hn p f hf0 ⟨R,hfs'⟩ hfm C hfabs 1 zero_le_one)
    simpa only [uIcc_of_le zero_le_one] using h.continuousOn
  have hEc : ContinuousOn E (Icc 0 1) := by
    obtain ⟨A,B,hA,hB,hvol⟩ := hX.exponential_volume K n hn p
    have hfi := lp_integrable_of_bounded_support μ f p hfs'
    have h := heatAt_entropy_absolutelyContinuous_nonneg μ hX.quadratic p hA hB hvol
      f hf0 hfi hfs' (a := 0) (b := 1) le_rfl zero_le_one
    simpa only [E,uIcc_of_le zero_le_one,boltzmannEntropy_heatMeasure_eq μ hX.quadratic f hf0]
      using h.continuousOn
  have hc0 : (c 0).val = ν := by
    dsimp only [c,NoncollapsedRCD.heatProbability]
    simpa only [max_self,heatMeasure,heatAt_zero,one_apply_eq_self] using hfe
  have he0 : E 0 = boltzmannEntropy μ ν := by
    dsimp only [E]
    have hh : heatMeasure μ hX.quadratic 0 f = ν := by
      simpa only [heatMeasure,heatAt_zero,one_apply_eq_self] using hfe
    rw [hh]
  have hdx : dist (c 0) v0 = (s:ℝ)*dist v0 v1 := by
    change (wassersteinEDist (c 0).val ν₀).toReal =
      (s:ℝ)*(wassersteinEDist ν₀ ν₁).toReal
    rw [hc0,hd0,ENNReal.toReal_mul,ENNReal.toReal_ofReal s.2.1]
  have hdy : dist (c 0) v1 = (1-(s:ℝ))*dist v0 v1 := by
    change (wassersteinEDist (c 0).val ν₁).toReal =
      (1-(s:ℝ))*(wassersteinEDist ν₀ ν₁).toReal
    rw [hc0,hd1,ENNReal.toReal_mul,ENNReal.toReal_ofReal (sub_nonneg.mpr s.2.2)]
  have hd (v : ACWassersteinProbability μ) {t : ℝ} (ht : 0 ≤ t) :
      dist (c t) v^2 = (wassersteinSq (heatMeasure μ hX.quadratic t f) v.val).toReal := by
    change (wassersteinEDist (c t).val v.val).toReal^2 = _
    dsimp only [c,NoncollapsedRCD.heatProbability]
    rw [max_eq_left ht,wassersteinEDist,←ENNReal.toReal_rpow,←Real.sqrt_eq_rpow,
      Real.sq_sqrt ENNReal.toReal_nonneg]
  have hvi (v : ACWassersteinProbability μ) (hv : v.val ≤ ENNReal.ofReal C • μ)
      (hvs : ∀ᵐ x ∂v.val, dist x p ≤ R)
      (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (_ : b ≤ 1) :
      (dist (c b) v^2-dist (c a) v^2)/2 ≤
        ∫ t in a..b, boltzmannEntropy μ v.val-E t-(K/2)*dist (c t) v^2 := by
    rw [hd v (ha.le.trans hab),hd v ha.le]
    convert hX.bounded_heat_EVI K n hn p f C hf0 hfC hfm hfs' v.val hv hvs ha hab using 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    change boltzmannEntropy μ v.val-E t-(K/2)*dist (c t) v^2 = _
    rw [hd v (ha.le.trans ht.1)]
  have hh := metric_segment_convexity_of_integrated_evi v0 v1 c E s.2.1 s.2.2
    (by norm_num : (0:ℝ)<1) hc hEc hdx hdy (hvi v0 h0 hs0) (hvi v1 h1 hs1)
  rw [he0] at hh
  have hd01 : dist v0 v1^2 = (wassersteinSq ν₀ ν₁).toReal := by
    change (wassersteinEDist ν₀ ν₁).toReal^2 = _
    rw [wassersteinEDist,←ENNReal.toReal_rpow,←Real.sqrt_eq_rpow,
      Real.sq_sqrt ENNReal.toReal_nonneg]
  rwa [hd01] at hh

end

 
section

 

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
theorem entropy_le_log_density_bound (μ ν : Measure X) [SigmaFinite μ]
    [IsProbabilityMeasure ν] {C : ℝ} (hC : 0 < C)
    (hν : ν ≤ ENNReal.ofReal C • μ) {S : Set X} (hS : MeasurableSet S)
    [IsFiniteMeasure (μ.restrict S)] (hs : ∀ᵐ x ∂ν, x ∈ S) :
    boltzmannEntropy μ ν ≤ Real.log C := by
  have hac : ν ≪ μ := Measure.absolutelyContinuous_of_le_smul hν
  have hEnt := entropy_integrable_of_bounded_support μ ν ENNReal.ofReal_ne_top hν hS hs
  have hlog := (integrable_toReal_rnDeriv_mul_iff hac).mp hEnt
  have hbound : ∀ᵐ x ∂ν, Real.log (ν.rnDeriv μ x).toReal ≤ Real.log C := by
    filter_upwards [hac.ae_le (rnDeriv_le_const_of_le_smul μ ν hν),
      hac.ae_le (Measure.rnDeriv_lt_top ν μ),Measure.rnDeriv_pos hac] with x hx hxt hx0
    apply Real.log_le_log (ENNReal.toReal_pos hx0.ne' hxt.ne)
    exact ((ENNReal.toReal_le_toReal hxt.ne ENNReal.ofReal_ne_top).mpr hx).trans_eq
      (ENNReal.toReal_ofReal hC.le)
  have hb := integral_mono_ae hlog (integrable_const (Real.log C)) hbound
  have he : (∫x, Real.log (ν.rnDeriv μ x).toReal ∂ν) = boltzmannEntropy μ ν :=
    (integral_rnDeriv_smul (f := fun x => Real.log (ν.rnDeriv μ x).toReal) hac).symm
  simpa only [he,integral_const,probReal_univ,one_smul] using hb

omit [MetricSpace X] [BorelSpace X] in
theorem log_density_floor_lt_entropy (μ ν : Measure X) [SigmaFinite μ]
    [IsProbabilityMeasure ν] (hac : ν ≪ μ)
    (hEnt : Integrable (fun x => (ν.rnDeriv μ x).toReal*Real.log (ν.rnDeriv μ x).toReal) μ)
    {D : ℝ} (hD : 0 < D) (hfloor : ∀ᵐ x ∂ν, D < (ν.rnDeriv μ x).toReal) :
    Real.log D < boltzmannEntropy μ ν := by
  have hlog := (integrable_toReal_rnDeriv_mul_iff hac).mp hEnt
  have hlt : ∀ᵐ x ∂ν, Real.log D < Real.log (ν.rnDeriv μ x).toReal :=
    hfloor.mono fun _ hx => Real.log_lt_log hD hx
  have hle := integral_mono_ae (integrable_const (Real.log D)) hlog (hlt.mono fun _ hx => hx.le)
  have he : (∫x, Real.log (ν.rnDeriv μ x).toReal ∂ν) = boltzmannEntropy μ ν :=
    (integral_rnDeriv_smul (f := fun x => Real.log (ν.rnDeriv μ x).toReal) hac).symm
  have hconst : (∫_ : X, Real.log D ∂ν) = Real.log D := by simp
  apply lt_of_le_of_ne (by simpa only [he,hconst] using hle)
  intro heq
  have ha : (fun _ : X => Real.log D) =ᵐ[ν] (fun x => Real.log (ν.rnDeriv μ x).toReal) :=
    (integral_eq_iff_of_ae_le (integrable_const _) hlog (hlt.mono fun _ hx => hx.le)).mp (by rwa [he,hconst])
  obtain ⟨x,hx,hxe⟩ := (hlt.and ha).exists
  exact hx.ne hxe

end

 

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.entropy_convexity_bounded_plan_marginal
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (C : ℝ≥0) (h0 : ν₀ ≤ ENNReal.ofReal C • hausdorff n X)
    (h1 : ν₁ ≤ ENNReal.ofReal C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (plan : Measure C(Time,X)) [IsProbabilityMeasure plan]
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (plan.map (fun γ => (γ 0,γ 1))))
    (s : Time) (hm : plan.map (fun γ => γ s) ≤ ENNReal.ofReal C • hausdorff n X) :
    boltzmannEntropy (hausdorff n X) (plan.map (fun γ => γ s)) ≤
      (1-(s:ℝ))*boltzmannEntropy (hausdorff n X) ν₀+
      (s:ℝ)*boltzmannEntropy (hausdorff n X) ν₁-
      (K/2)*(s:ℝ)*(1-(s:ℝ))*(wassersteinSq ν₀ ν₁).toReal := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let : Nonempty X := ⟨p⟩
  let : IsProbabilityMeasure (plan.map (fun γ => γ s)) :=
    inferInstance
  have hend := optimalPlan_endpoints ν₀ ν₁ plan hp
  have hp' : IsOptimalCoupling (plan.map (fun γ => γ 0)) (plan.map (fun γ => γ 1))
      (plan.map (fun γ => (γ 0,γ 1))) := by rwa [hend.1,hend.2]
  have hc : transportCost (plan.map (fun γ => (γ 0,γ 1))) ≠ ∞ := by
    rw [← wassersteinSq_eq_cost hp]
    exact wassersteinSq_finite (finiteSecondMoment_of_ae_dist_le ν₀ p hs0)
      (finiteSecondMoment_of_ae_dist_le ν₁ p hs1)
  have hd0 := wassersteinEDist_geodesic_plan plan hg hp' hc s 0
  have hd1 := wassersteinEDist_geodesic_plan plan hg hp' hc s 1
  have ht0 : ((0 : Time) : ℝ) = 0 := rfl
  have ht1 : ((1 : Time) : ℝ) = 1 := rfl
  simp only [hend.1,hend.2,ht0,sub_zero,abs_of_nonneg s.2.1] at hd0
  simp only [hend.1,hend.2,ht1,abs_sub_comm (s:ℝ),
    abs_of_nonneg (sub_nonneg.mpr s.2.2)] at hd1
  have hsupport : ∀ᵐ x ∂plan.map (fun γ => γ s), dist x p ≤ 3*R := by
    apply (ae_map_iff (measurable_path_eval s).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded _ _ plan hg hp p hR hs0 hs1).mono fun γ hγ => hγ.2 s
  exact hX.entropy_convexity_bounded_segment K n hn ν₀ ν₁ _ C h0 h1 hm p (3*R)
    (hs0.mono fun _ hx => hx.trans (by linarith))
    (hs1.mono fun _ hx => hx.trans (by linarith)) hsupport s hd0 hd1

 

theorem NoncollapsedRCD.entropy_plan_marginal_le_log_capacity
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C M : ℝ} (hC : 0 < C)
    (h0 : ν₀ ≤ ENNReal.ofReal C • hausdorff n X)
    (h1 : ν₁ ≤ ENNReal.ofReal C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (plan : Measure C(Time,X)) [IsProbabilityMeasure plan]
    (hg : ∀ᵐ γ ∂plan, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (plan.map (fun γ => (γ 0,γ 1))))
    (s : Time) (hm : plan.map (fun γ => γ s) ≤ ENNReal.ofReal M • hausdorff n X) :
    boltzmannEntropy (hausdorff n X) (plan.map (fun γ => γ s)) ≤
      Real.log C+max (-K) 0*R^2/2 := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let D : ℝ≥0 := ⟨max C M,hC.le.trans (le_max_left _ _)⟩
  have hmono : ∀ {a b : ℝ}, a ≤ b → ENNReal.ofReal a • μ ≤ ENNReal.ofReal b • μ := by
    intro a b hab S
    simp only [Measure.smul_apply,smul_eq_mul]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hab) _
  have hd0 : ν₀ ≤ ENNReal.ofReal D • μ := h0.trans (hmono (le_max_left _ _))
  have hd1 : ν₁ ≤ ENNReal.ofReal D • μ := h1.trans (hmono (le_max_left _ _))
  have hdm : plan.map (fun γ => γ s) ≤ ENNReal.ofReal D • μ := hm.trans (hmono (le_max_right _ _))
  have hh := hX.entropy_convexity_bounded_plan_marginal K n hn ν₀ ν₁ D hd0 hd1 p hR hs0 hs1 plan hg hp s hdm
  let : IsFiniteMeasure (μ.restrict (closedBall p R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall p R).measure_lt_top⟩
  have he0 := entropy_le_log_density_bound μ ν₀ hC h0 measurableSet_closedBall hs0
  have he1 := entropy_le_log_density_bound μ ν₁ hC h1 measurableSet_closedBall hs1
  have hE : (1-(s:ℝ))*boltzmannEntropy μ ν₀+(s:ℝ)*boltzmannEntropy μ ν₁ ≤ Real.log C := by
    have h0 := mul_le_mul_of_nonneg_left he0 (sub_nonneg.mpr s.2.2)
    have h1 := mul_le_mul_of_nonneg_left he1 s.2.1
    nlinarith only [h0,h1]
  have hD := wassersteinSq_ball_bound p p hR hs0 hs1
  simp only [dist_self,zero_add] at hD
  have hs : 0 ≤ (s:ℝ)*(1-(s:ℝ)) := mul_nonneg s.2.1 (sub_nonneg.mpr s.2.2)
  have hs' : (s:ℝ)*(1-(s:ℝ)) ≤ 1/4 := by nlinarith [sq_nonneg ((s:ℝ)-1/2)]
  have hprod : (s:ℝ)*(1-(s:ℝ))*(wassersteinSq ν₀ ν₁).toReal ≤ R^2 := by
    have h := mul_le_mul_of_nonneg_left hD hs
    have h' := mul_le_mul_of_nonneg_right hs' (sq_nonneg (2*R))
    nlinarith only [h,h']
  have ht : -(K/2)*(s:ℝ)*(1-(s:ℝ))*(wassersteinSq ν₀ ν₁).toReal ≤ max (-K) 0*R^2/2 := by
    have h1 := mul_le_mul_of_nonneg_right (le_max_left (-K) 0)
      (mul_nonneg hs (ENNReal.toReal_nonneg (a := wassersteinSq ν₀ ν₁)))
    have h2 := mul_le_mul_of_nonneg_left hprod (le_max_right (-K) 0)
    nlinarith only [h1,h2]
  linarith only [hh,hE,ht]


end RegularPointCoordinates

end OAI
