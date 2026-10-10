import Mathlib
import OAI.Analysis.RCDHeat.ExistingAnalytic
import OAI.Analysis.RCDHeat.VariableRadialSecant

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: VariableHeatODE, VariableHeat, VariableHeatCoefficient, VariableAverageDual, QuadraticComparisonAdd, VariablePointwiseDual. -/



namespace RegularPointCoordinates

section

 
open Set Filter MeasureTheory
open scoped Topology

theorem gronwallBound_integral_exp (δ c ε t : ℝ) :
    gronwallBound δ c ε t = δ*Real.exp (c*t)+ε*(∫s in (0:ℝ)..t, Real.exp (c*s)) := by
  by_cases hc : c = 0
  · subst c
    simp [gronwallBound_K0]
  · rw [gronwallBound_of_K_ne_0 hc,intervalIntegral.integral_comp_mul_left _ hc]
    simp only [mul_zero,integral_exp,Real.exp_zero,smul_eq_mul]
    ring

theorem variable_slope_integrated {D : ℝ → ℝ} {c E a b : ℝ} (hab : a ≤ b)
    (hD : ContinuousOn D (Icc a b))
    (hsec : ∀ t ∈ Ico a b, ∀ z, c*D t+E < z → ∃ᶠ s in 𝓝[>] t, slope D t s < z) :
    D b ≤ D a*Real.exp (c*(b-a))+E*(∫s in (0:ℝ)..(b-a), Real.exp (c*s)) := by
  have hg := le_gronwallBound_of_liminf_deriv_right_le (f' := fun t => c*D t+E)
    (K := c) (ε := E) hD (by
      intro t ht z hz
      simpa only [slope_def_field,div_eq_mul_inv,mul_comm] using hsec t ht z hz)
    le_rfl (by intro t ht; rfl) b ⟨hab,le_rfl⟩
  rwa [gronwallBound_integral_exp] at hg

end

 
section

 
open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.variable_heat_contraction_positive
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (p : X)
    (f g : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0) (hf0 : 0 ≤ f) (hg0 : 0 ≤ g)
    (hfC : ∀ᵐ x ∂hausdorff n X, f x ≤ C) (hgC : ∀ᵐ x ∂hausdorff n X, g x ≤ C)
    (hfm : ∫x, f x ∂hausdorff n X = 1) (hgm : ∫x, g x ∂hausdorff n X = 1)
    {r r' : ℝ} (hfs : ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r)
    (hgs : ∀ᵐ x ∂hausdorff n X, g x ≠ 0 → dist p x ≤ r')
    (N : ℝ) (hN : (n:ℝ) ≤ N) (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    letI : SeparableSpace X := hX.separable
    letI : ProperSpace X := hX.proper K n hn
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic (u^2*b) f)
        (heatMeasure (hausdorff n X) hX.quadratic (v^2*b) g)).toReal ≤
      (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic (u^2*a) f)
        (heatMeasure (hausdorff n X) hX.quadratic (v^2*a) g)).toReal*Real.exp (-2*K*(u^2+u*v+v^2)/3*(b-a))+
      2*N*(u-v)^2*(∫s in (0:ℝ)..(b-a), Real.exp (-2*K*(u^2+u*v+v^2)/3*s)) := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let D : ℝ → ℝ := fun t => (wassersteinSq (heatMeasure μ hX.quadratic (u^2*t) f)
    (heatMeasure μ hX.quadratic (v^2*t) g)).toReal/2
  let c := -2*K*(u^2+u*v+v^2)/3
  have hDc {t : ℝ} (ht : 0 < t) : ContinuousAt D t :=
    ((hX.heat_two_cost_continuousAt K n hn p f g C hf0 hfC hfm hfs hg0 hgC hgm hgs
      (mul_pos (sq_pos_of_pos hu) ht) (mul_pos (sq_pos_of_pos hv) ht)).comp
      (f := fun s : ℝ => (u^2*s,v^2*s)) (x := t)
      ((continuousAt_id.const_mul _).prodMk (continuousAt_id.const_mul _))).div_const 2
  have hi := variable_slope_integrated (D := D) (c := c) (E := N*(u-v)^2) hab
    (fun t ht => (hDc (ha.trans_le ht.1)).continuousWithinAt) (by
      intro t ht z hz
      apply hX.variable_heat_frequent_slope K n hn p f g C hf0 hg0 hfC hgC hfm hgm hfs hgs
        N hN u v hu hv (ha.trans_le ht.1) z
      convert hz using 1
      all_goals try dsimp only [D,c,μ]
      all_goals first | rfl | ring)
  dsimp only [D,c] at hi
  linarith only [hi]

theorem NoncollapsedRCD.variable_heat_contraction
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (p : X)
    (f g : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0) (hf0 : 0 ≤ f) (hg0 : 0 ≤ g)
    (hfC : ∀ᵐ x ∂hausdorff n X, f x ≤ C) (hgC : ∀ᵐ x ∂hausdorff n X, g x ≤ C)
    (hfm : ∫x, f x ∂hausdorff n X = 1) (hgm : ∫x, g x ∂hausdorff n X = 1)
    {r r' : ℝ} (hfs : ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r)
    (hgs : ∀ᵐ x ∂hausdorff n X, g x ≠ 0 → dist p x ≤ r')
    (N : ℝ) (hN : (n:ℝ) ≤ N) (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    {b : ℝ} (hb : 0 ≤ b) :
    letI : SeparableSpace X := hX.separable
    letI : ProperSpace X := hX.proper K n hn
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic (u^2*b) f)
        (heatMeasure (hausdorff n X) hX.quadratic (v^2*b) g)).toReal ≤
      (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic 0 f)
        (heatMeasure (hausdorff n X) hX.quadratic 0 g)).toReal*Real.exp (-2*K*(u^2+u*v+v^2)/3*b)+
      2*N*(u-v)^2*(∫s in (0:ℝ)..b, Real.exp (-2*K*(u^2+u*v+v^2)/3*s)) := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  rcases hb.eq_or_lt with hb|hb
  · subst b
    simp only [mul_zero,Real.exp_zero,mul_one,intervalIntegral.integral_same,add_zero,le_refl]
  let := ACWassersteinProbability.metric μ K n hX.cd
  let ρ := hX.heatProbability K n hn p f hf0 ⟨r,hfs⟩ hfm
  let σ := hX.heatProbability K n hn p g hg0 ⟨r',hgs⟩ hgm
  let D : ℝ → ℝ := fun t => dist (ρ (u^2*t)) (σ (v^2*t))^2
  let c := -2*K*(u^2+u*v+v^2)/3
  have hfabs : ∀ᵐ x ∂μ, |f x| ≤ C := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr hf0,hfC] with x hl hu
    simpa only [abs_of_nonneg hl] using hu
  have hgabs : ∀ᵐ x ∂μ, |g x| ≤ C := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr hg0,hgC] with x hl hu
    simpa only [abs_of_nonneg hl] using hu
  have hρ' : ContinuousOn ρ (Icc 0 (u^2*b)) := by
    have hh := (metricAC_uniformContinuousOn
      (hX.heat_probability_absolutelyContinuous K n hn p f hf0 ⟨r,hfs⟩ hfm C hfabs (u^2*b) (by positivity))).continuousOn
    change ContinuousOn ρ (uIcc 0 (u^2*b)) at hh
    rwa [uIcc_of_le (by positivity : (0:ℝ) ≤ u^2*b)] at hh
  have hσ' : ContinuousOn σ (Icc 0 (v^2*b)) := by
    have hh := (metricAC_uniformContinuousOn
      (hX.heat_probability_absolutelyContinuous K n hn p g hg0 ⟨r',hgs⟩ hgm C hgabs (v^2*b) (by positivity))).continuousOn
    change ContinuousOn σ (uIcc 0 (v^2*b)) at hh
    rwa [uIcc_of_le (by positivity : (0:ℝ) ≤ v^2*b)] at hh
  have hρ : ContinuousOn (fun t => ρ (u^2*t)) (Icc 0 b) :=
    hρ'.comp (by fun_prop) (fun t ht => ⟨mul_nonneg (sq_nonneg u) ht.1,mul_le_mul_of_nonneg_left ht.2 (sq_nonneg u)⟩)
  have hσ : ContinuousOn (fun t => σ (v^2*t)) (Icc 0 b) :=
    hσ'.comp (by fun_prop) (fun t ht => ⟨mul_nonneg (sq_nonneg v) ht.1,mul_le_mul_of_nonneg_left ht.2 (sq_nonneg v)⟩)
  have hcI : ContinuousWithinAt D (Icc 0 b) 0 := ((hρ 0 ⟨le_rfl,hb.le⟩).dist (hσ 0 ⟨le_rfl,hb.le⟩)).pow 2
  have hc : ContinuousWithinAt D (Ioi 0) 0 :=
    (hcI.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hb)).mono Ioi_subset_Ici_self
  have heq (t : ℝ) (ht : 0 ≤ t) : D t =
      (wassersteinSq (heatMeasure μ hX.quadratic (u^2*t) f) (heatMeasure μ hX.quadratic (v^2*t) g)).toReal := by
    rw [show D t = dist (ρ (u^2*t)) (σ (v^2*t))^2 from rfl,ACWassersteinProbability.dist_sq μ hX.cd]
    dsimp only [ρ,σ,NoncollapsedRCD.heatProbability]
    rw [max_eq_left (mul_nonneg (sq_nonneg u) ht),max_eq_left (mul_nonneg (sq_nonneg v) ht)]
  have he : ∀ᶠ a in 𝓝[>] (0:ℝ), D b ≤ D a*Real.exp (c*(b-a))+
      2*N*(u-v)^2*(∫s in (0:ℝ)..(b-a), Real.exp (c*s)) := by
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds hb)] with a ha ha'
    rw [heq b hb.le,heq a (show 0 < a from ha).le]
    exact hX.variable_heat_contraction_positive K n hn p f g C hf0 hg0 hfC hgC hfm hgm hfs hgs N hN u v hu hv ha (le_of_lt ha')
  have hIa : Continuous (fun a : ℝ => ∫s in (0:ℝ)..(b-a), Real.exp (c*s)) :=
    (intervalIntegral.continuous_primitive (fun _ _ => (by fun_prop : Continuous (fun s : ℝ => Real.exp (c*s))).intervalIntegrable _ _) 0).comp (by fun_prop)
  have hex : Continuous (fun a : ℝ => Real.exp (c*(b-a))) := by fun_prop
  have hlim : Tendsto (fun a : ℝ => D a*Real.exp (c*(b-a))+2*N*(u-v)^2*(∫s in (0:ℝ)..(b-a), Real.exp (c*s)))
      (𝓝[>] 0) (𝓝 (D 0*Real.exp (c*b)+2*N*(u-v)^2*(∫s in (0:ℝ)..b, Real.exp (c*s)))) := by
    simpa only [sub_zero] using (hc.tendsto.mul hex.continuousAt.continuousWithinAt.tendsto).add (hIa.continuousAt.continuousWithinAt.tendsto.const_mul _)
  have hh := ge_of_tendsto hlim he
  simpa only [heq b hb.le,heq 0 le_rfl,mul_zero,c] using hh

end

 
section

open Set Filter MeasureTheory
open scoped Topology

noncomputable def heatSpaceFactor (K u v t : ℝ) : ℝ :=
  Real.exp (-2*K*(u^2+u*v+v^2)/3*t)
noncomputable def heatTimePenalty (K N u v t : ℝ) : ℝ :=
  2*N*(u-v)^2*(∫s in (0:ℝ)..t, Real.exp (-2*K*(u^2+u*v+v^2)/3*s))

theorem heatSpaceFactor_pos (K u v t : ℝ) : 0 < heatSpaceFactor K u v t := Real.exp_pos _

end

 
section

 
open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.variable_heat_average_quadratic_dual
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (f g : Lp ℝ 2 (hausdorff n X)) {φ ψ : X → ℝ}
    (hφ : Measurable φ) (hψ : Measurable ψ)
    (hf : φ =ᵐ[hausdorff n X] f) (hg : ψ =ᵐ[hausdorff n X] g)
    (M N : ℝ) (hM : ∀ x, |φ x| ≤ M) (hN : ∀ x, |ψ x| ≤ N)
    {c : ℝ} (hc0 : 0 ≤ c) (hd : ∀ x y, ψ x-φ y ≤ c*dist x y^2)
    (D : ℝ) (hD : (n:ℝ) ≤ D) (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    {t : ℝ} (ht : 0 ≤ t) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ x y : X, ∀ r : ℝ, 0 < r →
      (⨍z in closedBall x r, heatAt (hausdorff n X) hX.quadratic (u^2*t) g z ∂hausdorff n X) -
        (⨍z in closedBall y r, heatAt (hausdorff n X) hX.quadratic (v^2*t) f z ∂hausdorff n X) ≤
      c*heatSpaceFactor K u v t*(dist x y+2*r)^2+c*heatTimePenalty K D u v t := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  intro x y r hr
  let A := closedBall x r
  let B := closedBall y r
  have hA0 : μ A ≠ 0 := ne_of_gt ((hX.fullSupport x r hr).trans_le (measure_mono ball_subset_closedBall))
  have hB0 : μ B ≠ 0 := ne_of_gt ((hX.fullSupport y r hr).trans_le (measure_mono ball_subset_closedBall))
  have hAt : μ A ≠ ∞ := ne_of_lt (hX.finiteOnBounded A isBounded_closedBall)
  have hBt : μ B ≠ ∞ := ne_of_lt (hX.finiteOnBounded B isBounded_closedBall)
  let a := uniformDensityLp μ A measurableSet_closedBall hAt
  let b := uniformDensityLp μ B measurableSet_closedBall hBt
  have ha0 : 0 ≤ a := uniformDensityLp_nonneg μ A measurableSet_closedBall hAt
  have hb0 : 0 ≤ b := uniformDensityLp_nonneg μ B measurableSet_closedBall hBt
  have ham : ∫z, a z ∂μ = 1 := uniformDensityLp_integral μ A measurableSet_closedBall hAt hA0
  have hbm : ∫z, b z ∂μ = 1 := uniformDensityLp_integral μ B measurableSet_closedBall hBt hB0
  have has : ∀ᵐ z ∂μ, a z ≠ 0 → dist x z ≤ r := by
    filter_upwards [uniformDensityLp_ae μ A measurableSet_closedBall hAt] with z hz hne
    have hh : z ∈ A := by by_contra hh; exact hne (hz.trans (indicator_of_notMem hh _))
    simpa only [A,mem_closedBall,dist_comm] using hh
  have hbs : ∀ᵐ z ∂μ, b z ≠ 0 → dist x z ≤ dist x y+r := by
    filter_upwards [uniformDensityLp_ae μ B measurableSet_closedBall hBt] with z hz hne
    have hh : z ∈ B := by by_contra hh; exact hne (hz.trans (indicator_of_notMem hh _))
    have hh' : dist y z ≤ r := by simpa only [B,mem_closedBall,dist_comm] using hh
    exact (dist_triangle x y z).trans (add_le_add_right hh' _)
  let C : ℝ≥0 := ⟨max (μ A).toReal⁻¹ (μ B).toReal⁻¹,
    (inv_nonneg.mpr ENNReal.toReal_nonneg).trans (le_max_left _ _)⟩
  have haC : ∀ᵐ z ∂μ, a z ≤ C :=
    (uniformDensityLp_bound μ A measurableSet_closedBall hAt).mono fun z hz => hz.trans (le_max_left _ _)
  have hbC : ∀ᵐ z ∂μ, b z ≤ C :=
    (uniformDensityLp_bound μ B measurableSet_closedBall hBt).mono fun z hz => hz.trans (le_max_right _ _)
  let ν := heatMeasure μ hX.quadratic (u^2*t) a
  let σ := heatMeasure μ hX.quadratic (v^2*t) b
  obtain ⟨hνp,hνa,hνm,_⟩ := hX.heat_law K n hn x a ha0 ⟨r,has⟩ ham (u^2*t) (mul_nonneg (sq_nonneg u) ht)
  obtain ⟨hσp,hσa,hσm,_⟩ := hX.heat_law K n hn x b hb0 ⟨dist x y+r,hbs⟩ hbm (v^2*t) (mul_nonneg (sq_nonneg v) ht)
  let : IsProbabilityMeasure ν := hνp
  let : IsProbabilityMeasure σ := hσp
  obtain ⟨plan,_,_,hopt,_⟩ := hX.cd ν σ hνp hσp hνa hσa hνm hσm
  have hm := optimal_transport_quadratic_dual hνm hσm hopt hφ hψ M N hM hN hd
  have hc := hX.variable_heat_contraction K n hn x a b C ha0 hb0 haC hbC ham hbm has hbs D hD u v hu hv ht
  rw [uniformDensityLp_heat_zero μ hX.quadratic A measurableSet_closedBall hAt hA0,
    uniformDensityLp_heat_zero μ hX.quadratic B measurableSet_closedBall hBt hB0] at hc
  let : IsProbabilityMeasure (uniformOn μ A) := uniformOn_probability μ A hA0 hAt
  let : IsProbabilityMeasure (uniformOn μ B) := uniformOn_probability μ B hB0 hBt
  have hw := wassersteinSq_ball_bound x y hr.le
    (uniformOn_ae_mem μ A measurableSet_closedBall) (uniformOn_ae_mem μ B measurableSet_closedBall)
  have hh : (∫z, ψ z ∂ν)-(∫z, φ z ∂σ) ≤
      c*heatSpaceFactor K u v t*(dist x y+2*r)^2+c*heatTimePenalty K D u v t := by
    calc _ ≤ c*(wassersteinSq ν σ).toReal := hm
      _ ≤ c*((wassersteinSq (uniformOn μ A) (uniformOn μ B)).toReal*heatSpaceFactor K u v t+heatTimePenalty K D u v t) :=
        mul_le_mul_of_nonneg_left hc hc0
      _ ≤ c*((dist x y+2*r)^2*heatSpaceFactor K u v t+heatTimePenalty K D u v t) :=
        mul_le_mul_of_nonneg_left (add_le_add_left (mul_le_mul_of_nonneg_right hw (heatSpaceFactor_pos K u v t).le) _) hc0
      _ = _ := by ring
  rw [heat_uniformDensityLp_pair μ hX.quadratic A measurableSet_closedBall hAt g (u^2*t) hg,
    heat_uniformDensityLp_pair μ hX.quadratic B measurableSet_closedBall hBt f (v^2*t) hf] at hh
  exact hh

end

 
section

 
open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] {μ : Measure X} [IsLocallyFiniteMeasure μ]
  [IsUnifLocDoublingMeasure μ] [μ.IsOpenPosMeasure]

theorem quadratic_comparison_of_average_bound_add
    (u v U V : X → ℝ) (hu : LocallyIntegrable u μ) (hv : LocallyIntegrable v μ)
    (hU : Continuous U) (hV : Continuous V) (heU : u =ᵐ[μ] U) (heV : v =ᵐ[μ] V)
    (c e : ℝ) (h : ∀ x y : X, ∀ r : ℝ, 0 < r →
      (⨍z in closedBall x r, u z ∂μ) - (⨍z in closedBall y r, v z ∂μ) ≤
        c*(dist x y + 2*r)^2+e) :
    ∀ x y, U x-V y ≤ c*dist x y^2+e := by
  let S := {x : X | Tendsto (fun r : ℝ => ⨍z in closedBall x r, u z ∂μ)
    (𝓝[>] 0) (𝓝 (U x))}
  let T := {x : X | Tendsto (fun r : ℝ => ⨍z in closedBall x r, v z ∂μ)
    (𝓝[>] 0) (𝓝 (V x))}
  have hS : ∀ᵐ x ∂μ, x ∈ S := by
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average μ hu (1:ℝ),heU] with x hx he
    change Tendsto _ _ (𝓝 (U x))
    rw [←he]
    exact hx (fun _ : ℝ => x) id tendsto_id (by
      filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [mem_closedBall,dist_self,one_mul]
      exact le_of_lt hr)
  have hT : ∀ᵐ x ∂μ, x ∈ T := by
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average μ hv (1:ℝ),heV] with x hx he
    change Tendsto _ _ (𝓝 (V x))
    rw [←he]
    exact hx (fun _ : ℝ => x) id tendsto_id (by
      filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [mem_closedBall,dist_self,one_mul]
      exact le_of_lt hr)
  have hST : ∀ x ∈ S, ∀ y ∈ T, U x-V y ≤ c*dist x y^2+e := by
    intro x hx y hy
    have hc : Tendsto (fun r : ℝ => c*(dist x y+2*r)^2+e) (𝓝[>] 0)
        (𝓝 (c*dist x y^2+e)) := by
      have hh : Continuous (fun r : ℝ => c*(dist x y+2*r)^2+e) := by fun_prop
      simpa using (hh.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    have hb : ∀ᶠ r in 𝓝[>] (0:ℝ),
        (⨍z in closedBall x r, u z ∂μ) - (⨍z in closedBall y r, v z ∂μ) ≤
          c*(dist x y+2*r)^2+e := by
      filter_upwards [self_mem_nhdsWithin] with r hr using h x y r hr
    exact le_of_tendsto_of_tendsto (hx.sub hy) hc hb
  have hd : Dense (S ×ˢ T) := (Measure.dense_of_ae hS).prod (Measure.dense_of_ae hT)
  have hc : IsClosed {z : X×X | U z.1-V z.2 ≤ c*dist z.1 z.2^2+e} :=
    isClosed_le ((hU.comp continuous_fst).sub (hV.comp continuous_snd)) (by fun_prop)
  have hs : closure (S ×ˢ T) ⊆ {z : X×X | U z.1-V z.2 ≤ c*dist z.1 z.2^2+e} :=
    hc.closure_subset_iff.mpr (fun z hz => hST z.1 hz.1 z.2 hz.2)
  intro x y
  exact hs (hd (x,y))

end

 

 
open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.variable_heat_pointwise_quadratic_dual
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (f g : Lp ℝ 2 (hausdorff n X)) {φ ψ : X → ℝ}
    (hφ : Measurable φ) (hψ : Measurable ψ)
    (hf : φ =ᵐ[hausdorff n X] f) (hg : ψ =ᵐ[hausdorff n X] g)
    (M N : ℝ) (hM : ∀ x, |φ x| ≤ M) (hN : ∀ x, |ψ x| ≤ N)
    {c : ℝ} (hc0 : 0 ≤ c) (hd : ∀ x y, ψ x-φ y ≤ c*dist x y^2)
    (D : ℝ) (hD : (n:ℝ) ≤ D) (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    {t : ℝ} (ht : 0 ≤ t) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ U V : X → ℝ, Continuous U → Continuous V →
      (heatAt (hausdorff n X) hX.quadratic (u^2*t) g : X → ℝ) =ᵐ[hausdorff n X] U →
      (heatAt (hausdorff n X) hX.quadratic (v^2*t) f : X → ℝ) =ᵐ[hausdorff n X] V →
      ∀ x y, U x-V y ≤ c*heatSpaceFactor K u v t*dist x y^2+c*heatTimePenalty K D u v t := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let : IsUnifLocDoublingMeasure μ := hX.locDoubling K n hn
  let : μ.IsOpenPosMeasure := hX.openPos K n
  intro U V hU hV heU heV
  exact quadratic_comparison_of_average_bound_add _ _ U V
    ((Lp.memLp _).locallyIntegrable (by norm_num)) ((Lp.memLp _).locallyIntegrable (by norm_num))
    hU hV heU heV _ _ (hX.variable_heat_average_quadratic_dual K n hn f g hφ hψ hf hg M N hM hN hc0 hd D hD u v hu hv ht)


end RegularPointCoordinates

end OAI
