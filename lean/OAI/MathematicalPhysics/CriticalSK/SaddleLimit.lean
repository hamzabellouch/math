import OAI.MathematicalPhysics.CriticalSK.PartitionBounds

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal

open scoped BigOperators NNReal

open scoped BigOperators

open scoped BigOperators InnerProductSpace

open Module

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal BigOperators

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped NNReal ENNReal BigOperators

open scoped NNReal ENNReal

open ProbabilityTheory

open Metric Set MeasureTheory

open scoped ENNReal Pointwise

open MeasureTheory Filter Set Real

namespace CriticalSK

section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma saddleRadius_le_iff (lam : ι → ℝ) {a r : ℝ} (ha : 0 < a) (hr : spectralTop lam < r) :
    saddleRadius lam a ≤ r ↔ spectralStieltjes lam r ≤ a := by
  have hs := saddleRadius_spec lam ha
  constructor
  · intro h
    rw [← hs.2]
    exact (spectralStieltjes_strictAnti lam).antitoneOn hs.1 hr h
  · intro h
    by_contra hc
    have he := spectralStieltjes_strictAnti lam hr hs.1 (lt_of_not_ge hc)
    rw [hs.2] at he
    exact (not_lt_of_ge h) he

lemma le_saddleRadius_iff (lam : ι → ℝ) {a r : ℝ} (ha : 0 < a) (hr : spectralTop lam < r) :
    r ≤ saddleRadius lam a ↔ a ≤ spectralStieltjes lam r := by
  have hs := saddleRadius_spec lam ha
  constructor
  · intro h
    rw [← hs.2]
    exact (spectralStieltjes_strictAnti lam).antitoneOn hr hs.1 h
  · intro h
    by_contra hc
    have he := spectralStieltjes_strictAnti lam hs.1 hr (lt_of_not_ge hc)
    rw [hs.2] at he
    exact (not_lt_of_ge h) he

lemma semicircleResolvent_gt_from_inverse {s x : ℝ} (hs : 0 < s) (hx : x ≤ 1)
    (h : s*x < (1-x)^2) : x < semicircleResolvent s := by
  have hsq := Real.sq_sqrt (show 0 ≤ s*(4+s) by positivity)
  have hp : 0 < 2+s-2*x := by linarith
  have hr : Real.sqrt (s*(4+s)) < 2+s-2*x := by nlinarith
  unfold semicircleResolvent
  linarith

lemma semicircleResolvent_subcritical_margin {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1/4) :
    1-u+(1/100)*Real.sqrt ((9/10)*u^2/(1-u)) <
      semicircleResolvent ((9/10)*u^2/(1-u)) := by
  have hden : 0 < 1-u := by linarith
  have hs : 0 < (9/10:ℝ)*u^2/(1-u) := by positivity
  have hpoly : ((9/10:ℝ)*u^2/(1-u))*(1-(49/50)*u) < (1-(1-(49/50)*u))^2 := by
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).mpr
    nlinarith [sq_pos_of_pos hu,mul_nonneg (sq_nonneg u) (show 0 ≤ 1/4-u by linarith)]
  have hx := semicircleResolvent_gt_from_inverse hs (show 1-(49/50:ℝ)*u ≤ 1 by linarith) hpoly
  have hsqrt : Real.sqrt ((9/10:ℝ)*u^2/(1-u)) ≤ 2*u := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · apply (div_le_iff₀ hden).mpr
      nlinarith [mul_nonneg (sq_nonneg u) (show 0 ≤ 1/4-u by linarith)]
  linarith

lemma subcritical_test_scale {s₀ u : ℝ} (hs₀ : 0 ≤ s₀) (hu : 0 < u)
    (hu1 : u ≤ 1/4) (hum : 16*s₀ ≤ u^2) :
    s₀ ≤ (9/10:ℝ)*u^2/(1-u) ∧ (9/10:ℝ)*u^2/(1-u) ≤ 1 := by
  have hden : 0 < 1-u := by linarith
  constructor
  · apply (le_div_iff₀ hden).mpr
    nlinarith
  · apply (div_le_iff₀ hden).mpr
    nlinarith [sq_nonneg (u-1/4)]

lemma saddleRadius_subcritical_lower (lam : ι → ℝ) {s₀ u : ℝ}
    (hs₀ : 0 ≤ s₀) (hedge : spectralTop lam < 2+s₀)
    (hres : ∀ s ∈ Icc s₀ 1, |spectralStieltjes lam (2+s)-semicircleResolvent s| ≤ (1/100)*Real.sqrt s)
    (hu : 0 < u) (hu1 : u ≤ 1/4) (hum : 16*s₀ ≤ u^2) :
    2+(9/10)*u^2/(1-u) ≤ saddleRadius lam (1-u) := by
  have hs := subcritical_test_scale hs₀ hu hu1 hum
  have htest := hres _ hs
  have hmargin := semicircleResolvent_subcritical_margin hu hu1
  have hle : 1-u ≤ spectralStieltjes lam (2+(9/10)*u^2/(1-u)) := by
    have hh := (abs_le.mp htest).1
    linarith
  exact (le_saddleRadius_iff lam (by linarith) (by linarith)).mpr hle

def saddlePairDeficit (lam : ι → ℝ) (q : ℝ) : ℝ :=
  sphericalVariational lam (1+q)+sphericalVariational lam (1-q)-2*sphericalVariational lam 1

def saddlePairSlope (lam : ι → ℝ) (u : ℝ) : ℝ :=
  (saddleRadius lam (1+u)-(1+u)⁻¹)/2-(saddleRadius lam (1-u)-(1-u)⁻¹)/2

lemma saddlePairDeficit_zero (lam : ι → ℝ) : saddlePairDeficit lam 0 = 0 := by
  simp [saddlePairDeficit]; ring

lemma saddlePairDeficit_hasDerivAt (lam : ι → ℝ) {u : ℝ} (hu : |u| < 1) :
    HasDerivAt (saddlePairDeficit lam) (saddlePairSlope lam u) u := by
  have h1 := (sphericalVariational_hasDerivAt lam (show 0 < 1+u by linarith [(abs_lt.mp hu).1])).comp u
    ((hasDerivAt_const u 1).add (hasDerivAt_id u))
  have h2 := (sphericalVariational_hasDerivAt lam (show 0 < 1-u by linarith [(abs_lt.mp hu).2])).comp u
    ((hasDerivAt_const u 1).sub (hasDerivAt_id u))
  convert! ((h1.add h2).sub_const (2*sphericalVariational lam 1)) using 1
  simp only [saddlePairSlope,zero_add,zero_sub,mul_one,mul_neg_one]
  ring

lemma saddlePairDeficit_continuousOn (lam : ι → ℝ) : ContinuousOn (saddlePairDeficit lam) (Icc 0 1) := by
  have h1 := (sphericalVariational_continuousOn lam).comp (continuous_const.add continuous_id).continuousOn
    (show MapsTo (fun q : ℝ => 1+q) (Icc 0 1) (Ici 0) by intro q hq; simp only [mem_Ici]; linarith [hq.1])
  have h2 := (sphericalVariational_continuousOn lam).comp (continuous_const.sub continuous_id).continuousOn
    (show MapsTo (fun q : ℝ => 1-q) (Icc 0 1) (Ici 0) by intro q hq; simp only [mem_Ici]; linarith [hq.2])
  exact (h1.add h2).sub continuousOn_const

lemma subcritical_coefficient {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1/4) :
    (1:ℝ)/3 ≤ 1/(2*(1+u))-1/(20*(1-u)) := by
  have hP : 0 < 1+u := by linarith
  have hM : 0 < 1-u := by linarith
  have hD : 0 < 1-u^2 := by nlinarith
  have he : 1/(2*(1+u))-1/(20*(1-u)) = (9-11*u)/(20*(1-u^2)) := by
    field_simp
    ring
  rw [he]
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith [mul_nonneg (show 0 ≤ 1/4-u by linarith) (show 0 ≤ 7/5-u by linarith)]

lemma subcritical_short_coefficient {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1/4) :
    u/(1-u^2) ≤ u+u^2/3 := by
  have hD : 0 < 1-u^2 := by nlinarith
  apply (div_le_iff₀ hD).mpr
  have hp : 0 ≤ 1-3*u-u^2 := by nlinarith
  nlinarith [mul_nonneg (sq_nonneg u) hp]

lemma saddlePairSlope_small_bound (lam : ι → ℝ) {s₀ u : ℝ}
    (hs₀ : 0 ≤ s₀) (hedge : spectralTop lam < 2+s₀) (hlow : 2-s₀ ≤ spectralTop lam)
    (hres₀ : spectralStieltjes lam (2+s₀) ≤ 1)
    (hres : ∀ s ∈ Icc s₀ 1, |spectralStieltjes lam (2+s)-semicircleResolvent s| ≤ (1/100)*Real.sqrt s)
    (hu : 0 < u) (hu1 : u ≤ 1/4) :
    saddlePairSlope lam u ≤ u-u^2/3+12*s₀ := by
  have hP : 0 < 1+u := by linarith
  have hM : 0 < 1-u := by linarith
  have hD : 0 < 1-u^2 := by nlinarith
  have hp : saddleRadius lam (1+u) ≤ 2+s₀ :=
    (saddleRadius_le_iff lam hP hedge).mpr (by linarith)
  by_cases hum : 16*s₀ ≤ u^2
  · have hm := saddleRadius_subcritical_lower lam hs₀ hedge hres hu hu1 hum
    have halg : (2+s₀-(1+u)⁻¹)/2-((2+(9/10)*u^2/(1-u))-(1-u)⁻¹)/2 =
        u-u^2*(1/(2*(1+u))-1/(20*(1-u)))+s₀/2 := by
      field_simp
      ring
    have hc := subcritical_coefficient hu.le hu1
    unfold saddlePairSlope
    nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg u)]
  · have hm : 2-s₀ < saddleRadius lam (1-u) := hlow.trans_lt (saddleRadius_spec lam hM).1
    have halg : (2+s₀-(1+u)⁻¹)/2-(2-s₀-(1-u)⁻¹)/2 = s₀+u/(1-u^2) := by
      field_simp
      ring
    have hc := subcritical_short_coefficient hu.le hu1
    unfold saddlePairSlope
    nlinarith

lemma saddlePairDeficit_small_bound (lam : ι → ℝ) {s₀ q : ℝ}
    (hs₀ : 0 ≤ s₀) (hedge : spectralTop lam < 2+s₀) (hlow : 2-s₀ ≤ spectralTop lam)
    (hres₀ : spectralStieltjes lam (2+s₀) ≤ 1)
    (hres : ∀ s ∈ Icc s₀ 1, |spectralStieltjes lam (2+s)-semicircleResolvent s| ≤ (1/100)*Real.sqrt s)
    (hq : q ∈ Icc 0 (1/4)) :
    saddlePairDeficit lam q ≤ q^2/2-q^3/9+12*s₀*q := by
  let g : ℝ → ℝ := fun u => u^2/2-u^3/9+12*s₀*u
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hdg (u : ℝ) : HasDerivAt g (u-u^2/3+12*s₀) u := by
    convert! ((((hasDerivAt_id u).pow 2).div_const 2).sub (((hasDerivAt_id u).pow 3).div_const 9)).add
      ((hasDerivAt_id u).const_mul (12*s₀)) using 1
    simp only [id_eq]
    ring
  have hD (u : ℝ) (hu : u ∈ Ioo 0 q) :
      HasDerivAt (fun u => saddlePairDeficit lam u-g u)
        (saddlePairSlope lam u-(u-u^2/3+12*s₀)) u := by
    exact (saddlePairDeficit_hasDerivAt lam (by rw [abs_of_pos hu.1]; linarith [hu.2,hq.2])).sub (hdg u)
  have hc : ContinuousOn (fun u => saddlePairDeficit lam u-g u) (Icc 0 q) :=
    ((saddlePairDeficit_continuousOn lam).mono (fun _ hu => ⟨hu.1,by linarith [hu.2,hq.2]⟩)).sub hg.continuousOn
  have hmono := antitoneOn_of_deriv_nonpos (convex_Icc 0 q) hc
    (fun u hu => (hD u (by rwa [interior_Icc] at hu)).differentiableAt.differentiableWithinAt)
    (fun u hu => by
      rw [interior_Icc] at hu
      rw [(hD u hu).deriv]
      have hh := saddlePairSlope_small_bound lam hs₀ hedge hlow hres₀ hres hu.1 (by linarith [hu.2,hq.2])
      linarith)
  have hh := hmono (show (0:ℝ) ∈ Icc 0 q from ⟨le_refl 0,hq.1⟩) (show q ∈ Icc 0 q from ⟨hq.1,le_refl q⟩) hq.1
  simpa [g,saddlePairDeficit_zero] using hh

lemma saddlePairDeficit_shrinking_cubic (lam : ι → ℝ) {s₀ q : ℝ}
    (hs₀ : 0 ≤ s₀) (hedge : spectralTop lam < 2+s₀) (hlow : 2-s₀ ≤ spectralTop lam)
    (hres₀ : spectralStieltjes lam (2+s₀) ≤ 1)
    (hres : ∀ s ∈ Icc s₀ 1, |spectralStieltjes lam (2+s)-semicircleResolvent s| ≤ (1/100)*Real.sqrt s)
    (hq : q ∈ Icc 0 (1/4)) (hscale : 216*s₀ ≤ q^2) :
    saddlePairDeficit lam q ≤ q^2/2-q^3/18 := by
  have hh := saddlePairDeficit_small_bound lam hs₀ hedge hlow hres₀ hres hq
  nlinarith [mul_le_mul_of_nonneg_right hscale hq.1]

end

section

lemma semicircleResolvent_lt_from_inverse {s x : ℝ} (hs : 0 < s) (hx : x ≤ 1)
    (h : (1-x)^2 < s*x) : semicircleResolvent s < x := by
  have hsq := Real.sq_sqrt (show 0 ≤ s*(4+s) by positivity)
  have hn := Real.sqrt_nonneg (s*(4+s))
  have hp : 0 < 2+s-2*x := by linarith
  have hr : 2+s-2*x < Real.sqrt (s*(4+s)) := by nlinarith
  unfold semicircleResolvent
  linarith

lemma subcritical_radius_gap {a : ℝ} (ha : 0 < a) (ha1 : a < 1) : 2 < a+a⁻¹ := by
  have hsq : 0 < (1-a)^2 := sq_pos_of_pos (by linarith)
  have heq : (a+a⁻¹-2)*a = (1-a)^2 := by field_simp; ring
  nlinarith

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)]

lemma saddleRadius_subcritical_tendsto (lam : (n : ℕ) → ι n → ℝ)
    (htop : Tendsto (fun n => spectralTop (lam n)) atTop (𝓝 2))
    (hres : ∀ s > 0, Tendsto (fun n => spectralStieltjes (lam n) (2+s)) atTop (𝓝 (semicircleResolvent s)))
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun n => saddleRadius (lam n) a) atTop (𝓝 (a+a⁻¹)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := min (ε/2) ((a+a⁻¹-2)/2)
  have hδ : 0 < δ := lt_min (by positivity) (by linarith [subcritical_radius_gap ha ha1])
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδr : δ ≤ (a+a⁻¹-2)/2 := min_le_right _ _
  have hminus : 0 < a+a⁻¹-2-δ := by linarith
  have hplus : 0 < a+a⁻¹-2+δ := by linarith
  have he : (a+a⁻¹-2)*a = (1-a)^2 := by field_simp; ring
  have hRm : a < semicircleResolvent (a+a⁻¹-2-δ) :=
    semicircleResolvent_gt_from_inverse hminus ha1.le (by nlinarith)
  have hRp : semicircleResolvent (a+a⁻¹-2+δ) < a :=
    semicircleResolvent_lt_from_inverse hplus ha1.le (by nlinarith)
  have hm := (hres _ hminus).eventually (lt_mem_nhds hRm)
  have hp := (hres _ hplus).eventually (gt_mem_nhds hRp)
  have ht := htop.eventually (gt_mem_nhds (show (2:ℝ) < a+a⁻¹-δ by linarith))
  filter_upwards [hm,hp,ht] with n hnm hnp hnt
  have hshadowMinus : 2+(a+a⁻¹-2-δ) = a+a⁻¹-δ := by ring
  have hshadowPlus : 2+(a+a⁻¹-2+δ) = a+a⁻¹+δ := by ring
  rw [hshadowMinus] at hnm
  rw [hshadowPlus] at hnp
  have hlow := (le_saddleRadius_iff (lam n) ha hnt).mpr hnm.le
  have hupp := (saddleRadius_le_iff (lam n) ha (by linarith : spectralTop (lam n) < a+a⁻¹+δ)).mpr hnp.le
  rw [Real.dist_eq,abs_lt]
  constructor <;> linarith

lemma sphericalVariational_deriv_tendsto (lam : (n : ℕ) → ι n → ℝ)
    (htop : Tendsto (fun n => spectralTop (lam n)) atTop (𝓝 2))
    (hres : ∀ s > 0, Tendsto (fun n => spectralStieltjes (lam n) (2+s)) atTop (𝓝 (semicircleResolvent s)))
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun n => deriv (sphericalVariational (lam n)) a) atTop (𝓝 (a/2)) := by
  have h := ((saddleRadius_subcritical_tendsto lam htop hres ha ha1).sub_const a⁻¹).div_const 2
  simpa only [add_sub_cancel_right, (sphericalVariational_hasDerivAt _ ha).deriv] using h

def saddleSubcriticalError {κ : Type*} [Fintype κ] [Nonempty κ] (lam : κ → ℝ) : ℝ :=
  ∫ a in (0:ℝ)..1, |deriv (sphericalVariational lam) a-a/2|

lemma saddleSubcriticalError_tendsto (lam : (n : ℕ) → ι n → ℝ)
    (hbound : ∀ᶠ n in atTop, ∀ i, |lam n i| ≤ 3)
    (htop : Tendsto (fun n => spectralTop (lam n)) atTop (𝓝 2))
    (hres : ∀ s > 0, Tendsto (fun n => spectralStieltjes (lam n) (2+s)) atTop (𝓝 (semicircleResolvent s))) :
    Tendsto (fun n => saddleSubcriticalError (lam n)) atTop (𝓝 0) := by
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun a => |deriv (sphericalVariational (lam n)) a-a/2|)
      (volume.restrict (Ioo (0:ℝ) 1)) :=
    ((measurable_deriv _).sub (measurable_id.div_const 2)).abs.aestronglyMeasurable
  have hdom : ∀ᶠ n in atTop, ∀ᵐ a ∂volume.restrict (Ioo (0:ℝ) 1),
      ‖|deriv (sphericalVariational (lam n)) a-a/2|‖ ≤ 2 := by
    filter_upwards [hbound] with n hn
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
    rw [norm_eq_abs,abs_abs,(sphericalVariational_hasDerivAt _ ha.1).deriv]
    calc
      _ ≤ |(saddleRadius (lam n) a-a⁻¹)/2|+|a/2| := abs_sub _ _
      _ ≤ 3/2+a/2 := by
        rw [abs_of_pos (div_pos ha.1 (by norm_num) : 0 < a/2)]
        exact add_le_add (sphericalVariational_slope_bound _ ha.1 hn) (le_refl _)
      _ ≤ 2 := by linarith [ha.2]
  have hlim : ∀ᵐ a ∂volume.restrict (Ioo (0:ℝ) 1),
      Tendsto (fun n => |deriv (sphericalVariational (lam n)) a-a/2|) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
    simpa using ((sphericalVariational_deriv_tendsto lam htop hres ha.1 ha.2).sub_const (a/2)).abs
  have hint : Integrable (fun _ : ℝ => (2:ℝ)) (volume.restrict (Ioo (0:ℝ) 1)) := by
    exact (continuousOn_const.integrableOn_Icc (μ := volume) (a := (0:ℝ)) (b := 1)).mono_set Ioo_subset_Icc_self
  have hh := tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => (2:ℝ))
    (Eventually.of_forall hmeas) hdom hint hlim
  simpa only [saddleSubcriticalError,intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo,integral_zero] using hh

end

open Set Filter

lemma spectralGood_reference (n : ℕ) {h s : ℝ} (hh : 0 ≤ h) (hs : 0 ≤ s) :
    (fun i => 2-orderedJacobiGaps n i) ∈ spectralGood n h s := by
  intro i
  simp only [sub_self,abs_zero]
  unfold edgeError
  exact add_nonneg (add_nonneg (mul_nonneg (formA_nonneg n hh) (Real.rpow_nonneg (add_nonneg (orderedJacobiGaps_nonneg n i) hs) _))
    (formB_nonneg n)) (mul_nonneg (formC_nonneg n) (orderedJacobiGaps_nonneg n i))

lemma spectralGood_natural_controls {h L : ℝ} (hh : 0 ≤ h) (hL : 1696 ≤ L)
    (hcost : edgeFixedCost h L < 1/100) :
    ∀ᶠ n : ℕ in atTop, ∀ lam ∈ spectralGood n h (naturalEdgeScale n L),
      (∀ i, |lam i| ≤ 3) ∧ |spectralTop lam-2| ≤ naturalEdgeScale n L := by
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hc := traceCost_natural_eventually hh hLp hcost
  have hs := (naturalEdgeScale_tendsto L).eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [hc,hs,edgeLength_tents_eventually] with n hn hns hnfit
  intro lam hlam
  have hp := naturalEdgeScale_pos n hLp
  refine ⟨spectralGood_bounded n hh hp hns.le (by norm_num : (1/100:ℝ) ≤ 1/5) hn hlam,?_⟩
  have hlow := (abs_le.mp (spectralGood_top_close hh hL hns.le hnfit hn hlam 0 (by simp))).1
  have hlu := le_spectralTop lam 0
  obtain ⟨i,hi⟩ := spectralTop_attained lam
  have hu := spectralGood_top_upper n hh hp hns.le (by norm_num : (1/100:ℝ) ≤ 1) hn hlam i
  rw [hi] at hu
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma spectralGood_natural_top_tendsto {h L : ℝ} (hh : 0 ≤ h) (hL : 1696 ≤ L)
    (hcost : edgeFixedCost h L < 1/100) (lam : (n : ℕ) → Fin (n+1) → ℝ)
    (hgood : ∀ᶠ n in atTop, lam n ∈ spectralGood n h (naturalEdgeScale n L)) :
    Tendsto (fun n => spectralTop (lam n)) atTop (𝓝 2) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [spectralGood_natural_controls hh hL hcost,hgood,
    (naturalEdgeScale_tendsto L).eventually (gt_mem_nhds hε)] with n hn hng hne
  rw [Real.dist_eq]
  exact (hn (lam n) hng).2.trans_lt hne

lemma traceError_fixed_tendsto {h s : ℝ} (hh : 0 ≤ h) (hs : 0 < s) :
    Tendsto (fun n : ℕ => 416*formA n h*s^(-1/8:ℝ)+8*formB n/Real.sqrt s+
      2*formC n+2/((n+1:ℝ)*s)) atTop (𝓝 0) := by
  have hA := ((formA_tendsto hh).const_mul 416).mul_const (s^(-1/8:ℝ))
  have hB := (formB_tendsto.const_mul 8).div_const (Real.sqrt s)
  have hC := formC_tendsto.const_mul 2
  have hN : Tendsto (fun n : ℕ => ((n:ℝ)+1)*s) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1:ℝ)))).atTop_mul_const hs
  simpa only [mul_zero,zero_mul,zero_div,zero_add] using ((hA.add hB).add hC).add (hN.const_div_atTop (2:ℝ))

lemma spectralGood_natural_resolvent_tendsto {h L : ℝ} (hh : 0 ≤ h) (hL : 1696 ≤ L)
    (hcost : edgeFixedCost h L < 1/100) (hspace : 16 ≤ L*Real.sqrt L)
    (lam : (n : ℕ) → Fin (n+1) → ℝ)
    (hgood : ∀ᶠ n in atTop, lam n ∈ spectralGood n h (naturalEdgeScale n L))
    (s : ℝ) (hs : 0 < s) :
    Tendsto (fun n => spectralStieltjes (lam n) (2+s)) atTop (𝓝 (semicircleResolvent s)) := by
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [traceCost_natural_eventually hh hLp hcost,hgood,
    (naturalEdgeScale_tendsto L).eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
    (naturalEdgeScale_tendsto L).eventually (gt_mem_nhds hs),
    (traceError_fixed_tendsto hh hs).eventually (gt_mem_nhds hε)] with n hnc hng hn1 hns hne
  have hp := naturalEdgeScale_pos n hLp
  have hsmall := (traceCost_small n hh hp hn1.le hnc).trans (by norm_num : (1/100:ℝ) ≤ 1/2)
  have hsc : 2 ≤ (n+1:ℝ)*naturalEdgeScale n L*Real.sqrt (naturalEdgeScale n L) := by
    have hx := (naturalEdgeScale_space n hLp).1
    linarith
  have ht := (spectralGood_resolvent n hh hp hns.le hsmall hsc hng).2.2
  rw [Real.dist_eq]
  apply lt_of_le_of_lt _ hne
  simpa only [spectralStieltjes,Fintype.card_fin,Nat.cast_add,Nat.cast_one,div_eq_mul_inv,mul_comm] using ht

lemma spectralGood_natural_saddle_tendsto {h L : ℝ} (hh : 0 ≤ h) (hL : 1696 ≤ L)
    (hcost : edgeFixedCost h L < 1/100) (hspace : 16 ≤ L*Real.sqrt L)
    (lam : (n : ℕ) → Fin (n+1) → ℝ)
    (hgood : ∀ᶠ n in atTop, lam n ∈ spectralGood n h (naturalEdgeScale n L)) :
    Tendsto (fun n => saddleSubcriticalError (lam n)) atTop (𝓝 0) := by
  apply saddleSubcriticalError_tendsto lam
  · filter_upwards [spectralGood_natural_controls hh hL hcost,hgood] with n hn hng
    exact (hn (lam n) hng).1
  · exact spectralGood_natural_top_tendsto hh hL hcost lam hgood
  · exact spectralGood_natural_resolvent_tendsto hh hL hcost hspace lam hgood

lemma spectralGood_saddle_uniform {h L : ℝ} (hh : 0 ≤ h) (hL : 1696 ≤ L)
    (hcost : edgeFixedCost h L < 1/100) (hspace : 16 ≤ L*Real.sqrt L)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ lam ∈ spectralGood n h (naturalEdgeScale n L),
      saddleSubcriticalError lam+naturalEdgeScale n L/2 < ε := by
  classical
  let bad (n : ℕ) (lam : Fin (n+1) → ℝ) : Prop :=
    lam ∈ spectralGood n h (naturalEdgeScale n L) ∧ ε ≤ saddleSubcriticalError lam+naturalEdgeScale n L/2
  let lam (n : ℕ) : Fin (n+1) → ℝ :=
    if hb : ∃ x, bad n x then Classical.choose hb else fun i => 2-orderedJacobiGaps n i
  have hg (n) : lam n ∈ spectralGood n h (naturalEdgeScale n L) := by
    dsimp only [lam]
    split
    · exact (Classical.choose_spec ‹∃ x, bad n x›).1
    · exact spectralGood_reference n hh (naturalEdgeScale_pos n (lt_of_lt_of_le (by norm_num) hL)).le
  have hlim := (spectralGood_natural_saddle_tendsto hh hL hcost hspace lam (Eventually.of_forall hg)).add
    ((naturalEdgeScale_tendsto L).div_const 2)
  have hlim' : Tendsto (fun n => saddleSubcriticalError (lam n)+naturalEdgeScale n L/2) atTop (𝓝 0) := by
    simpa only [zero_div,add_zero] using hlim
  filter_upwards [hlim'.eventually (gt_mem_nhds hε)] with n hn
  intro x hx
  by_contra hnot
  have hex : ∃ y, bad n y := ⟨x,hx,le_of_not_gt hnot⟩
  have hh := (Classical.choose_spec hex).2
  have he : lam n = Classical.choose hex := dite_eq_left hex
  rw [he] at hn
  exact (not_lt_of_ge hh) hn

end CriticalSK

end

end OAI
