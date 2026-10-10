import Mathlib
import OAI.Analysis.RCDHeat.HeatTest

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: DynamicalPlan, BallComparison. -/



open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
namespace RegularPointCoordinates
universe u
open Metric
open Metric
section DynamicalPlan

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

local instance pathBorel : MeasurableSpace C(Time, X) := borel _
local instance pathBorelSpace : BorelSpace C(Time, X) := ⟨rfl⟩

 
theorem measurable_path_eval (t : Time) : Measurable (fun γ : C(Time, X) => γ t) :=
  (continuous_eval_const t).measurable

 
theorem optimalPlan_endpoints (ν₀ ν₁ : Measure X) (plan : Measure C(Time, X))
    (hp : IsOptimalCoupling ν₀ ν₁ (Measure.map (fun γ => (γ 0, γ 1)) plan)) :
    Measure.map (fun γ => γ 0) plan = ν₀ ∧
      Measure.map (fun γ => γ 1) plan = ν₁ := by
  have hpairs := (measurable_path_eval (X := X) 0).prodMk (measurable_path_eval 1)
  constructor
  · simpa only [Measure.map_map measurable_fst hpairs, Function.comp_def] using hp.1
  · simpa only [Measure.map_map measurable_snd hpairs, Function.comp_def] using hp.2.1

 

theorem FullCD.support_volume_bound
    (μ : Measure X) [SigmaFinite μ] (K : ℝ) (n : ℕ)
    (hcd : FullCD μ K n) (s₀ s₁ s : Set X)
    (hs₀ : MeasurableSet s₀) (hs₁ : MeasurableSet s₁) (hs : MeasurableSet s)
    (h₀₀ : μ s₀ ≠ 0) (h₀top : μ s₀ ≠ ∞) (h₁₀ : μ s₁ ≠ 0) (h₁top : μ s₁ ≠ ∞)
    (hM₀ : FiniteSecondMoment (uniformOn μ s₀))
    (hM₁ : FiniteSecondMoment (uniformOn μ s₁))
    (N : ℝ) (hnN : (n : ℝ) ≤ N) (hN : 1 < N) (t : Time) (c : ℝ≥0∞)
    (hτ : ∀ x ∈ s₀, ∀ y ∈ s₁, c ≤ tau K N t (dist x y))
    (hmid : ∀ γ : C(Time, X), IsGeodesic γ → γ 0 ∈ s₀ → γ 1 ∈ s₁ → γ t ∈ s) :
    c * (μ s₁) ^ (1 / N) ≤ (μ s) ^ (1 / N) := by
  let := uniformOn_probability μ s₀ h₀₀ h₀top
  let := uniformOn_probability μ s₁ h₁₀ h₁top
  obtain ⟨plan, hp, hgeo, hopt, hentropy⟩ :=
    hcd (uniformOn μ s₀) (uniformOn μ s₁) inferInstance inferInstance
      (uniformOn_absolutelyContinuous μ s₀) (uniformOn_absolutelyContinuous μ s₁) hM₀ hM₁
  let := hp
  obtain ⟨hmap₀, hmap₁⟩ := optimalPlan_endpoints _ _ plan hopt
  have he₀ : ∀ᵐ γ ∂plan, γ 0 ∈ s₀ := by
    apply ae_of_ae_map (measurable_path_eval 0).aemeasurable
    rw [hmap₀]
    exact uniformOn_ae_mem μ s₀ hs₀
  have he₁ : ∀ᵐ γ ∂plan, γ 1 ∈ s₁ := by
    apply ae_of_ae_map (measurable_path_eval 1).aemeasurable
    rw [hmap₁]
    exact uniformOn_ae_mem μ s₁ hs₁
  have hrn : ∀ᵐ γ ∂plan,
      ((uniformOn μ s₁).rnDeriv μ (γ 1)) ^ (-(1 / N)) = (μ s₁) ^ (1 / N) := by
    apply ae_of_ae_map (measurable_path_eval (X := X) 1).aemeasurable
      (p := fun x => ((uniformOn μ s₁).rnDeriv μ x) ^ (-(1 / N)) = (μ s₁) ^ (1 / N))
    rw [hmap₁]
    exact uniformOn_rnDeriv_neg_power μ s₁ hs₁ N
  have hsupp : ∀ᵐ x ∂Measure.map (fun γ => γ t) plan, x ∈ s := by
    apply (ae_map_iff (measurable_path_eval t).aemeasurable hs).mpr
    filter_upwards [hgeo, he₀, he₁] with γ hg h₀ h₁
    exact hmid γ hg h₀ h₁
  let : IsProbabilityMeasure (Measure.map (fun path => path t) plan) := inferInstance
  calc
    c * (μ s₁) ^ (1 / N) = ∫⁻ _γ : C(Time, X), c * (μ s₁) ^ (1 / N) ∂plan := by
      simp
    _ ≤ ∫⁻ γ, tau K N (1 - (t : ℝ)) (dist (γ 0) (γ 1)) *
          ((uniformOn μ s₀).rnDeriv μ (γ 0)) ^ (-(1 / N)) +
        tau K N (t : ℝ) (dist (γ 0) (γ 1)) *
          ((uniformOn μ s₁).rnDeriv μ (γ 1)) ^ (-(1 / N)) ∂plan := by
      apply lintegral_mono_ae
      filter_upwards [he₀, he₁, hrn] with γ h₀ h₁ hdens
      rw [hdens]
      exact (mul_le_mul_left (hτ _ h₀ _ h₁) _).trans (le_add_left le_rfl)
    _ ≤ renyiIntegral μ (Measure.map (fun γ => γ t) plan) N := hentropy N hnN t
    _ ≤ (μ s) ^ (1 / N) := renyiIntegral_le_support_volume μ _ s hs hsupp N hN

end DynamicalPlan

 
noncomputable def midpointFloor (K N D : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (2 * Real.cosh (D * Real.sqrt (|K| / (N - 1)))))

theorem midpointFloor_pos (K N D : ℝ) : 0 < midpointFloor K N D := by
  unfold midpointFloor
  exact ENNReal.ofReal_pos.mpr (one_div_pos.mpr (mul_pos (by norm_num) (Real.cosh_pos _)))

theorem midpointFloor_ne_top (K N D : ℝ) : midpointFloor K N D ≠ ∞ :=
  ENNReal.ofReal_ne_top

theorem midpointFloor_le_half (K N D : ℝ) :
    midpointFloor K N D ≤ ENNReal.ofReal (1 / 2) := by
  apply ENNReal.ofReal_le_ofReal
  apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
  nlinarith [Real.one_le_cosh (D * Real.sqrt (|K| / (N - 1)))]

 
theorem sin_half_div_sin_ge_half (a : ℝ) (ha0 : 0 < a) (haπ : a < Real.pi) :
    (1 / 2 : ℝ) ≤ Real.sin (a / 2) / Real.sin a := by
  have hsin : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 haπ
  have hhalfsin : 0 < Real.sin (a / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hd : Real.sin a = 2 * Real.sin (a / 2) * Real.cos (a / 2) := by
    convert Real.sin_two_mul (a / 2) using 1; congr 1; ring
  apply (le_div_iff₀ hsin).mpr
  rw [hd]
  nlinarith [Real.cos_le_one (a / 2)]

 
theorem sinh_half_div_sinh (a : ℝ) (ha : 0 < a) :
    Real.sinh (a / 2) / Real.sinh a = 1 / (2 * Real.cosh (a / 2)) := by
  have hs : Real.sinh (a / 2) ≠ 0 := (Real.sinh_pos_iff.mpr (by linarith)).ne'
  have hc : Real.cosh (a / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have hd : Real.sinh a = 2 * Real.sinh (a / 2) * Real.cosh (a / 2) := by
    convert Real.sinh_two_mul (a / 2) using 1; congr 1; ring
  rw [hd]
  field_simp

 
theorem midpointFloor_le_sigma (K N D θ : ℝ) (hN : 1 < N)
    (hθ : 0 ≤ θ) (hθD : θ ≤ D) :
    midpointFloor K N D ≤ sigma K N (1 / 2) θ := by
  have hD : 0 ≤ D := hθ.trans hθD
  have hNm : 0 < N - 1 := sub_pos.mpr hN
  unfold sigma
  split_ifs with hz hconj hK
  · exact midpointFloor_le_half K N D
  · exact le_top
  · have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm (not_or.mp hz).1)
    have hroot : 0 < Real.sqrt (K / (N - 1)) :=
      Real.sqrt_pos.mpr (div_pos hK hNm)
    have ha0 : 0 < θ * Real.sqrt (K / (N - 1)) := mul_pos hθpos hroot
    have hasq : (θ * Real.sqrt (K / (N - 1))) ^ 2 = K * θ ^ 2 / (N - 1) := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg hK.le hNm.le)]
      ring
    have hasq_lt : (θ * Real.sqrt (K / (N - 1))) ^ 2 < Real.pi ^ 2 := by
      rw [hasq, div_lt_iff₀ hNm]
      nlinarith [lt_of_not_ge hconj]
    have haπ : θ * Real.sqrt (K / (N - 1)) < Real.pi := by
      nlinarith [Real.pi_pos]
    refine (midpointFloor_le_half K N D).trans (ENNReal.ofReal_le_ofReal ?_)
    convert sin_half_div_sin_ge_half (θ * Real.sqrt (K / (N - 1))) ha0 haπ using 1; congr 2; ring
  · have hKneg : K < 0 := lt_of_le_of_ne (le_of_not_gt hK) (not_or.mp hz).2
    have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm (not_or.mp hz).1)
    have hroot : 0 < Real.sqrt (-K / (N - 1)) :=
      Real.sqrt_pos.mpr (div_pos (neg_pos.mpr hKneg) hNm)
    have ha0 : 0 < θ * Real.sqrt (-K / (N - 1)) := mul_pos hθpos hroot
    have hd : 1 / 2 * θ * Real.sqrt (-K / (N - 1)) =
        (θ * Real.sqrt (-K / (N - 1))) / 2 := by ring
    rw [hd, sinh_half_div_sinh _ ha0]
    unfold midpointFloor
    rw [abs_of_neg hKneg]
    apply ENNReal.ofReal_le_ofReal
    apply one_div_le_one_div_of_le (mul_pos (by norm_num) (Real.cosh_pos _))
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (by positivity : 0 ≤ θ * Real.sqrt (-K / (N - 1)) / 2),
      abs_of_nonneg (by positivity : 0 ≤ D * Real.sqrt (-K / (N - 1)))]
    have : θ * Real.sqrt (-K / (N - 1)) ≤ D * Real.sqrt (-K / (N - 1)) :=
      mul_le_mul_of_nonneg_right hθD hroot.le
    nlinarith

 
theorem midpointFloor_le_tau (K N D θ : ℝ) (hN : 1 < N)
    (hθ : 0 ≤ θ) (hθD : θ ≤ D) :
    midpointFloor K N D ≤ tau K N (1 / 2) θ := by
  have hN0 : 0 < N := lt_trans zero_lt_one hN
  have hα : 0 ≤ 1 - 1 / N := by
    rw [sub_nonneg, div_le_one hN0]
    exact hN.le
  have hβ : 0 ≤ 1 / N := (one_div_pos.mpr hN0).le
  have he : 1 / N + (1 - 1 / N) = 1 := by ring
  unfold tau
  norm_num only [show (1 / 2 : ℝ) ≠ 0 by norm_num,
    show (1 / 2 : ℝ) ≠ 1 by norm_num, ite_false]
  calc
    midpointFloor K N D = (midpointFloor K N D) ^ (1 / N + (1 - 1 / N)) := by
      rw [he, ENNReal.rpow_one]
    _ = (midpointFloor K N D) ^ (1 / N) * (midpointFloor K N D) ^ (1 - 1 / N) :=
      ENNReal.rpow_add_of_nonneg _ _ hβ hα
    _ ≤ (ENNReal.ofReal (1 / 2)) ^ (1 / N) * (sigma K N (1 / 2) θ) ^ (1 - 1 / N) :=
      mul_le_mul' (ENNReal.rpow_le_rpow (midpointFloor_le_half K N D) hβ)
        (ENNReal.rpow_le_rpow (midpointFloor_le_sigma K N D θ hN hθ hθD) hα)


variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
 

theorem geodesic_midpoint_mem_ball (p : X) (r : ℝ) (hr : 0 < r)
    (γ : C(Time, X)) (hγ : IsGeodesic γ)
    (h₀ : γ 0 ∈ Metric.ball p (r / 8))
    (h₁ : γ 1 ∈ Metric.ball p (3 / 2 * r)) :
    γ (⟨1 / 2, by constructor <;> norm_num⟩ : Time) ∈ Metric.ball p r := by
  let t : Time := ⟨1 / 2, by constructor <;> norm_num⟩
  have he : dist (γ t) (γ 0) = 1 / 2 * dist (γ 0) (γ 1) := by
    rw [hγ]
    norm_num [t]
  have htri := dist_triangle (γ t) (γ 0) p
  have hend := dist_triangle (γ 0) p (γ 1)
  rw [dist_comm p (γ 1)] at hend
  rw [he] at htri
  change dist (γ 0) p < r / 8 at h₀
  change dist (γ 1) p < 3 / 2 * r at h₁
  change dist (γ t) p < r
  linarith

 
noncomputable def ballGrowthConstant (K N R : ℝ) : ℝ≥0∞ :=
  (midpointFloor K N (2 * R) ^ N)⁻¹

theorem ballGrowthConstant_pos (K N R : ℝ) (hN : 0 ≤ N) :
    0 < ballGrowthConstant K N R := by
  unfold ballGrowthConstant
  exact ENNReal.inv_pos.mpr (ENNReal.rpow_ne_top_of_nonneg hN (midpointFloor_ne_top K N (2 * R)))

theorem ballGrowthConstant_ne_top (K N R : ℝ) : ballGrowthConstant K N R ≠ ∞ := by
  unfold ballGrowthConstant
  exact ENNReal.inv_ne_top.mpr
    (ENNReal.rpow_pos (midpointFloor_pos _ _ _) (midpointFloor_ne_top _ _ _)).ne'

 
theorem FullCD.ball_growth
    (μ : Measure X) [SigmaFinite μ] (K : ℝ) (n : ℕ) (hcd : FullCD μ K n)
    (hpos : ∀ x : X, ∀ r : ℝ, 0 < r → 0 < μ (Metric.ball x r))
    (hfin : ∀ s : Set X, Bornology.IsBounded s → μ s < ∞)
    (hn : 2 ≤ n) (p : X) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    μ (Metric.ball p (3 / 2 * r)) ≤ ballGrowthConstant K n R * μ (Metric.ball p r) := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := lt_trans zero_lt_one hn1
  have hsmall0 : μ (Metric.ball p (r / 8)) ≠ 0 := (hpos p _ (by positivity)).ne'
  have hlarge0 : μ (Metric.ball p (3 / 2 * r)) ≠ 0 := (hpos p _ (by positivity)).ne'
  have hsmalltop : μ (Metric.ball p (r / 8)) ≠ ∞ := (hfin _ Metric.isBounded_ball).ne
  have hlargetop : μ (Metric.ball p (3 / 2 * r)) ≠ ∞ := (hfin _ Metric.isBounded_ball).ne
  have hroot := hcd.support_volume_bound μ K n
    (Metric.ball p (r / 8)) (Metric.ball p (3 / 2 * r)) (Metric.ball p r)
    Metric.isOpen_ball.measurableSet Metric.isOpen_ball.measurableSet Metric.isOpen_ball.measurableSet
    hsmall0 hsmalltop hlarge0 hlargetop
    (uniformOn_finiteSecondMoment μ _ Metric.isOpen_ball.measurableSet hsmall0 hsmalltop p (r / 8)
      (fun _ hx => le_of_lt hx))
    (uniformOn_finiteSecondMoment μ _ Metric.isOpen_ball.measurableSet hlarge0 hlargetop p (3 / 2 * r)
      (fun _ hx => le_of_lt hx))
    n le_rfl hn1 (⟨1 / 2, by constructor <;> norm_num⟩ : Time) (midpointFloor K n (2 * R))
    (by
      intro x hx y hy
      apply midpointFloor_le_tau K n (2 * R) (dist x y) hn1 dist_nonneg
      have htri := dist_triangle x p y
      rw [dist_comm p y] at htri
      change dist x p < r / 8 at hx
      change dist y p < 3 / 2 * r at hy
      linarith)
    (geodesic_midpoint_mem_ball p r hr)
  have hpow := ENNReal.rpow_le_rpow hroot hn0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hn0.le, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, one_div_mul_cancel hn0.ne', ENNReal.rpow_one,
    ENNReal.rpow_one] at hpow
  have hc0 : midpointFloor K n (2 * R) ^ (n : ℝ) ≠ 0 :=
    (ENNReal.rpow_pos (midpointFloor_pos _ _ _) (midpointFloor_ne_top _ _ _)).ne'
  have hct : midpointFloor K n (2 * R) ^ (n : ℝ) ≠ ∞ := by
    exact ENNReal.rpow_ne_top_of_nonneg hn0.le (midpointFloor_ne_top _ _ _)
  calc
    μ (Metric.ball p (3 / 2 * r)) = (midpointFloor K n (2 * R) ^ (n : ℝ))⁻¹ *
        (midpointFloor K n (2 * R) ^ (n : ℝ) * μ (Metric.ball p (3 / 2 * r))) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
    _ ≤ _ := by
      change _ ≤ (midpointFloor K n (2 * R) ^ (n : ℝ))⁻¹ * μ (Metric.ball p r)
      exact mul_le_mul_right hpow _

 
theorem FullCD.ball_growth_iterated
    (μ : Measure X) [SigmaFinite μ] (K : ℝ) (n : ℕ) (hcd : FullCD μ K n)
    (hpos : ∀ x : X, ∀ r : ℝ, 0 < r → 0 < μ (Metric.ball x r))
    (hfin : ∀ s : Set X, Bornology.IsBounded s → μ s < ∞)
    (hn : 2 ≤ n) (p : X) (r R : ℝ) (hr : 0 < r) (k : ℕ)
    (hk : (3 / 2 : ℝ) ^ k * r ≤ R) :
    μ (Metric.ball p ((3 / 2 : ℝ) ^ k * r)) ≤
      ballGrowthConstant K n R ^ k * μ (Metric.ball p r) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hrk : 0 < (3 / 2 : ℝ) ^ k * r := by positivity
    have hks : (3 / 2 : ℝ) ^ k * r ≤ (3 / 2 : ℝ) ^ (k + 1) * r := by
      rw [pow_succ]
      nlinarith
    have hkR := hks.trans hk
    have hs := hcd.ball_growth μ K n hpos hfin hn p ((3 / 2 : ℝ) ^ k * r) R hrk hkR
    have he : 3 / 2 * ((3 / 2 : ℝ) ^ k * r) = (3 / 2 : ℝ) ^ (k + 1) * r := by
      rw [pow_succ]
      ring
    rw [he] at hs
    calc
      μ (Metric.ball p ((3 / 2 : ℝ) ^ (k + 1) * r)) ≤
          ballGrowthConstant K n R * μ (Metric.ball p ((3 / 2 : ℝ) ^ k * r)) := hs
      _ ≤ ballGrowthConstant K n R * (ballGrowthConstant K n R ^ k * μ (Metric.ball p r)) :=
        mul_le_mul_right (ih hkR) _
      _ = _ := by rw [← mul_assoc, ← pow_succ']

 

theorem FullCD.uniform_ball_volume_lower_bound
    (μ : Measure X) [SigmaFinite μ] (K : ℝ) (n : ℕ) (hcd : FullCD μ K n)
    (hpos : ∀ x : X, ∀ r : ℝ, 0 < r → 0 < μ (Metric.ball x r))
    (hfin : ∀ s : Set X, Bornology.IsBounded s → μ s < ∞)
    (hn : 2 ≤ n) (p : X) (R r : ℝ) (hr : 0 < r) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ x ∈ Metric.closedBall p R, c ≤ μ (Metric.ball x r) := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((R + 1) / r) (by norm_num : (1 : ℝ) < 3 / 2)
  have hsize : R + 1 < (3 / 2 : ℝ) ^ k * r := (div_lt_iff₀ hr).mp hk
  let T := (3 / 2 : ℝ) ^ k * r
  let C := ballGrowthConstant K n T
  have hC0 : C ≠ 0 := (ballGrowthConstant_pos K n T (Nat.cast_nonneg n)).ne'
  have hCt : C ≠ ∞ := ballGrowthConstant_ne_top K n T
  have hCk0 : C ^ k ≠ 0 := pow_ne_zero _ hC0
  have hCkt : C ^ k ≠ ∞ := ENNReal.pow_ne_top hCt
  refine ⟨(C ^ k)⁻¹ * μ (Metric.ball p 1), ?_, ?_⟩
  · exact ENNReal.mul_pos (ENNReal.inv_pos.mpr hCkt).ne' (hpos p 1 (by norm_num)).ne'
  · intro x hx
    have hsub : Metric.ball p 1 ⊆ Metric.ball x T := by
      intro y hy
      have htri := dist_triangle y p x
      have hxp : dist p x ≤ R := by simpa only [Metric.mem_closedBall, dist_comm] using hx
      change dist y p < 1 at hy
      change dist y x < T
      dsimp [T]
      linarith
    have hb : μ (Metric.ball p 1) ≤ C ^ k * μ (Metric.ball x r) :=
      (measure_mono hsub).trans (hcd.ball_growth_iterated μ K n hpos hfin hn x r T hr k le_rfl)
    calc
      (C ^ k)⁻¹ * μ (Metric.ball p 1) ≤ (C ^ k)⁻¹ * (C ^ k * μ (Metric.ball x r)) :=
        mul_le_mul_right hb _
      _ = _ := by rw [← mul_assoc, ENNReal.inv_mul_cancel hCk0 hCkt, one_mul]

 

theorem compact_closedBall_of_uniform_volume_lower_bound
    [CompleteSpace X] [SeparableSpace X] (μ : Measure X)
    (hfin : ∀ s : Set X, Bornology.IsBounded s → μ s < ∞)
    (p : X) (R : ℝ)
    (hlow : ∀ r : ℝ, 0 < r → ∃ c : ℝ≥0∞, 0 < c ∧
      ∀ x ∈ Metric.closedBall p R, c ≤ μ (Metric.ball x r)) :
    IsCompact (Metric.closedBall p R) := by
  apply TotallyBounded.isCompact_of_isClosed _ Metric.isClosed_closedBall
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨c, hc, hclow⟩ := hlow (ε / 2) (half_pos hε)
  obtain ⟨S, _hSA, hS, hsmall⟩ :=
    Metric.isOpen_ball.measurableSet.exists_isCompact_sdiff_lt
      (μ := μ) (A := Metric.ball p (R + ε)) (hfin _ Metric.isBounded_ball).ne hc.ne'
  obtain ⟨t, htfin, htcover⟩ := (Metric.totallyBounded_iff.mp hS.totallyBounded) (ε / 2) (half_pos hε)
  refine ⟨t, htfin, ?_⟩
  intro x hx
  have hex : ∃ y ∈ S, dist x y < ε / 2 := by
    by_contra hn
    push Not at hn
    have hsub : Metric.ball x (ε / 2) ⊆ Metric.ball p (R + ε) \ S := by
      intro y hy
      refine ⟨?_, ?_⟩
      · have htri := dist_triangle y x p
        change dist y x < ε / 2 at hy
        change dist x p ≤ R at hx
        change dist y p < R + ε
        linarith
      · intro hyS
        have hbad := hn y hyS
        change dist y x < ε / 2 at hy
        rw [dist_comm] at hy
        exact (not_lt_of_ge hbad) hy
    exact (not_lt_of_ge ((hclow x hx).trans (measure_mono hsub))) hsmall
  obtain ⟨y, hyS, hxy⟩ := hex
  obtain ⟨z, hzt, hyz⟩ := Set.mem_iUnion₂.mp (htcover hyS)
  refine Set.mem_iUnion₂.mpr ⟨z, hzt, ?_⟩
  change dist y z < ε / 2 at hyz
  change dist x z < ε
  linarith [dist_triangle x y z]

 

theorem NoncollapsedRCD.proper (K : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) : ProperSpace X := by
  let := hX.complete
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  have : SigmaFinite (hausdorff n X) := inferInstance
  constructor
  intro p R
  apply compact_closedBall_of_uniform_volume_lower_bound (hausdorff n X) hX.finiteOnBounded p R
  intro r hr
  exact hX.cd.uniform_ball_volume_lower_bound (hausdorff n X) K n hX.fullSupport hX.finiteOnBounded hn p R r hr


end RegularPointCoordinates

end OAI
