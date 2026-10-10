import OAI.Geometry.Kahler.BasePhaseMoments

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma cosh_strict_quadratic {x : ℝ} (hx : 0 < x) : x^2 < 2*(Real.cosh x-1) := by
  have hh := (Real.hasSum_cosh x).summable.sum_le_tsum (Finset.range 3) (fun n hn => by positivity)
  rw [(Real.hasSum_cosh x).tsum_eq] at hh
  norm_num [Finset.sum_range_succ] at hh
  nlinarith [pow_pos hx 4]

lemma exists_profile_amplitude {a : ℝ} (ha : 1 < a) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ (Real.log a)^2-2*s*(Real.cosh (Real.log a)-1) < 0 := by
  have hα := Real.log_pos ha
  have hq := cosh_strict_quadratic hα
  have hd : 0 < 2*(Real.cosh (Real.log a)-1) := lt_of_le_of_lt (sq_nonneg _) hq
  have hr : (Real.log a)^2/(2*(Real.cosh (Real.log a)-1)) < 1 := (div_lt_one hd).mpr hq
  obtain ⟨s,hs,hs1⟩ := exists_between hr
  refine ⟨s,lt_of_le_of_lt (div_nonneg (sq_nonneg _) hd.le) hs,hs1,?_⟩
  have hh := (div_lt_iff₀ hd).mp hs
  nlinarith

lemma profile_transition_width {a s : ℝ} (ha : 1 < a) (ha2 : a < 2) (hs : 0 < s) (hs1 : s < 1) :
    ∃ δ : ℝ, 0 < δ ∧ s*(1-Real.exp (-(Real.log a+δ))) < Real.exp (-(Real.log a+3*δ)) := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have he : Real.exp (-Real.log a) = a⁻¹ := by rw [Real.exp_neg,Real.exp_log ha0]
  have hi : (1:ℝ)/2 < a⁻¹ := by
    have hh := (one_div_lt_one_div_of_lt ha0 ha2)
    simpa only [one_div] using hh
  have hi1 : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha
  have hzero : s*(1-Real.exp (-(Real.log a+0))) < Real.exp (-(Real.log a+3*0)) := by
    simp only [add_zero,mul_zero,he]
    nlinarith
  have hc1 : ContinuousAt (fun d : ℝ => s*(1-Real.exp (-(Real.log a+d)))) 0 := by fun_prop
  have hc2 : ContinuousAt (fun d : ℝ => Real.exp (-(Real.log a+3*d))) 0 := by fun_prop
  obtain ⟨ε,hε,heps⟩ := Metric.eventually_nhds_iff.mp (hc1.eventually_lt hc2 hzero)
  refine ⟨ε/2,by positivity,heps ?_⟩
  simp only [dist_zero_right,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < ε/2)]
  linarith

def leftCut (α δ y : ℝ) : ℝ := 1-Real.smoothTransition ((y-α)/δ)

def rightCut (α δ R y : ℝ) : ℝ :=
  Real.smoothTransition ((y-(α+2*δ))/δ) * (1-Real.smoothTransition ((y-R)/δ))

lemma leftCut_smooth (α δ : ℝ) : ContDiff ℝ ∞ (leftCut α δ) := by
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const δ))
lemma rightCut_smooth (α δ R : ℝ) : ContDiff ℝ ∞ (rightCut α δ R) := by
  exact (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const δ)).mul
    (contDiff_const.sub (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const δ)))

lemma leftCut_bounds (α δ y : ℝ) : 0 ≤ leftCut α δ y ∧ leftCut α δ y ≤ 1 := by
  unfold leftCut
  constructor <;> linarith [Real.smoothTransition.nonneg ((y-α)/δ),Real.smoothTransition.le_one ((y-α)/δ)]
lemma rightCut_bounds (α δ R y : ℝ) : 0 ≤ rightCut α δ R y ∧ rightCut α δ R y ≤ 1 := by
  have h1 := Real.smoothTransition.nonneg ((y-(α+2*δ))/δ)
  have h2 := Real.smoothTransition.le_one ((y-(α+2*δ))/δ)
  have h3 := Real.smoothTransition.nonneg ((y-R)/δ)
  have h4 := Real.smoothTransition.le_one ((y-R)/δ)
  unfold rightCut
  constructor
  · positivity
  · nlinarith

lemma leftCut_one {α δ y : ℝ} (hδ : 0 < δ) (hy : y ≤ α) : leftCut α δ y = 1 := by
  rw [leftCut, Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)]
  ring
lemma leftCut_zero {α δ y : ℝ} (hδ : 0 < δ) (hy : α+δ ≤ y) : leftCut α δ y = 0 := by
  rw [leftCut, Real.smoothTransition.one_of_one_le ((le_div_iff₀ hδ).mpr (by linarith))]
  ring
lemma rightCut_zero_left {α δ R y : ℝ} (hδ : 0 < δ) (hy : y ≤ α+2*δ) : rightCut α δ R y = 0 := by
  rw [rightCut,Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le),zero_mul]
lemma rightCut_zero_right {α δ R y : ℝ} (hδ : 0 < δ) (hy : R+δ ≤ y) : rightCut α δ R y = 0 := by
  rw [rightCut,Real.smoothTransition.one_of_one_le (x := (y-R)/δ) ((le_div_iff₀ hδ).mpr (by linarith)),sub_self,mul_zero]
lemma rightCut_one {α δ R y : ℝ} (hδ : 0 < δ) (hy : α+3*δ ≤ y) (hyR : y ≤ R) : rightCut α δ R y = 1 := by
  rw [rightCut,Real.smoothTransition.one_of_one_le ((le_div_iff₀ hδ).mpr (by linarith)),
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)]
  ring

lemma integral_exp_neg_interval (a b : ℝ) : (∫ y in a..b, Real.exp (-y)) = Real.exp (-a)-Real.exp (-b) := by
  rw [intervalIntegral.integral_comp_neg,integral_exp]

lemma cutoff_negative_mass {α δ s : ℝ} (hα : 0 ≤ α) (hδ : 0 < δ) (hs : 0 ≤ s) :
    0 ≤ s*(∫ y in 0..α+δ, Real.exp (-y)*leftCut α δ y) ∧
    s*(∫ y in 0..α+δ, Real.exp (-y)*leftCut α δ y) ≤ s*(1-Real.exp (-(α+δ))) := by
  have hc : Continuous (fun y => Real.exp (-y)*leftCut α δ y) :=
    (Real.continuous_exp.comp continuous_neg).mul (leftCut_smooth α δ).continuous
  constructor
  · apply mul_nonneg hs
    exact intervalIntegral.integral_nonneg (by linarith) (fun y hy => mul_nonneg (Real.exp_pos _).le (leftCut_bounds _ _ _).1)
  · apply mul_le_mul_of_nonneg_left _ hs
    have hh := intervalIntegral.integral_mono_on (μ := volume) (a := 0) (b := α+δ) (by linarith) (hc.intervalIntegrable _ _)
      ((Real.continuous_exp.comp continuous_neg).intervalIntegrable _ _)
      (fun y hy => mul_le_of_le_one_right (Real.exp_pos _).le (leftCut_bounds α δ y).2)
    simpa only [Function.comp_def,integral_exp_neg_interval,neg_zero,Real.exp_zero] using hh

lemma cutoff_positive_mass {α δ R : ℝ} (hα : 0 ≤ α) (hδ : 0 < δ) (hR : α+3*δ ≤ R) :
    Real.exp (-(α+3*δ))-Real.exp (-R) ≤ ∫ y in 0..R+δ, Real.exp (-y)*rightCut α δ R y := by
  have hc : Continuous (fun y => Real.exp (-y)*rightCut α δ R y) :=
    (Real.continuous_exp.comp continuous_neg).mul (rightCut_smooth α δ R).continuous
  have hh := intervalIntegral.integral_mono_interval (μ := volume) (a := α+3*δ) (b := R) (c := 0) (d := R+δ)
    (by linarith) hR (by linarith)
    (Eventually.of_forall (fun y => mul_nonneg (Real.exp_pos _).le (rightCut_bounds α δ R y).1)) (hc.intervalIntegrable _ _)
  have he : (∫ y in α+3*δ..R, Real.exp (-y)*rightCut α δ R y) = ∫ y in α+3*δ..R, Real.exp (-y) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hR] at hy
    dsimp only
    rw [rightCut_one hδ hy.1 hy.2,mul_one]
  simpa only [he,integral_exp_neg_interval] using hh

def profilePrimitive (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  Real.exp y * ∫ v in 0..y, Real.exp (-v)*f v

lemma profilePrimitive_deriv {f : ℝ → ℝ} (hf : Continuous f) (y : ℝ) :
    HasDerivAt (profilePrimitive f) (profilePrimitive f y+f y) y := by
  have hc : Continuous (fun v => Real.exp (-v)*f v) := (Real.continuous_exp.comp continuous_neg).mul hf
  have hp : HasDerivAt (fun y : ℝ => ∫ v in 0..y, Real.exp (-v)*f v) (Real.exp (-y)*f y) y := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 y)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hd : HasDerivAt (fun y : ℝ => Real.exp y * ∫ v in 0..y, Real.exp (-v)*f v)
      (Real.exp y * (∫ v in 0..y, Real.exp (-v)*f v) + Real.exp y * (Real.exp (-y)*f y)) y :=
    (Real.hasDerivAt_exp y).mul hp
  have he : Real.exp y*Real.exp (-y) = 1 := by rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
  unfold profilePrimitive
  simpa only [← mul_assoc,he,one_mul] using hd

lemma profilePrimitive_smooth {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (profilePrimitive f) := by
  have hc : ContDiff ℝ ∞ (fun v => Real.exp (-v)*f v) := Real.contDiff_exp.comp contDiff_id.neg |>.mul hf
  have hp : ∀ y : ℝ, HasDerivAt (fun y => ∫ v in 0..y, Real.exp (-v)*f v) (Real.exp (-y)*f y) y := fun y =>
    intervalIntegral.integral_hasDerivAt_right (hc.continuous.intervalIntegrable _ _)
      hc.continuous.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuous.continuousAt
  have hi : ContDiff ℝ ∞ (fun y => ∫ v in 0..y, Real.exp (-v)*f v) := by
    rw [contDiff_infty_iff_deriv]
    refine ⟨fun y => (hp y).differentiableAt,?_⟩
    rw [show (deriv fun y => ∫ v in 0..y, Real.exp (-v)*f v) = (fun y => Real.exp (-y)*f y) from funext (fun y => (hp y).deriv)]
    exact hc
  exact Real.contDiff_exp.mul hi

lemma profilePrimitive_zero (f : ℝ → ℝ) : profilePrimitive f 0 = 0 := by simp [profilePrimitive]

lemma profilePrimitive_tail {f : ℝ → ℝ} (hf : Continuous f) {E : ℝ}
    (hE : ∫ v in 0..E, Real.exp (-v)*f v = 0)
    (htail : ∀ y, E ≤ y → f y = 0) {y : ℝ} (hy : E ≤ y) : profilePrimitive f y = 0 := by
  have hc : Continuous (fun v : ℝ => Real.exp (-v)*f v) := (Real.continuous_exp.comp continuous_neg).mul hf
  have hzero : (∫ v in E..y, Real.exp (-v)*f v) = 0 := by
    calc
      _ = ∫ v in E..y, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [uIcc_of_le hy] at hv
        dsimp only
        rw [htail v hv.1,mul_zero]
      _ = 0 := by simp
  have hh := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (hc.intervalIntegrable 0 E) (hc.intervalIntegrable E y)
  rw [hE,hzero,zero_add] at hh
  simp only [profilePrimitive,← hh,mul_zero]

structure RadialProfiles (a : ℝ) where
  s : ℝ
  F : ℝ
  R : ℝ
  cutoff : ℝ
  f : ℝ → ℝ
  b : ℝ → ℝ
  s_pos : 0 < s
  s_lt : s < 1
  F_nonneg : 0 ≤ F
  F_lt : F < 1
  R_pos : 0 < R
  cutoff_pos : 0 < cutoff
  cutoff_lt : cutoff < R
  smooth_f : ContDiff ℝ ∞ f
  smooth_b : ContDiff ℝ ∞ b
  small : ∀ y, 0 ≤ y → |f y| ≤ F
  plateau : ∀ y ∈ Icc 0 (Real.log a), f y = -s
  cancellation : ∫ y in Ioi 0, Real.exp (-y)*f y = 0
  ode : ∀ y, HasDerivAt b (b y+f y) y
  b_zero : b 0 = 0
  tail : ∀ y, cutoff ≤ y → f y = 0 ∧ b y = 0
  negativity : (Real.log a)^2-2*s*(Real.cosh (Real.log a)-1) < 0

lemma exists_radialProfiles {a : ℝ} (ha : 1 < a) (ha2 : a < 2) (Rmin : ℝ) :
    ∃ p : RadialProfiles a, Rmin < p.R := by
  obtain ⟨s,hs,hs1,hsneg⟩ := exists_profile_amplitude ha
  obtain ⟨δ,hδ,hwidth⟩ := profile_transition_width ha ha2 hs hs1
  let α := Real.log a
  have hα : 0 < α := Real.log_pos ha
  let N := s*(∫ y in 0..α+δ, Real.exp (-y)*leftCut α δ y)
  have hN := cutoff_negative_mass hα.le hδ hs.le
  change 0 ≤ N ∧ N ≤ s*(1-Real.exp (-(α+δ))) at hN
  have hgap : 0 < Real.exp (-(α+3*δ))-N := by linarith
  obtain ⟨R,hR,hsmall⟩ := ((eventually_gt_atTop (α+3*δ)).and
    (Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds hgap))).exists
  let P := ∫ y in 0..R+δ, Real.exp (-y)*rightCut α δ R y
  have hPbound := cutoff_positive_mass hα.le hδ hR.le
  change Real.exp (-(α+3*δ))-Real.exp (-R) ≤ P at hPbound
  have hNP : N < P := by linarith
  have hP : 0 < P := lt_of_le_of_lt hN.1 hNP
  have hratio : 0 ≤ N/P := div_nonneg hN.1 hP.le
  have hratio1 : N/P < 1 := (div_lt_one hP).mpr hNP
  let f : ℝ → ℝ := fun y => -s*leftCut α δ y+(N/P)*rightCut α δ R y
  let E := R+δ
  have hE : 0 < E := by dsimp [E]; linarith
  have hf : ContDiff ℝ ∞ f := (contDiff_const.mul (leftCut_smooth α δ)).add (contDiff_const.mul (rightCut_smooth α δ R))
  have htail : ∀ y, E ≤ y → f y = 0 := by
    intro y hy
    dsimp [f]
    rw [leftCut_zero hδ (by dsimp [E] at hy; linarith),rightCut_zero_right hδ hy]
    ring
  have hplateau : ∀ y ∈ Icc 0 (Real.log a), f y = -s := by
    intro y hy
    dsimp [f]
    rw [leftCut_one hδ hy.2,rightCut_zero_left hδ (by linarith [hy.2])]
    ring
  have hfsmall : ∀ y, 0 ≤ y → |f y| ≤ max s (N/P) := by
    intro y hy
    by_cases hyl : y ≤ α+δ
    · have hν : rightCut α δ R y = 0 := rightCut_zero_left hδ (by linarith)
      have hχ := leftCut_bounds α δ y
      dsimp [f]
      rw [hν,mul_zero,add_zero,abs_mul,abs_neg,abs_of_pos hs,abs_of_nonneg hχ.1]
      exact (mul_le_of_le_one_right hs.le hχ.2).trans (le_max_left _ _)
    · have hχ : leftCut α δ y = 0 := leftCut_zero hδ (le_of_not_ge hyl)
      have hν := rightCut_bounds α δ R y
      dsimp [f]
      rw [hχ,mul_zero,zero_add,abs_mul,abs_of_nonneg hratio,abs_of_nonneg hν.1]
      exact (mul_le_of_le_one_right hratio hν.2).trans (le_max_right _ _)
  have hχc : Continuous (fun y => Real.exp (-y)*leftCut α δ y) :=
    (Real.continuous_exp.comp continuous_neg).mul (leftCut_smooth α δ).continuous
  have hνc : Continuous (fun y => Real.exp (-y)*rightCut α δ R y) :=
    (Real.continuous_exp.comp continuous_neg).mul (rightCut_smooth α δ R).continuous
  have hχint : (∫ y in 0..E, Real.exp (-y)*leftCut α δ y) = ∫ y in 0..α+δ, Real.exp (-y)*leftCut α δ y := by
    have hh := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (hχc.intervalIntegrable 0 (α+δ)) (hχc.intervalIntegrable (α+δ) E)
    have hz : (∫ y in α+δ..E, Real.exp (-y)*leftCut α δ y) = 0 := by
      calc
        _ = ∫ y in α+δ..E, (0:ℝ) := by
          apply intervalIntegral.integral_congr
          intro y hy
          rw [uIcc_of_le (by dsimp [E]; linarith : α+δ ≤ E)] at hy
          dsimp only
          rw [leftCut_zero hδ hy.1,mul_zero]
        _ = 0 := by simp
    rw [hz,add_zero] at hh
    exact hh.symm
  have hcancel : (∫ y in 0..E, Real.exp (-y)*f y) = 0 := by
    have he : (fun y => Real.exp (-y)*f y) =
        (fun y => -s*(Real.exp (-y)*leftCut α δ y)+(N/P)*(Real.exp (-y)*rightCut α δ R y)) := by
      funext y
      dsimp [f]
      ring
    rw [he,intervalIntegral.integral_add ((hχc.const_mul (-s)).intervalIntegrable _ _) ((hνc.const_mul (N/P)).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,hχint]
    change -s*(∫ y in 0..α+δ, Real.exp (-y)*leftCut α δ y)+(N/P)*P = 0
    rw [div_mul_cancel₀ _ (ne_of_gt hP)]
    dsimp [N]
    ring
  have himproper : (∫ y in Ioi 0, Real.exp (-y)*f y) = 0 := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := Ioc 0 E) measurableSet_Ioi (fun y hy => hy.1) (fun y hy => ?_),
      ← intervalIntegral.integral_of_le hE.le,hcancel]
    have hyE : E ≤ y := by
      by_contra hn
      exact hy.2 ⟨hy.1,(le_of_lt (lt_of_not_ge hn))⟩
    rw [htail y hyE,mul_zero]
  let p : RadialProfiles a :=
    { s := s, F := max s (N/P), R := max E Rmin+1, cutoff := E, f := f, b := profilePrimitive f
      s_pos := hs, s_lt := hs1, F_nonneg := (le_max_left s (N/P)).trans' hs.le
      F_lt := max_lt hs1 hratio1, R_pos := by linarith [le_max_left E Rmin]
      cutoff_pos := hE, cutoff_lt := by linarith [le_max_left E Rmin]
      smooth_f := hf, smooth_b := profilePrimitive_smooth hf, small := hfsmall, plateau := hplateau
      cancellation := himproper, ode := profilePrimitive_deriv hf.continuous, b_zero := profilePrimitive_zero f
      tail := fun y hy => ⟨htail y hy,profilePrimitive_tail hf.continuous hcancel htail hy⟩
      negativity := hsneg }
  refine ⟨p,?_⟩
  dsimp [p]
  linarith [le_max_right E Rmin]

end PinchedHartogs.BaseConstruction

end

end OAI
