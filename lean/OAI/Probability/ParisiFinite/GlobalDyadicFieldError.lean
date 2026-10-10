import Mathlib
import OAI.Probability.ParisiFinite.Splice

namespace OAI

/-! Global Dyadic Field Error. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite

lemma global_dyadic_field_error (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0}
    (hγ : Monotone γ) (hb : ∀ t,γ t ≤ β) (r : ℝ≥0) (hr : r<1) (n : ℕ) (x : ℝ) :
    |(finiteTimeField β hβ (dyadicSchedule γ false 0 1 n) 0 r).val x-field β γ r x| ≤
      (β:ℝ)*dyadicMesh 1 n := by
  have hh := dyadic_suffix_value_error β hβ hγ hb 0 1 n r hr x
  rw [←zero_add (r:ℝ),finiteTimeField_suffix_val]
  simpa only [zero_add,field] using hh

lemma global_dyadic_field_tendstoUniformly (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0}
    (hγ : Monotone γ) (hb : ∀ t,γ t ≤ β) (r : ℝ≥0) (hr : r<1) :
    TendstoUniformly (fun n => (finiteTimeField β hβ (dyadicSchedule γ false 0 1 n) 0 r).val)
      (field β γ r) atTop := by
  have he : Tendsto (fun n => (β:ℝ)*(dyadicMesh 1 n:ℝ)) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero] using (dyadicMesh_tendsto 1).const_mul (β:ℝ)
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [he.eventually (gt_mem_nhds hε)] with n hn x
  rw [Real.dist_eq,abs_sub_comm]
  exact (global_dyadic_field_error β hβ hγ hb r hr n x).trans_lt hn

lemma global_dyadic_gradient_tendstoUniformly (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0}
    (hγ : Monotone γ) (hb : ∀ t,γ t ≤ β) (r : ℝ≥0) (hr : r<1) :
    TendstoUniformly (fun n => (finiteTimeField β hβ (dyadicSchedule γ false 0 1 n) 0 r).d1)
      (fieldGradient β γ r) atTop := by
  obtain ⟨m,hu,hd,_,_⟩ := exists_uniform_derivative_limit
    (fun n => finiteTimeField_curvature β hβ _ (dyadicSchedule_coeff_bound hb false 0 1 n) 0 r)
    (global_dyadic_field_tendstoUniformly β hβ hγ hb r hr)
  have he : m=fieldGradient β γ r := funext fun x => (hd x).deriv.symm
  rwa [he] at hu

lemma finiteTimeCoefficient_scheduleValue (ls : Schedule) (s : ℝ) (r : ℝ≥0) :
    finiteTimeCoefficient ls s (s+r)=(scheduleValue ls r:ℝ) := by
  induction ls generalizing s r with
  | nil => rfl
  | cons l ls ih =>
    rcases l with ⟨a,d⟩
    have hc : s+(r:ℝ)<s+(d:ℝ) ↔ r<d := by exact_mod_cast add_lt_add_iff_left s
    simp only [finiteTimeCoefficient,scheduleValue,hc]
    split_ifs with hrd
    · rfl
    · have he : s+(r:ℝ)=(s+d)+(r-d:ℝ≥0) := by
        rw [NNReal.coe_sub (le_of_not_gt hrd)]
        ring
      rw [he,ih]

lemma dyadicSchedule_low_sample (γ : ℝ≥0 → ℝ≥0) (t d : ℝ≥0) (n : ℕ)
    (r : ℝ≥0) (hr : r<d) :
    ∃ y : ℝ≥0,scheduleValue (dyadicSchedule γ false t d n) r=γ y ∧
      y ≤ t+r ∧ t+r ≤ y+dyadicMesh d n := by
  induction n generalizing t d r with
  | zero =>
    refine ⟨t,?_,le_add_of_nonneg_right zero_le,?_⟩
    · simp [dyadicSchedule,scheduleValue,hr]
    · simpa only [dyadicMesh,pow_zero,div_one] using add_le_add_right hr.le t
  | succ n ih =>
    simp only [dyadicSchedule]
    by_cases hrd : r<d/2
    · rw [scheduleValue_append_left _ _ r (by rwa [dyadicSchedule_nnwidth])]
      simpa only [dyadicMesh_succ] using ih t (d/2) r hrd
    · have hd : d/2 ≤ r := le_of_not_gt hrd
      have he : d/2+(r-d/2)=r := add_tsub_cancel_of_le hd
      have ht : r-d/2<d/2 := by
        apply (tsub_lt_iff_left hd).mpr
        simpa only [add_halves] using hr
      have hlo := scheduleValue_append_right
        (dyadicSchedule γ false t (d/2) n)
        (dyadicSchedule γ false (t+d/2) (d/2) n) (r-d/2)
      rw [dyadicSchedule_nnwidth,he] at hlo
      rw [hlo]
      simpa only [dyadicMesh_succ,add_assoc,he] using ih (t+d/2) (d/2) (r-d/2) ht

lemma dyadicSchedule_low_value_tendsto (γ : ℝ≥0 → ℝ≥0) (t d r : ℝ≥0)
    (hr : r<d) (hc : ContinuousAt γ (t+r)) :
    Tendsto (fun n => scheduleValue (dyadicSchedule γ false t d n) r) atTop (𝓝 (γ (t+r))) := by
  choose y hy hlo hhi using fun n => dyadicSchedule_low_sample γ t d n r hr
  have ht : Tendsto y atTop (𝓝 (t+r)) := by
    rw [←NNReal.tendsto_coe]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa only [sub_zero] using (tendsto_const_nhds.sub (dyadicMesh_tendsto d)))
      tendsto_const_nhds
    · intro n
      have hh : (t+r:ℝ≥0) ≤ (y n:ℝ)+(dyadicMesh d n:ℝ) := by exact_mod_cast hhi n
      linarith
    · intro n; exact_mod_cast hlo n
  simpa only [hy,Function.comp_def] using hc.tendsto.comp ht

lemma dyadicSchedule_low_value_coe_tendsto (γ : ℝ≥0 → ℝ≥0) (t d r : ℝ≥0)
    (hr : r<d) (hc : ContinuousAt (fun s : ℝ => (γ (Real.toNNReal s):ℝ)) (t+r:ℝ≥0)) :
    Tendsto (fun n => (scheduleValue (dyadicSchedule γ false t d n) r:ℝ))
      atTop (𝓝 (γ (t+r):ℝ)) := by
  have hc' : ContinuousAt γ (t+r) := by
    change Tendsto γ (𝓝 (t+r)) (𝓝 (γ (t+r)))
    rw [←NNReal.tendsto_coe]
    simpa only [Function.comp_def,Real.toNNReal_coe] using
      (hc.comp NNReal.continuous_coe.continuousAt).tendsto
  exact NNReal.continuous_coe.continuousAt.tendsto.comp
    (dyadicSchedule_low_value_tendsto γ t d r hr hc')

lemma global_dyadic_coefficient_tendsto_ae {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) :
    ∀ᵐ t ∂volume,t ∈ Ioo (0:ℝ) 1 →
      Tendsto (fun n => finiteTimeCoefficient (dyadicSchedule γ false 0 1 n) 0 t)
        atTop (𝓝 (γ (Real.toNNReal t):ℝ)) := by
  let c (s : ℝ) : ℝ := γ (Real.toNNReal s)
  have hm : Monotone c := fun s t h =>
    NNReal.coe_le_coe.mpr (hγ (Real.toNNReal_le_toNNReal h))
  have hc : ∀ᵐ t ∂volume,ContinuousAt c t := by
    rw [ae_iff]
    exact hm.countable_not_continuousAt.measure_zero volume
  filter_upwards [hc] with t ht hmem
  have hr : Real.toNNReal t < 1 := by
    exact_mod_cast (show (Real.toNNReal t:ℝ)<1 by rw [Real.coe_toNNReal _ hmem.1.le];exact hmem.2)
  have hh := dyadicSchedule_low_value_coe_tendsto γ 0 1 (Real.toNNReal t) hr
    (by simpa only [zero_add,Real.coe_toNNReal _ hmem.1.le,c] using ht)
  simpa only [zero_add,←finiteTimeCoefficient_scheduleValue _ (0:ℝ),
    Real.coe_toNNReal _ hmem.1.le] using hh

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite
open ParisiPath

namespace ThirdJet
variable {f : SmoothField}

lemma continuous_transformD3_joint (j : ThirdJet f) (a : ℝ) :
    Continuous (fun p : ℝ×ℝ => j.transformD3 a p.1 p.2) := by
  have hb : ∀ y,|j.expThird a y|≤
      (j.bound3+3*Real.nnabs a*(f.bound1*f.bound2)+(Real.nnabs a)^2*f.bound1^3:ℝ≥0) := by
    intro y
    simpa only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat,Real.coe_nnabs,
      NNReal.coe_pow,sq_abs] using j.expThird_bound a y
  exact ((continuous_tiltedMean_joint f.lipschitz (j.continuous_expThird a) hb a).sub
    (((continuous_transform_d1 f a).mul (continuous_transform_d2 f a)).const_mul (3*a))).sub
      (((continuous_transform_d1 f a).pow 3).const_mul (a^2))

def slabD3 (j : ThirdJet f) (a b t x : ℝ) : ℝ :=
  j.transformD3 a (Real.sqrt (b-t)) x

lemma continuous_slabD3 (j : ThirdJet f) (a b : ℝ) :
    Continuous (uncurry (j.slabD3 a b)) :=
  (j.continuous_transformD3_joint a).comp
    (((continuous_const.sub continuous_fst).sqrt).prodMk continuous_snd)

lemma slabD3_bound (j : ThirdJet f) (a b t x : ℝ) :
    |j.slabD3 a b t x|≤(j.transform a 0).bound3 :=
  (j.transform a (Real.sqrt (b-t))).normD3 x

def gradientDt (j : ThirdJet f) (a b t x : ℝ) : ℝ :=
  if t<b then -(1/2:ℝ)*(j.slabD3 a b t x+
    2*a*(fieldOnInterval f a b t).d1 x*(fieldOnInterval f a b t).d2 x) else 0

def gradientTimeBound (j : ThirdJet f) (a : ℝ) : ℝ≥0 :=
  ((j.transform a 0).bound3+2*Real.nnabs a*f.bound1*(f.transform a 0).bound2)/2

lemma gradientDt_bound (j : ThirdJet f) (a b t x : ℝ) :
    ‖j.gradientDt a b t x‖≤j.gradientTimeBound a := by
  unfold gradientDt
  split_ifs
  · simp only [norm_mul,Real.norm_eq_abs,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
    have hp : |2*a*(fieldOnInterval f a b t).d1 x*(fieldOnInterval f a b t).d2 x|≤
        2*|a| *(f.bound1:ℝ)*(f.transform a 0).bound2 := by
      rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
      gcongr <;> first | exact (fieldOnInterval f a b t).normD1 x | exact (fieldOnInterval f a b t).normD2 x
    have hh := (abs_add_le _ _).trans (add_le_add (j.slabD3_bound a b t x) hp)
    simp only [gradientTimeBound,NNReal.coe_div,NNReal.coe_add,NNReal.coe_mul,
      NNReal.coe_ofNat,Real.coe_nnabs]
    linarith
  · simp

lemma measurable_gradientDt (j : ThirdJet f) (a b : ℝ) :
    Measurable (uncurry (j.gradientDt a b)) :=
  Measurable.ite (measurableSet_lt measurable_fst measurable_const)
    (((j.continuous_slabD3 a b).add
      (((continuous_fieldOnInterval_d1 f a b).const_mul (2*a)).mul
        (continuous_fieldOnInterval_d2 f a b))).const_mul (-(1/2:ℝ))).measurable
    measurable_const

lemma continuous_gradientDt (j : ThirdJet f) (a b t : ℝ) :
    Continuous (j.gradientDt a b t) := by
  unfold gradientDt
  split_ifs
  · exact (((j.continuous_slabD3 a b).comp (continuous_const.prodMk continuous_id)).add
      (((fieldOnInterval f a b t).continuousD1.const_mul (2*a)).mul
        (fieldOnInterval f a b t).continuousD2)).const_mul _
  · exact continuous_const

lemma hasDerivAt_fieldOnInterval_dt (j : ThirdJet f) (a b t x : ℝ) :
    HasDerivAt (fieldOnInterval_dt f a b t) (j.gradientDt a b t x) x := by
  unfold fieldOnInterval_dt gradientDt
  split_ifs
  · convert (((j.transform a (Real.sqrt (b-t))).hasD3 x).add
      (((fieldOnInterval f a b t).hasD2 x).pow 2 |>.const_mul a)).const_mul (-(1/2:ℝ)) using 1 <;>
      first | rfl | (dsimp only [slabD3,transform]; ring)
  · exact hasDerivAt_const x 0

lemma gradient_integral_time (j : ThirdJet f) (a b u v x : ℝ) :
    ∫ t in u..v,j.gradientDt a b t x=
      (fieldOnInterval f a b v).d1 x-(fieldOnInterval f a b u).d1 x := by
  have hd := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x t => fieldOnInterval_dt f a b t x)
    (F' := fun x t => j.gradientDt a b t x) (x₀ := x)
    (s := Set.univ) (bound := fun _ => (j.gradientTimeBound a:ℝ))
    (μ := volume) (a := u) (b := v) (Filter.univ_mem)
    (Eventually.of_forall fun x => ((measurable_fieldOnInterval_dt f a b).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    (integrable_fieldOnInterval_dt f a b u v x)
    (((j.measurable_gradientDt a b).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    (ae_of_all _ fun t _ x _ => j.gradientDt_bound a b t x)
    intervalIntegrable_const
    (ae_of_all _ fun t _ x _ => j.hasDerivAt_fieldOnInterval_dt a b t x)
  have he : (fun x => ∫ t in u..v,fieldOnInterval_dt f a b t x)=
      (fun x => (fieldOnInterval f a b v).val x-(fieldOnInterval f a b u).val x) :=
    funext fun x => fieldOnInterval_integral_time f a b u v x
  rw [he] at hd
  exact hd.2.unique (((fieldOnInterval f a b v).hasD1 x).sub
    ((fieldOnInterval f a b u).hasD1 x))

def slabGradientTest (j : ThirdJet f) (a b : ℝ) : TimeQuadraticTest where
  val := fun t x => (fieldOnInterval f a b t).d1 x
  d1 := fun t x => (fieldOnInterval f a b t).d2 x
  d2 := j.slabD3 a b
  dt := j.gradientDt a b
  hasD1 := fun t => (fieldOnInterval f a b t).hasD2
  hasD2 := fun t => (j.transform a (Real.sqrt (b-t))).hasD3
  continuousD2 := fun t => (j.transform a (Real.sqrt (b-t))).continuousD3
  c1 := (f.transform a 0).bound2
  c2 := (j.transform a 0).bound3
  ct := j.gradientTimeBound a
  bound1 := fun t x => by simpa only [Real.norm_eq_abs,fieldOnInterval,SmoothField.transform] using (fieldOnInterval f a b t).normD2 x
  bound2 := fun t x => by simpa only [Real.norm_eq_abs] using j.slabD3_bound a b t x
  boundT := j.gradientDt_bound a b
  measT := j.measurable_gradientDt a b
  continuousT := j.continuous_gradientDt a b
  jointD1 := ae_of_all _ fun _ _ _ => (continuous_fieldOnInterval_d2 f a b).continuousAt
  jointD2 := ae_of_all _ fun _ _ _ => (j.continuous_slabD3 a b).continuousAt
  integralT := fun u _ v _ x => (j.gradient_integral_time a b u v x).symm

end ThirdJet
end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite
open ParisiPath

namespace ThirdJet
variable {f : SmoothField}

lemma intervalIntegrable_gradientDt (j : ThirdJet f) (a b u v x : ℝ) :
    IntervalIntegrable (fun t => j.gradientDt a b t x) volume u v := by
  apply (intervalIntegrable_const (c := (j.gradientTimeBound a:ℝ))).mono_fun'
    (((j.measurable_gradientDt a b).comp (show Measurable (fun u : ℝ => (u,x)) by fun_prop)).aestronglyMeasurable)
  exact ae_of_all _ fun t => j.gradientDt_bound a b t x

lemma gradientDt_rightContinuous (j : ThirdJet f) (a b t x : ℝ) :
    ContinuousWithinAt (fun u => j.gradientDt a b u x) (Ici t) t := by
  by_cases ht : t<b
  · apply ContinuousAt.continuousWithinAt
    have hc := (((j.continuous_slabD3 a b).add
      (((continuous_fieldOnInterval_d1 f a b).const_mul (2*a)).mul
        (continuous_fieldOnInterval_d2 f a b))).const_mul (-(1/2:ℝ))).comp
      (show Continuous (fun u : ℝ => (u,x)) by fun_prop)
    apply hc.continuousAt.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht] with u hu
    exact ite_eq_left hu
  · have he : (fun u => j.gradientDt a b u x) =ᶠ[𝓝[Ici t] t] (fun _ => (0:ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact ite_eq_right (not_lt.mpr ((le_of_not_gt ht).trans hu))
    exact continuousWithinAt_const.congr_of_eventuallyEq he (he.self_of_nhdsWithin (by simp))

lemma hasDerivWithinAt_gradient_time (j : ThirdJet f) (a b t x : ℝ) :
    HasDerivWithinAt (fun u => (fieldOnInterval f a b u).d1 x)
      (j.gradientDt a b t x) (Ici t) t := by
  have hm := ((j.measurable_gradientDt a b).comp
    (show Measurable (fun u : ℝ => (u,x)) by fun_prop)).stronglyMeasurable.stronglyMeasurableAtFilter
      (l := 𝓝[Ioi t] t) (μ := volume)
  have hd := intervalIntegral.integral_hasDerivWithinAt_right
    (s := Ici t) (t := Ioi t) (j.intervalIntegrable_gradientDt a b 0 t x) hm
    ((j.gradientDt_rightContinuous a b t x).mono Ioi_subset_Ici_self)
  have he : (fun v => ∫ u in (0:ℝ)..v,j.gradientDt a b u x)=
      (fun v => (fieldOnInterval f a b v).d1 x-(fieldOnInterval f a b 0).d1 x) :=
    funext fun v => j.gradient_integral_time a b 0 v x
  rw [he] at hd
  simpa only [sub_add_cancel] using hd.add_const ((fieldOnInterval f a b 0).d1 x)

lemma gradient_square_integral_time (j : ThirdJet f) (a b u v x : ℝ) :
    ∫ t in u..v,2*(fieldOnInterval f a b t).d1 x*j.gradientDt a b t x=
      ((fieldOnInterval f a b v).d1 x)^2-((fieldOnInterval f a b u).d1 x)^2 := by
  have hm := ((continuous_fieldOnInterval_d1 f a b).comp
    (show Continuous (fun u : ℝ => (u,x)) by fun_prop))
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right (hm.pow 2).continuousOn
  · intro t _
    have hd := (j.hasDerivWithinAt_gradient_time a b t x).pow 2
    convert hd.mono (Ioi_subset_Ici_self) using 1 <;> first | rfl | norm_num
  · apply (intervalIntegrable_const (c := 2*(f.bound1:ℝ)*(j.gradientTimeBound a:ℝ))).mono_fun'
      ((hm.measurable.const_mul 2).mul ((j.measurable_gradientDt a b).comp
        (show Measurable (fun u : ℝ => (u,x)) by fun_prop))).aestronglyMeasurable
    exact ae_of_all _ fun t => by
      change ‖2*(fieldOnInterval f a b t).d1 x*j.gradientDt a b t x‖≤_
      rw [norm_mul,norm_mul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
      change 2*‖(fieldOnInterval f a b t).d1 x‖*‖j.gradientDt a b t x‖≤
        2*(f.bound1:ℝ)*(j.gradientTimeBound a:ℝ)
      exact mul_le_mul (mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs,fieldOnInterval,SmoothField.transform] using (fieldOnInterval f a b t).normD1 x) zero_le_two)
        (j.gradientDt_bound a b t x) (norm_nonneg _) (by positivity)

def squareGradientField (j : ThirdJet f) : SmoothField where
  val := fun x => (f.d1 x)^2
  d1 := fun x => 2*f.d1 x*f.d2 x
  d2 := fun x => 2*(f.d2 x)^2+2*f.d1 x*j.d3 x
  hasD1 := fun x => by
    convert (f.hasD2 x).pow 2 using 1
    first | rfl | norm_num
  hasD2 := fun x => by
    convert ((f.hasD2 x).const_mul 2).mul (j.hasD3 x) using 1
    first | rfl | ring
  continuousD2 := ((f.continuousD2.pow 2).const_mul 2).add
    ((f.continuousD1.const_mul 2).mul j.continuousD3)
  bound1 := 2*f.bound1*f.bound2
  bound2 := 2*f.bound2^2+2*f.bound1*j.bound3
  normD1 := fun x => by
    simp only [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2),NNReal.coe_mul,NNReal.coe_ofNat]
    gcongr <;> first | exact f.normD1 x | exact f.normD2 x
  normD2 := fun x => by
    apply (abs_add_le _ _).trans
    simp only [abs_mul,abs_pow,abs_of_nonneg (by norm_num : (0:ℝ)≤2),NNReal.coe_mul,
      NNReal.coe_add,NNReal.coe_ofNat,NNReal.coe_pow]
    gcongr <;> first | exact f.normD1 x | exact f.normD2 x | exact j.normD3 x

def slabSquareGradientTest (j : ThirdJet f) (a b : ℝ) : TimeQuadraticTest where
  val := fun t x => ((fieldOnInterval f a b t).d1 x)^2
  d1 := fun t x => 2*(fieldOnInterval f a b t).d1 x*(fieldOnInterval f a b t).d2 x
  d2 := fun t x => 2*((fieldOnInterval f a b t).d2 x)^2+
    2*(fieldOnInterval f a b t).d1 x*j.slabD3 a b t x
  dt := fun t x => 2*(fieldOnInterval f a b t).d1 x*j.gradientDt a b t x
  hasD1 := fun t => (j.transform a (Real.sqrt (b-t))).squareGradientField.hasD1
  hasD2 := fun t => (j.transform a (Real.sqrt (b-t))).squareGradientField.hasD2
  continuousD2 := fun t => (j.transform a (Real.sqrt (b-t))).squareGradientField.continuousD2
  c1 := (j.transform a 0).squareGradientField.bound1
  c2 := (j.transform a 0).squareGradientField.bound2
  ct := 2*f.bound1*j.gradientTimeBound a
  bound1 := fun t x => by
    simpa only [Real.norm_eq_abs,fieldOnInterval,squareGradientField,transform,SmoothField.transform]
      using (j.transform a (Real.sqrt (b-t))).squareGradientField.normD1 x
  bound2 := fun t x => by
    simpa only [Real.norm_eq_abs,fieldOnInterval,squareGradientField,transform,SmoothField.transform,slabD3]
      using (j.transform a (Real.sqrt (b-t))).squareGradientField.normD2 x
  boundT := fun t x => by
    rw [norm_mul,norm_mul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    simp only [NNReal.coe_mul,NNReal.coe_ofNat]
    gcongr
    · exact (fieldOnInterval f a b t).normD1 x
    · exact j.gradientDt_bound a b t x
  measT := ((continuous_fieldOnInterval_d1 f a b).measurable.const_mul 2).mul
    (j.measurable_gradientDt a b)
  continuousT := fun t => ((fieldOnInterval f a b t).continuousD1.const_mul 2).mul
    (j.continuous_gradientDt a b t)
  jointD1 := ae_of_all _ fun _ _ _ =>
    (((continuous_fieldOnInterval_d1 f a b).const_mul 2).mul
      (continuous_fieldOnInterval_d2 f a b)).continuousAt
  jointD2 := ae_of_all _ fun _ _ _ =>
    ((((continuous_fieldOnInterval_d2 f a b).pow 2).const_mul 2).add
      (((continuous_fieldOnInterval_d1 f a b).const_mul 2).mul
        (j.continuous_slabD3 a b))).continuousAt
  integralT := fun u _ v _ x => (j.gradient_square_integral_time a b u v x).symm

end ThirdJet
end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite
open ParisiPath

lemma SmoothField.d1_eq_of_val_eq {f g : SmoothField} (h : f.val=g.val) (x : ℝ) :
    f.d1 x=g.d1 x := by
  exact (h ▸ f.hasD1 x).unique (g.hasD1 x)

structure ScheduleGradientSquare (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (s : ℝ) where
  test : TimeQuadraticTest
  val_eq : ∀ t x,test.val t x=((finiteTimeField β hβ ls s t).d1 x)^2
  d1_eq : ∀ t x,test.d1 t x=2*(finiteTimeField β hβ ls s t).d1 x*
    (finiteTimeField β hβ ls s t).d2 x
  cancel : ∀ t,s≤t → t<s+width ls → ∀ x z,
    test.dt t x+test.d1 t x*z+test.d2 t x/2=
      ((finiteTimeField β hβ ls s t).d2 x)^2+
        2*(finiteTimeField β hβ ls s t).d1 x*(finiteTimeField β hβ ls s t).d2 x*
          (z-finiteTimeCoefficient ls s t*(finiteTimeField β hβ ls s t).d1 x)

def scheduleGradientSquare (β : ℝ≥0) (hβ : 0<β) (ls : Schedule)
    (s : ℝ) (hs : 0 ≤ s) (he : s+width ls≤1) : ScheduleGradientSquare β hβ ls s := by
  induction ls generalizing s with
  | nil =>
    refine ⟨(terminalThird β hβ).squareGradientField.staticTimeTest,
      fun _ _ => rfl,fun _ _ => rfl,?_⟩
    intro t ht ht'
    simp only [width,List.map_nil,List.sum_nil,add_zero] at ht'
    exact False.elim (not_lt_of_ge ht ht')
  | cons l ls ih =>
    rcases l with ⟨a,d⟩
    let c : ℝ := s+d
    have hc0 : 0≤c := add_nonneg hs d.coe_nonneg
    have hend : c+width ls≤1 := by
      dsimp only [c]
      rw [width_cons] at he
      linarith
    have hc1 : c≤1 := by linarith [schedule_width_nonneg ls]
    let tail := ih c hc0 hend
    let slab := (recursionThird β hβ ls).slabSquareGradientTest a c
    have hval : (fieldOnInterval (smoothRecursion β hβ ls) a c c).val=
        (finiteTimeField β hβ ls c c).val := by
      funext x
      rw [fieldOnInterval_right,finiteTimeField_start,smoothRecursion_val]
    have hmatch (x : ℝ) : slab.val c x=tail.test.val c x := by
      change ((fieldOnInterval (smoothRecursion β hβ ls) a c c).d1 x)^2=tail.test.val c x
      rw [tail.val_eq,SmoothField.d1_eq_of_val_eq hval]
    refine ⟨slab.glue tail.test c ⟨hc0,hc1⟩ hmatch,?_,?_,?_⟩
    · intro t x
      simp only [TimeQuadraticTest.glue,TimeQuadraticTest.splice,finiteTimeField,
        ThirdJet.slabSquareGradientTest,slab,c]
      split_ifs
      · rfl
      · exact tail.val_eq t x
    · intro t x
      simp only [TimeQuadraticTest.glue,TimeQuadraticTest.splice,finiteTimeField,
        ThirdJet.slabSquareGradientTest,slab,c]
      split_ifs
      · rfl
      · exact tail.d1_eq t x
    · intro t ht ht' x z
      simp only [TimeQuadraticTest.glue,TimeQuadraticTest.splice,finiteTimeField,
        finiteTimeCoefficient,ThirdJet.slabSquareGradientTest,slab,c]
      split_ifs with hcut
      · rw [ThirdJet.gradientDt,ite_eq_left hcut]
        ring
      · exact tail.cancel t (le_of_not_gt hcut) (by rw [width_cons] at ht';dsimp only [c];linarith) x z

lemma finiteTimeField_d1_start (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (s x : ℝ) :
    (finiteTimeField β hβ ls s s).d1 x=(smoothRecursion β hβ ls).d1 x :=
  SmoothField.d1_eq_of_val_eq (funext fun x =>
    (finiteTimeField_start β hβ ls s x).trans (congrFun (smoothRecursion_val β hβ ls) x).symm) x

lemma finiteTimeField_d1_after (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (s t x : ℝ)
    (ht : s+width ls≤t) : (finiteTimeField β hβ ls s t).d1 x=(terminalField β hβ).d1 x :=
  SmoothField.d1_eq_of_val_eq (funext fun x => finiteTimeField_after β hβ ls s t x ht) x

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite

lemma scheduleSuffix_ordered {β a : ℝ} {ls : Schedule}
    (h : ParisiGuerra.OrderedFrom β a ls) (r : ℝ≥0) :
    ParisiGuerra.OrderedFrom β a (scheduleSuffix ls r) := by
  induction ls generalizing a r with
  | nil => exact h
  | cons l ls ih =>
    simp only [scheduleSuffix]
    split_ifs
    · exact h
    · exact ordered_lower h.1 (ih h.2 _)

lemma SmoothField.d2_eq_of_val_eq {f g : SmoothField} (h : f.val=g.val) (x : ℝ) :
    f.d2 x=g.d2 x := by
  have hd : f.d1=g.d1 := funext (SmoothField.d1_eq_of_val_eq h)
  exact (hd ▸ f.hasD2 x).unique (g.hasD2 x)

lemma finiteTimeField_suffix_d2 (β : ℝ≥0) (hβ : 0<β) (ls : Schedule)
    (s : ℝ) (r : ℝ≥0) :
    (finiteTimeField β hβ ls s (s+r)).d2=(smoothRecursion β hβ (scheduleSuffix ls r)).d2 := by
  apply funext
  exact SmoothField.d2_eq_of_val_eq (funext fun x =>
    (finiteTimeField_suffix_val β hβ ls s r x).trans (congrFun (smoothRecursion_val β hβ _) x).symm)

lemma finiteTimeField_curvature_lipschitz (β : ℝ≥0) (hβ : 0<β) (ls : Schedule)
    (h : ParisiGuerra.OrderedFrom β 0 ls) (s : ℝ) (r : ℝ≥0) :
    LipschitzWith (5*β^2) (finiteTimeField β hβ ls s (s+r)).d2 := by
  rw [finiteTimeField_suffix_d2]
  exact recursion_curvature_lipschitz β hβ _ (scheduleSuffix_ordered h r)

lemma global_dyadic_curvature_tendstoUniformly (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0}
    (hγ : Monotone γ) (hb : ∀ t,γ t≤β) (r : ℝ≥0) (hr : r<1) :
    TendstoUniformly (fun n => (finiteTimeField β hβ (dyadicSchedule γ false 0 1 n) 0 r).d2)
      (fieldCurvature β γ r) atTop := by
  have hl (n : ℕ) : LipschitzWith (5*β^2)
      (finiteTimeField β hβ (dyadicSchedule γ false 0 1 n) 0 r).d2 := by
    simpa only [zero_add] using finiteTimeField_curvature_lipschitz β hβ _
      (ordered_lower (γ 0).coe_nonneg (ordered_upper
        (show (γ (0+1):ℝ)≤β by exact_mod_cast hb _) (dyadicSchedule_ordered hγ false 0 1 n))) 0 r
  obtain ⟨g,hu,hd,hg⟩ := exists_uniform_derivative_lipschitz_limit
    (fun n => (finiteTimeField β hβ (dyadicSchedule γ false 0 1 n) 0 r).hasD2) hl
    (global_dyadic_gradient_tendstoUniformly β hβ hγ hb r hr)
  have he : g=fieldCurvature β γ r := funext (fun x => (hd x).deriv.symm)
  rwa [he] at hu

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiPath
variable {K M : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

lemma generatorC2_bound (f : QuadraticTest) (b : Drift K M) (t x : ℝ) :
    ‖generatorC2 f b t x‖ ≤ (f.c1:ℝ)*(M:ℝ)+(f.c2:ℝ)/2 := by
  exact le_of_tendsto (mollify_generator_tendsto b f t x).norm
    (Eventually.of_forall fun n => generator_bound _ b t x)

lemma generatorC2_integrable (hW : IsBrownianReal W P) (b : Drift K M)
    (f : QuadraticTest) (t : ℝ) :
    Integrable (fun ω => generatorC2 f b t (extend (solution b (brownianPath W ω)) t)) P := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hX := aemeasurable_solution_eval b (brownianPath W) (brownianPath_aemeasurable_eval hW)
    (projIcc 0 1 zero_le_one t)
  apply Integrable.of_bound (C := (f.c1:ℝ)*(M:ℝ)+(f.c2:ℝ)/2)
  · exact (((f.continuous_d1.mul (b.lipschitz t).continuous).add
      (continuous_const.mul f.continuousD2)).measurable.comp_aemeasurable hX).aestronglyMeasurable
  · exact ae_of_all _ fun ω => generatorC2_bound f b t _

lemma timeDerivativeC2_integrable_inner (hW : IsBrownianReal W P) (b : Drift K M)
    (f : TimeQuadraticTest) (t : ℝ) :
    Integrable (fun ω => f.dt t (extend (solution b (brownianPath W ω)) t)) P := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hX := aemeasurable_solution_eval b (brownianPath W) (brownianPath_aemeasurable_eval hW)
    (projIcc 0 1 zero_le_one t)
  exact Integrable.of_bound ((f.continuousT t).measurable.comp_aemeasurable hX).aestronglyMeasurable
    (C := f.ct) (ae_of_all _ fun ω => f.boundT t _)

lemma timeGeneratorC2_aestronglyMeasurable (hW : IsBrownianReal W P)
    (b : Drift K M) (f : TimeQuadraticTest)
    (hc : ∀ᵐ t ∂volume,t ∈ Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x)) :
    AEStronglyMeasurable (timeGeneratorC2 P W b f) (volume.restrict (Ioc (0:ℝ) 1)) := by
  exact aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => timeGenerator_aestronglyMeasurable hW b (f.mollify (shrinkingBump n)) hc)
    (ae_of_all _ fun t => mollify_timeGenerator_tendsto hW b f t)

lemma timeDerivativeC2_aestronglyMeasurable (hW : IsBrownianReal W P)
    (b : Drift K M) (f : TimeQuadraticTest)
    (hc : ∀ᵐ t ∂volume,t ∈ Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x)) :
    AEStronglyMeasurable (timeDerivativeC2 P W b f) (volume.restrict (Ioc (0:ℝ) 1)) := by
  exact aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => timeDerivative_aestronglyMeasurable hW b (f.mollify (shrinkingBump n)) hc)
    (ae_of_all _ fun t => mollify_timeDerivative_tendsto hW b f t)

lemma timeGeneratorC2_intervalIntegrable (hW : IsBrownianReal W P)
    (b : Drift K M) (f : TimeQuadraticTest)
    (hc : ∀ᵐ t ∂volume,t ∈ Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x)) :
    IntervalIntegrable (timeGeneratorC2 P W b f) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  apply Integrable.of_bound (timeGeneratorC2_aestronglyMeasurable hW b f hc)
    (C := (f.c1:ℝ)*(M:ℝ)+(f.c2:ℝ)/2)
  exact ae_of_all _ fun t => le_of_tendsto (mollify_timeGenerator_tendsto hW b f t).norm
    (Eventually.of_forall fun n => expectedGenerator_bound hW b ((f.mollify (shrinkingBump n)).slice t) t)

lemma timeDerivativeC2_intervalIntegrable (hW : IsBrownianReal W P)
    (b : Drift K M) (f : TimeQuadraticTest)
    (hc : ∀ᵐ t ∂volume,t ∈ Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x)) :
    IntervalIntegrable (timeDerivativeC2 P W b f) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  apply Integrable.of_bound (timeDerivativeC2_aestronglyMeasurable hW b f hc) (C := f.ct)
  exact ae_of_all _ fun t => le_of_tendsto (mollify_timeDerivative_tendsto hW b f t).norm
    (Eventually.of_forall fun n => timeDerivative_bound hW b (f.mollify (shrinkingBump n)) t)

end ParisiPath
namespace ParisiFinite
open ParisiPath
variable {K M : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

 

theorem finite_schedule_verification (hW : IsBrownianReal W P)
    (b : Drift K M)
    (hc : ∀ᵐ t ∂volume,t ∈ Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x))
    (β : ℝ≥0) (hβ : 0 < β) (ls : Schedule) (hw : width ls = 1) :
    (∫ ω,terminal β (solution b (brownianPath W ω) ⟨1,by simp⟩) ∂P)-recursion β ls 0 =
      ∫ t in (0:ℝ)..1,∫ ω,
        (finiteTimeField β hβ ls 0 t).d1 (extend (solution b (brownianPath W ω)) t) *
          b.val t (extend (solution b (brownianPath W ω)) t) -
        (finiteTimeCoefficient ls 0 t)/2 *
          ((finiteTimeField β hβ ls 0 t).d1 (extend (solution b (brownianPath W ω)) t))^2 ∂P := by
  let r := scheduleTimeRealization β hβ ls 0 le_rfl (by rw [hw]; norm_num)
  have hh := brownian_solution_time_generator_identity_C2 hW b r.test hc
  have hj := timeGeneratorC2_intervalIntegrable hW b r.test hc
  have ht := timeDerivativeC2_intervalIntegrable hW b r.test hc
  have h1 (x : ℝ) : r.test.val 1 x = terminal β x := by
    rw [r.val_eq,finiteTimeField_after β hβ ls 0 1 x (by rw [hw]; norm_num)]
  have h0 : r.test.val 0 0 = recursion β ls 0 := by rw [r.val_eq,finiteTimeField_start]
  simp_rw [h1,h0] at hh
  rw [hh,←intervalIntegral.integral_add hj ht]
  apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
  intro t ht
  change (∫ ω,generatorC2 (r.test.slice t) b t (extend (solution b (brownianPath W ω)) t) ∂P)+
    (∫ ω,r.test.dt t (extend (solution b (brownianPath W ω)) t) ∂P)=_
  rw [←integral_add (generatorC2_integrable hW b _ t) (timeDerivativeC2_integrable_inner hW b r.test t)]
  apply integral_congr_ae
  filter_upwards [] with ω
  simp only [generatorC2,TimeQuadraticTest.slice,r.d1_eq,r.d2_eq,r.dt_eq]
  rw [finiteTimeField_PDE β hβ ls 0 t _ ht.1.le (by simpa only [hw,zero_add] using ht.2)]
  ring

end ParisiFinite

end

end OAI
