import Mathlib
import OAI.Probability.ParisiFinite.SpinTrace

namespace OAI

/-! Continuous Tilted Mean Joint. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite

lemma continuous_tiltedMean_joint {L : ℝ≥0} {f g : ℝ → ℝ}
    (hf : LipschitzWith L f) (hg : Continuous g) {M : ℝ≥0}
    (hM : ∀ x,|g x|≤M) (a : ℝ) :
    Continuous (fun p : ℝ×ℝ => tiltedMean a p.1 f g p.2) := by
  have hh := continuous_parameterTilt (S := ℝ×ℝ)
    (f := fun _ => f) (g := fun _ => g) (x := Prod.snd) (c := Prod.fst)
    (M := fun _ => (M:ℝ)) (fun _ => hf)
    (hf.continuous.comp continuous_snd) (hg.comp continuous_snd)
    continuous_snd continuous_fst continuous_const (fun _ => hM) a
  simpa only [tiltedMean,expMoment,expMass,ambientTilt,ambientMoment,ambientMass,
    smul_eq_mul,mul_comm] using hh

lemma continuous_transform_val (f : SmoothField) (a : ℝ) :
    Continuous (fun p : ℝ×ℝ => (f.transform a p.1).val p.2) := by
  have hh := continuous_parameterStep (S := ℝ×ℝ)
    (f := fun _ => f.val) (x := Prod.snd) (c := Prod.fst)
    (fun _ => f.lipschitz) (f.continuousVal.comp continuous_snd)
    continuous_snd continuous_fst a
  simpa only [SmoothField.transform,step,ambientStep,smul_eq_mul,mul_comm] using hh

lemma continuous_transform_d1 (f : SmoothField) (a : ℝ) :
    Continuous (fun p : ℝ×ℝ => (f.transform a p.1).d1 p.2) :=
  continuous_tiltedMean_joint f.lipschitz f.continuousD1 f.normD1 a

lemma continuous_transform_d2 (f : SmoothField) (a : ℝ) :
    Continuous (fun p : ℝ×ℝ => (f.transform a p.1).d2 p.2) := by
  exact (continuous_tiltedMean_joint f.lipschitz f.continuousD2 f.normD2 a).add
    (((continuous_tiltedMean_joint f.lipschitz (f.continuousD1.pow 2)
      (g := fun x => f.d1 x^2) (M := f.bound1^2) (sq_bound f.normD1) a).sub
      ((continuous_transform_d1 f a).pow 2)).const_mul a)

lemma continuous_fieldOnInterval_val (f : SmoothField) (a b : ℝ) :
    Continuous (fun p : ℝ×ℝ => (fieldOnInterval f a b p.1).val p.2) := by
  exact (continuous_transform_val f a).comp
    (((continuous_const.sub continuous_fst).sqrt).prodMk continuous_snd)

lemma continuous_fieldOnInterval_d1 (f : SmoothField) (a b : ℝ) :
    Continuous (fun p : ℝ×ℝ => (fieldOnInterval f a b p.1).d1 p.2) := by
  exact (continuous_transform_d1 f a).comp
    (((continuous_const.sub continuous_fst).sqrt).prodMk continuous_snd)

lemma continuous_fieldOnInterval_d2 (f : SmoothField) (a b : ℝ) :
    Continuous (fun p : ℝ×ℝ => (fieldOnInterval f a b p.1).d2 p.2) := by
  exact (continuous_transform_d2 f a).comp
    (((continuous_const.sub continuous_fst).sqrt).prodMk continuous_snd)

 

def fieldOnInterval_dt (f : SmoothField) (a b t x : ℝ) : ℝ :=
  if t<b then -(1/2:ℝ)*((fieldOnInterval f a b t).d2 x+
    a*((fieldOnInterval f a b t).d1 x)^2) else 0

def fieldOnInterval_timeBound (f : SmoothField) (a : ℝ) : ℝ≥0 :=
  (f.bound2+3*Real.nnabs a*f.bound1^2)/2

lemma fieldOnInterval_dt_bound (f : SmoothField) (a b t x : ℝ) :
    ‖fieldOnInterval_dt f a b t x‖≤fieldOnInterval_timeBound f a := by
  unfold fieldOnInterval_dt
  split_ifs with ht
  · rw [norm_mul,Real.norm_eq_abs,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
    have h1 := (fieldOnInterval f a b t).normD1 x
    have h2 := (fieldOnInterval f a b t).normD2 x
    have hs := sq_bound (fieldOnInterval f a b t).normD1 x
    have htri := norm_add_le ((fieldOnInterval f a b t).d2 x)
      (a*((fieldOnInterval f a b t).d1 x)^2)
    simp only [Real.norm_eq_abs,abs_mul] at htri ⊢
    change |(fieldOnInterval f a b t).d2 x| ≤
      (f.bound2:ℝ)+2*|a| *(f.bound1:ℝ)^2 at h2
    change |((fieldOnInterval f a b t).d1 x)^2| ≤ (f.bound1:ℝ)^2 at hs
    simp only [fieldOnInterval_timeBound,NNReal.coe_div,NNReal.coe_add,NNReal.coe_mul,
      NNReal.coe_pow,NNReal.coe_ofNat,Real.coe_nnabs]
    nlinarith [mul_le_mul_of_nonneg_left hs (abs_nonneg a)]
  · simp

lemma measurable_fieldOnInterval_dt (f : SmoothField) (a b : ℝ) :
    Measurable (uncurry (fieldOnInterval_dt f a b)) := by
  exact Measurable.ite (measurableSet_lt measurable_fst measurable_const)
    ((((continuous_fieldOnInterval_d2 f a b).add
      (((continuous_fieldOnInterval_d1 f a b).pow 2).const_mul a)).const_mul
      (-(1/2:ℝ))).measurable) measurable_const

lemma continuous_fieldOnInterval_dt (f : SmoothField) (a b t : ℝ) :
    Continuous (fieldOnInterval_dt f a b t) := by
  unfold fieldOnInterval_dt
  split_ifs
  · exact (((fieldOnInterval f a b t).continuousD2.add
      (((fieldOnInterval f a b t).continuousD1.pow 2).const_mul a)).const_mul _)
  · exact continuous_const

lemma integrable_fieldOnInterval_dt (f : SmoothField) (a b u v x : ℝ) :
    IntervalIntegrable (fun t => fieldOnInterval_dt f a b t x) volume u v := by
  apply (intervalIntegrable_const (c := (fieldOnInterval_timeBound f a:ℝ))).mono_fun'
    ((measurable_fieldOnInterval_dt f a b).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  exact ae_of_all _ fun t => fieldOnInterval_dt_bound f a b t x

lemma fieldOnInterval_after (f : SmoothField) (a b t x : ℝ) (ht : b≤t) :
    (fieldOnInterval f a b t).val x=f.val x := by
  have hs : Real.sqrt (b-t)=0 := Real.sqrt_eq_zero_of_nonpos (sub_nonpos.mpr ht)
  simpa only [fieldOnInterval,hs,sub_self,Real.sqrt_zero] using fieldOnInterval_right f a b x

lemma fieldOnInterval_integral_before (f : SmoothField) (a b u v x : ℝ)
    (huv : u≤v) (hv : v≤b) :
    ∫ t in u..v,fieldOnInterval_dt f a b t x=
      (fieldOnInterval f a b v).val x-(fieldOnInterval f a b u).val x := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv
    (((continuous_fieldOnInterval_val f a b).comp
      (continuous_id.prodMk continuous_const)).continuousOn)
  · intro t ht
    have hb : t<b := ht.2.trans_le hv
    simpa only [fieldOnInterval_dt,ite_eq_left hb,Function.comp_def,id_eq] using
      hasDerivAt_fieldOnInterval_time f a b t x hb
  · exact integrable_fieldOnInterval_dt f a b u v x

lemma fieldOnInterval_integral_after (f : SmoothField) (a b u v x : ℝ)
    (huv : u≤v) (hu : b≤u) :
    ∫ t in u..v,fieldOnInterval_dt f a b t x=
      (fieldOnInterval f a b v).val x-(fieldOnInterval f a b u).val x := by
  rw [fieldOnInterval_after f a b v x (hu.trans huv),fieldOnInterval_after f a b u x hu,
    sub_self]
  rw [←intervalIntegral.integral_zero (a := u) (b := v) (μ := volume) (E := ℝ)]
  apply intervalIntegral.integral_congr_ae
  exact ae_of_all _ fun t ht => by
    rw [uIoc_of_le huv] at ht
    exact ite_eq_right (not_lt.mpr (hu.trans ht.1.le))

lemma fieldOnInterval_integral_time (f : SmoothField) (a b u v x : ℝ) :
    ∫ t in u..v,fieldOnInterval_dt f a b t x=
      (fieldOnInterval f a b v).val x-(fieldOnInterval f a b u).val x := by
  wlog huv : u≤v generalizing u v
  · rw [intervalIntegral.integral_symm]
    rw [this v u (le_of_not_ge huv)]
    ring
  by_cases hv : v≤b
  · exact fieldOnInterval_integral_before f a b u v x huv hv
  by_cases hu : b≤u
  · exact fieldOnInterval_integral_after f a b u v x huv hu
  rw [←intervalIntegral.integral_add_adjacent_intervals
    (integrable_fieldOnInterval_dt f a b u b x) (integrable_fieldOnInterval_dt f a b b v x),
    fieldOnInterval_integral_before f a b u b x (le_of_not_ge hu) le_rfl,
    fieldOnInterval_integral_after f a b b v x (le_of_not_ge hv) le_rfl]
  ring

end ParisiFinite

end

end OAI
