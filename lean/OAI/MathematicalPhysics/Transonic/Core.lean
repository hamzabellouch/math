import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace OAI


section

section SourceConstruction


/-!
The normalized sonic equation is regular singular. After removing its
nonresonant finite jet, the remaining problem has the form
`z g' + c g = z H(z, g)` with `c > 0`. The analytic disk space below supports
a contraction argument for this equation.
-/

noncomputable section SourceNoncomp
open Set Filter Metric MeasureTheory
open scoped Topology NNReal
namespace SepticProfile.Fuchsian

abbrev Disk := ↥(closedBall (0 : ℂ) 1)
abbrev DiskMap := C(Disk, ℂ)

def extend (f : DiskMap) (z : ℂ) : ℂ := by
  classical
  exact if h : z ∈ closedBall (0 : ℂ) 1 then f ⟨z,h⟩ else 0

@[simp] theorem extend_coe (f : DiskMap) (z : Disk) : extend f z = f z := by
  simp [extend, z.property]

@[simp] theorem extend_zero : extend (0 : DiskMap) = 0 := by
  funext z
  simp [extend]

@[simp] theorem extend_add (f g : DiskMap) : extend (f+g) = extend f + extend g := by
  funext z
  simp only [extend, Pi.add_apply]
  split <;> simp

@[simp] theorem extend_smul (c : ℂ) (f : DiskMap) :
    extend (c • f) = c • extend f := by
  funext z
  simp only [extend, Pi.smul_apply]
  split <;> simp

def analyticDisk : Submodule ℂ DiskMap where
  carrier := {f | DifferentiableOn ℂ (extend f) (ball (0 : ℂ) 1)}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    simpa using hf.add hg
  smul_mem' := by
    intro c f hf
    simpa using hf.const_smul c

 theorem analyticDisk_closed : IsClosed (analyticDisk : Set DiskMap) := by
  apply IsSeqClosed.isClosed
  intro fs f hfs hf
  change DifferentiableOn ℂ (extend f) (ball (0 : ℂ) 1)
  have hu : TendstoUniformlyOn (fun n => extend (fs n)) (extend f)
      atTop (ball (0 : ℂ) 1) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have he : ∀ᶠ n in atTop, dist (fs n) f < ε :=
      hf.eventually (ball_mem_nhds f hε)
    filter_upwards [he] with n hn z hz
    have hz' : z ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hz
    have hb := ContinuousMap.dist_apply_le_dist (f := fs n) (g := f) ⟨z,hz'⟩
    simpa [extend, hz', dist_comm] using hb.trans_lt hn
  exact hu.tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall hfs) isOpen_ball

instance : CompleteSpace analyticDisk := analyticDisk_closed.completeSpace_coe

abbrev UnitInterval := ↥(Icc (0 : ℝ) 1)

def diskScale (t : UnitInterval) (z : Disk) : Disk :=
  ⟨(t : ℝ) • (z : ℂ), by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg t.property.1]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp z.property)
      t.property.1).trans (by simpa using t.property.2)⟩

 theorem continuous_diskScale : Continuous (fun p : UnitInterval × Disk => diskScale p.1 p.2) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)

 theorem scale_mem_ball (t : UnitInterval) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    (t : ℝ) • z ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff] at hz ⊢
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
  exact (mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg z)).trans_lt (by simpa using hz)

def dilateMap (t : UnitInterval) (f : DiskMap) : DiskMap :=
  ⟨fun z => f (diskScale t z), f.continuous.comp
    (continuous_diskScale.comp (continuous_const.prodMk continuous_id))⟩

 theorem extend_dilate_on (t : UnitInterval) (f : DiskMap) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) :
    extend (dilateMap t f) z = extend f ((t : ℝ) • z) := by
  have hz' := ball_subset_closedBall hz
  have htz := ball_subset_closedBall (scale_mem_ball t hz)
  unfold extend
  rw [dite_eq_left hz', dite_eq_left htz]
  rfl

 theorem dilate_analytic (t : UnitInterval) {f : DiskMap} (hf : f ∈ analyticDisk) :
    dilateMap t f ∈ analyticDisk := by
  change DifferentiableOn ℂ (extend (dilateMap t f)) (ball (0 : ℂ) 1)
  change DifferentiableOn ℂ (extend f) (ball (0 : ℂ) 1) at hf
  have hs : DifferentiableOn ℂ (fun z : ℂ => (t : ℝ) • z) (ball 0 1) := by
    simpa only [Complex.real_smul, id_eq] using (differentiableOn_id.const_mul (t : ℂ))
  exact (hf.comp hs (fun z hz => scale_mem_ball t hz)).congr
    (fun z hz => extend_dilate_on t f hz)

def dilate (t : UnitInterval) (f : analyticDisk) : analyticDisk :=
  ⟨dilateMap t f, dilate_analytic t f.property⟩

 theorem norm_dilate_le (t : UnitInterval) (f : analyticDisk) : ‖dilate t f‖ ≤ ‖f‖ := by
  change ‖dilateMap t f‖ ≤ ‖(f : DiskMap)‖
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro z
  exact (f : DiskMap).norm_coe_le_norm (diskScale t z)

 theorem continuous_dilate (f : analyticDisk) : Continuous (fun t => dilate t f) := by
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (f : DiskMap).continuous.comp continuous_diskScale

def clip (t : ℝ) : UnitInterval := projIcc 0 1 (by norm_num) t

def radialIntegrand (c : ℝ) (f : analyticDisk) (t : ℝ) : analyticDisk :=
  (t ^ c : ℝ) • dilate (clip t) f

def radialIntegral (c : ℝ) (f : analyticDisk) : analyticDisk :=
  ∫ t : ℝ in 0..1, radialIntegrand c f t

 theorem continuous_radialIntegrand {c : ℝ} (hc : 0 ≤ c) (f : analyticDisk) :
    Continuous (radialIntegrand c f) := by
  exact (Real.continuous_rpow_const hc).smul
    ((continuous_dilate f).comp (continuous_projIcc (h := show (0 : ℝ) ≤ 1 by norm_num)))

 theorem norm_radialIntegrand_le {c t : ℝ} (hc : 0 ≤ c)
    (ht : t ∈ Icc (0 : ℝ) 1) (f : analyticDisk) :
    ‖radialIntegrand c f t‖ ≤ ‖f‖ := by
  rw [radialIntegrand, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht.1 _)]
  calc
    t ^ c * ‖dilate (clip t) f‖ ≤ 1 * ‖f‖ :=
      mul_le_mul (Real.rpow_le_one ht.1 ht.2 hc) (norm_dilate_le (clip t) f)
        (norm_nonneg (dilate (clip t) f)) (by norm_num : (0 : ℝ) ≤ 1)
    _ = ‖f‖ := one_mul _

 theorem norm_radialIntegral_le {c : ℝ} (hc : 0 ≤ c) (f : analyticDisk) :
    ‖radialIntegral c f‖ ≤ ‖f‖ := by
  change ‖∫ t : ℝ in 0..1, radialIntegrand c f t‖ ≤ ‖f‖
  have hb : ∀ t ∈ uIoc (0 : ℝ) 1, ‖radialIntegrand c f t‖ ≤ ‖f‖ := by
    intro t ht
    have ht' : t ∈ Ioc (0 : ℝ) 1 := by
      simpa only [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] using ht
    exact norm_radialIntegrand_le hc ⟨ht'.1.le, ht'.2⟩ f
  calc
    ‖∫ t : ℝ in 0..1, radialIntegrand c f t‖ ≤ ‖f‖ * |(1 : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hb
    _ = ‖f‖ := by rw [sub_zero, abs_one, mul_one]

 theorem differentiableAt_extend (f : analyticDisk) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    DifferentiableAt ℂ (extend (f : DiskMap)) z :=
  f.property.differentiableAt (isOpen_ball.mem_nhds hz)

 theorem deriv_bound (f : analyticDisk) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ‖deriv (extend (f : DiskMap)) z‖ ≤ ‖f‖ / ((1 - ‖z‖) / 2) := by
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hr : 0 < (1 - ‖z‖) / 2 := by linarith
  have hs : closedBall z ((1 - ‖z‖) / 2) ⊆ ball (0 : ℂ) 1 := by
    intro w hw
    rw [mem_ball_zero_iff]
    have hw' : ‖w-z‖ ≤ (1-‖z‖)/2 := mem_closedBall_iff_norm.mp hw
    have hb : ‖w‖ ≤ ‖w-z‖ + ‖z‖ := by
      simpa only [sub_add_cancel] using norm_add_le (w-z) z
    linarith
  rw [← Complex.cderiv_eq_deriv isOpen_ball f.property hr hs]
  apply Complex.norm_cderiv_le hr
  intro w hw
  have hw' : w ∈ closedBall (0 : ℂ) 1 :=
    ball_subset_closedBall (hs (sphere_subset_closedBall hw))
  have hn := (f : DiskMap).norm_coe_le_norm ⟨w,hw'⟩
  rw [← extend_coe] at hn
  exact hn

def derivLinear {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : analyticDisk →ₗ[ℂ] ℂ where
  toFun f := deriv (extend (f : DiskMap)) z
  map_add' f g := by
    simp only [Submodule.coe_add, extend_add]
    exact deriv_add (differentiableAt_extend f hz) (differentiableAt_extend g hz)
  map_smul' c f := by
    simp only [Submodule.coe_smul_of_tower, extend_smul, RingHom.id_apply]
    exact deriv_const_smul c (differentiableAt_extend f hz)

def derivEval {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : analyticDisk →L[ℂ] ℂ :=
  (derivLinear hz).mkContinuous (((1-‖z‖)/2)⁻¹) (by
    intro f
    simpa only [derivLinear, LinearMap.coe_mk, AddHom.coe_mk,
      div_eq_mul_inv, mul_comm] using deriv_bound f hz)

def eval (z : Disk) : analyticDisk →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ z).comp analyticDisk.subtypeL

@[simp] theorem eval_apply (z : Disk) (f : analyticDisk) : eval z f = (f : DiskMap) z := rfl

 theorem deriv_dilate (t : UnitInterval) (f : analyticDisk) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) :
    deriv (extend (dilate t f : DiskMap)) z =
      (t : ℂ) * deriv (extend (f : DiskMap)) ((t : ℂ) * z) := by
  have ht := scale_mem_ball t hz
  rw [Complex.real_smul] at ht
  have hd := (differentiableAt_extend f ht).hasDerivAt.comp z
    ((hasDerivAt_id z).const_mul (t : ℂ))
  have he : (fun w => extend (f : DiskMap) ((t : ℂ) * w)) =ᶠ[𝓝 z]
      extend (dilate t f : DiskMap) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    change extend (f : DiskMap) ((t : ℂ) * w) = extend (dilateMap t (f : DiskMap)) w
    simpa only [Complex.real_smul] using (extend_dilate_on t (f : DiskMap) hw).symm
  simpa only [mul_one, mul_comm] using (hd.congr_of_eventuallyEq he.symm).deriv

 theorem clip_coe {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : (clip t : ℝ) = t :=
  congrArg Subtype.val (projIcc_of_mem (by norm_num) ht)

 theorem radialIntegrand_eval {c t : ℝ} (f : analyticDisk)
    (ht : t ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    eval ⟨z,ball_subset_closedBall hz⟩ (radialIntegrand c f t) =
      ((t ^ c : ℝ) : ℂ) * extend (f : DiskMap) ((t : ℂ) * z) := by
  change (t ^ c : ℝ) • (f : DiskMap) (diskScale (clip t) ⟨z,ball_subset_closedBall hz⟩) = _
  rw [Complex.real_smul, ← extend_coe]
  congr 2
  change (clip t : ℝ) • z = (t : ℂ) * z
  rw [clip_coe ht, Complex.real_smul]

 theorem radialIntegrand_deriv {c t : ℝ} (f : analyticDisk)
    (ht : t ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    derivEval hz (radialIntegrand c f t) =
      ((t ^ c : ℝ) : ℂ) * (t : ℂ) * deriv (extend (f : DiskMap)) ((t : ℂ) * z) := by
  change deriv (extend ((radialIntegrand c f t : analyticDisk) : DiskMap)) z = _
  have he : extend ((radialIntegrand c f t : analyticDisk) : DiskMap) =
      ((t ^ c : ℝ) : ℂ) • extend (dilate (clip t) f : DiskMap) := by
    funext w
    classical
    by_cases hw : w ∈ closedBall (0 : ℂ) 1
    · simp only [extend, dite_eq_left hw, Pi.smul_apply]
      change (t ^ c : ℝ) • (dilate (clip t) f : DiskMap) ⟨w,hw⟩ =
        ((t ^ c : ℝ) : ℂ) • (dilate (clip t) f : DiskMap) ⟨w,hw⟩
      rw [Complex.real_smul, smul_eq_mul]
    · simp only [extend, dite_eq_right hw, Pi.smul_apply, smul_zero]
  rw [he, deriv_const_smul _ (differentiableAt_extend (dilate (clip t) f) hz),
    deriv_dilate (clip t) f hz]
  rw [clip_coe ht]
  simp only [smul_eq_mul, mul_assoc]

def radialOperator (c : ℝ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    analyticDisk →L[ℂ] ℂ :=
  z • derivEval hz + ((c + 1 : ℝ) : ℂ) • eval ⟨z,ball_subset_closedBall hz⟩

 theorem radialOperator_apply (c : ℝ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1)
    (f : analyticDisk) :
    radialOperator c hz f = z * deriv (extend (f : DiskMap)) z +
      ((c+1 : ℝ) : ℂ) * extend (f : DiskMap) z := by
  change z * deriv (extend (f : DiskMap)) z +
    ((c+1 : ℝ) : ℂ) * (f : DiskMap) ⟨z,ball_subset_closedBall hz⟩ = _
  rw [← extend_coe]

 theorem radial_primitive_deriv {c : ℝ} (f : analyticDisk) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x : ℝ => (x ^ (c+1) : ℝ) •
      extend (f : DiskMap) ((x : ℂ) * z))
      (radialOperator c hz (radialIntegrand c f t)) t := by
  have htz : (t : ℂ) * z ∈ ball (0 : ℂ) 1 := by
    simpa only [Complex.real_smul] using scale_mem_ball ⟨t,ht.1.le,ht.2.le⟩ hz
  have hf := ((differentiableAt_extend f htz).hasDerivAt.comp (t : ℂ)
    ((hasDerivAt_id (t : ℂ)).mul_const z)).comp_ofReal
  have hp := Real.hasDerivAt_rpow_const (p := c+1) (Or.inl (ne_of_gt ht.1))
  have h := hp.smul hf
  have he : radialOperator c hz (radialIntegrand c f t) =
      (t ^ (c+1) : ℝ) • (deriv (extend (f : DiskMap)) ((t : ℂ) * z) * (1 * z)) +
      ((c+1) * t ^ (c+1-1) : ℝ) • extend (f : DiskMap) ((t : ℂ) * z) := by
    rw [radialOperator, add_apply, smul_apply,
      smul_apply, radialIntegrand_eval f ⟨ht.1.le,ht.2.le⟩ hz,
      radialIntegrand_deriv f ⟨ht.1.le,ht.2.le⟩ hz]
    simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_mul, add_sub_cancel_right,
      one_mul]
    rw [Real.rpow_add_one ht.1.ne']
    push_cast
    ring
  rw [he]
  exact h

 theorem radial_primitive_continuous {c : ℝ} (hc : 0 ≤ c) (f : analyticDisk) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) :
    ContinuousOn (fun x : ℝ => (x ^ (c+1) : ℝ) •
      extend (f : DiskMap) ((x : ℂ) * z)) (Icc (0 : ℝ) 1) := by
  have hC : Continuous (fun x : ℝ => (x ^ (c+1) : ℝ) •
      eval ⟨z,ball_subset_closedBall hz⟩ (dilate (clip x) f)) :=
    (Real.continuous_rpow_const (by linarith : 0 ≤ c+1)).smul
      ((eval ⟨z,ball_subset_closedBall hz⟩).continuous.comp
        ((continuous_dilate f).comp
          (continuous_projIcc (h := show (0 : ℝ) ≤ 1 by norm_num))))
  apply hC.continuousOn.congr
  intro t ht
  apply congrArg (fun w : ℂ => (t ^ (c+1) : ℝ) • w)
  change extend (f : DiskMap) ((t : ℂ) * z) =
    (f : DiskMap) (diskScale (clip t) ⟨z,ball_subset_closedBall hz⟩)
  rw [← extend_coe]
  congr 1
  change (t : ℂ) * z = (clip t : ℝ) • z
  rw [clip_coe ht, Complex.real_smul]

 theorem radialIntegral_ode {c : ℝ} (hc : 0 ≤ c) (f : analyticDisk) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) :
    radialOperator c hz (radialIntegral c f) = extend (f : DiskMap) z := by
  have hi : IntervalIntegrable (radialIntegrand c f) volume 0 1 :=
    (continuous_radialIntegrand hc f).intervalIntegrable _ _
  have hL : IntervalIntegrable (fun t => radialOperator c hz (radialIntegrand c f t))
      volume 0 1 :=
    ((radialOperator c hz).continuous.comp (continuous_radialIntegrand hc f)).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0 : ℝ) ≤ 1) (radial_primitive_continuous hc f hz)
    (fun t ht => radial_primitive_deriv f hz ht) hL
  rw [(radialOperator c hz).intervalIntegral_comp_comm hi] at hFTC
  change radialOperator c hz (radialIntegral c f) = _ at hFTC
  simpa only [Real.one_rpow, Real.zero_rpow (by linarith : c+1 ≠ 0),
    one_smul, zero_smul, sub_zero, Complex.ofReal_one, Complex.ofReal_zero,
    one_mul, zero_mul] using hFTC

def coordinateMulMap (f : DiskMap) : DiskMap :=
  ⟨fun z => (z : ℂ) * f z, continuous_subtype_val.mul f.continuous⟩

 theorem extend_coordinateMulMap (f : DiskMap) :
    extend (coordinateMulMap f) = fun z => z * extend f z := by
  funext z
  classical
  by_cases hz : z ∈ closedBall (0 : ℂ) 1
  · simp only [extend, dite_eq_left hz]
    rfl
  · simp only [extend, dite_eq_right hz, mul_zero]

 def coordinateMul (f : analyticDisk) : analyticDisk :=
  ⟨coordinateMulMap (f : DiskMap), by
    change DifferentiableOn ℂ (extend (coordinateMulMap (f : DiskMap))) (ball 0 1)
    rw [extend_coordinateMulMap]
    exact differentiableOn_id.mul f.property⟩

 theorem norm_coordinateMul_le (f : analyticDisk) : ‖coordinateMul f‖ ≤ ‖f‖ := by
  change ‖coordinateMulMap (f : DiskMap)‖ ≤ ‖(f : DiskMap)‖
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro z
  change ‖(z : ℂ) * (f : DiskMap) z‖ ≤ ‖(f : DiskMap)‖
  rw [norm_mul]
  calc
    ‖(z : ℂ)‖ * ‖(f : DiskMap) z‖ ≤ 1 * ‖(f : DiskMap)‖ :=
      mul_le_mul (mem_closedBall_zero_iff.mp z.property)
        ((f : DiskMap).norm_coe_le_norm z) (norm_nonneg _) (by norm_num)
    _ = ‖(f : DiskMap)‖ := one_mul _

 theorem coordinateMul_sub (f g : analyticDisk) :
    coordinateMul (f-g) = coordinateMul f - coordinateMul g := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  exact mul_sub (z : ℂ) ((f : DiskMap) z) ((g : DiskMap) z)

 theorem radialIntegrand_sub (c : ℝ) (f g : analyticDisk) (t : ℝ) :
    radialIntegrand c (f-g) t = radialIntegrand c f t - radialIntegrand c g t := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  exact smul_sub (t ^ c : ℝ) ((f : DiskMap) (diskScale (clip t) z))
    ((g : DiskMap) (diskScale (clip t) z))

 theorem radialIntegral_sub {c : ℝ} (hc : 0 ≤ c) (f g : analyticDisk) :
    radialIntegral c (f-g) = radialIntegral c f - radialIntegral c g := by
  unfold radialIntegral
  simp_rw [radialIntegrand_sub]
  exact intervalIntegral.integral_sub (continuous_radialIntegrand hc f |>.intervalIntegrable _ _)
    (continuous_radialIntegrand hc g |>.intervalIntegrable _ _)

 def inverse (c : ℝ) (f : analyticDisk) : analyticDisk :=
  coordinateMul (radialIntegral c f)

 theorem norm_inverse_le {c : ℝ} (hc : 0 ≤ c) (f : analyticDisk) : ‖inverse c f‖ ≤ ‖f‖ :=
  (norm_coordinateMul_le _).trans (norm_radialIntegral_le hc f)

 theorem inverse_sub {c : ℝ} (hc : 0 ≤ c) (f g : analyticDisk) :
    inverse c (f-g) = inverse c f - inverse c g := by
  rw [inverse, radialIntegral_sub hc, coordinateMul_sub]
  rfl

 theorem inverse_ode {c : ℝ} (hc : 0 ≤ c) (f : analyticDisk) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) :
    z * deriv (extend (inverse c f : DiskMap)) z + (c : ℂ) * extend (inverse c f : DiskMap) z =
      z * extend (f : DiskMap) z := by
  have he : extend (inverse c f : DiskMap) =
      fun z => z * extend (radialIntegral c f : DiskMap) z := extend_coordinateMulMap _
  have hd : deriv (fun w => w * extend (radialIntegral c f : DiskMap) w) z =
      extend (radialIntegral c f : DiskMap) z + z * deriv (extend (radialIntegral c f : DiskMap)) z := by
    simpa only [id_eq, Pi.mul_def, one_mul] using ((hasDerivAt_id z).mul
      (differentiableAt_extend (radialIntegral c f) hz).hasDerivAt).deriv
  rw [he, hd]
  have h := radialIntegral_ode hc f hz
  rw [radialOperator_apply] at h
  rw [← h]
  push_cast
  ring

 theorem inverse_zero (c : ℝ) (f : analyticDisk) : extend (inverse c f : DiskMap) 0 = 0 := by
  rw [show extend (inverse c f : DiskMap) =
      (fun z => z * extend (radialIntegral c f : DiskMap) z) from extend_coordinateMulMap _]
  exact zero_mul _

/-- Bounds on an analytic right-hand side give an invariant fixed point of
the regular-singular integral operator. -/
 theorem exists_fuchsian_disk_invariant {c r R M L : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hR : 0 ≤ R) (hrM : r * M ≤ R) (hrL : r * L ≤ 1/2)
    (H : analyticDisk → analyticDisk)
    (hbound : ∀ f, ‖f‖ ≤ R → ‖H f‖ ≤ M)
    (hlip : ∀ f g, ‖f‖ ≤ R → ‖g‖ ≤ R → ‖H f - H g‖ ≤ L * ‖f-g‖)
    (P : Set analyticDisk) (hPc : IsClosed P) (hP0 : 0 ∈ P)
    (hP : ∀ f ∈ P, ‖f‖ ≤ R → (r : ℂ) • inverse c (H f) ∈ P) :
    ∃ f : analyticDisk, f ∈ P ∧ ‖f‖ ≤ R ∧ extend (f : DiskMap) 0 = 0 ∧
      ∀ z ∈ ball (0 : ℂ) 1,
        z * deriv (extend (f : DiskMap)) z + (c : ℂ) * extend (f : DiskMap) z =
          (r : ℂ) * z * extend (H f : DiskMap) z := by
  let T : analyticDisk → analyticDisk := fun f => (r : ℂ) • inverse c (H f)
  have hT : ∀ f, ‖f‖ ≤ R → ‖T f‖ ≤ R := by
    intro f hf
    change ‖(r : ℂ) • inverse c (H f)‖ ≤ R
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    exact (mul_le_mul_of_nonneg_left ((norm_inverse_le hc (H f)).trans (hbound f hf)) hr).trans hrM
  have hTd : ∀ f g, ‖f‖ ≤ R → ‖g‖ ≤ R → ‖T f-T g‖ ≤ (1/2 : ℝ) * ‖f-g‖ := by
    intro f g hf hg
    change ‖(r : ℂ) • inverse c (H f) - (r : ℂ) • inverse c (H g)‖ ≤ _
    rw [← smul_sub (r : ℂ) (inverse c (H f)) (inverse c (H g)), ← inverse_sub hc, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hr]
    calc
      r * ‖inverse c (H f-H g)‖ ≤ r * (L * ‖f-g‖) :=
        mul_le_mul_of_nonneg_left ((norm_inverse_le hc (H f-H g)).trans (hlip f g hf hg)) hr
      _ ≤ (1/2 : ℝ) * ‖f-g‖ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hrL (norm_nonneg _)
  have hmaps : MapsTo T (closedBall 0 R) (closedBall 0 R) := by
    intro f hf
    exact mem_closedBall_zero_iff.mpr (hT f (mem_closedBall_zero_iff.mp hf))
  have hmapsP : MapsTo T (closedBall 0 R ∩ P) (closedBall 0 R ∩ P) := by
    intro f hf
    exact ⟨hmaps hf.1, hP f hf.2 (mem_closedBall_zero_iff.mp hf.1)⟩
  have hcontract : ContractingWith (1/2 : ℝ≥0) (hmapsP.restrict T _ _) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro f g
    change dist (T f.val) (T g.val) ≤ ((1/2 : ℝ≥0) : ℝ) * dist f.val g.val
    rw [dist_eq_norm, dist_eq_norm]
    exact hTd f.val g.val (mem_closedBall_zero_iff.mp f.property.1)
      (mem_closedBall_zero_iff.mp g.property.1)
  obtain ⟨f,hf,hfix,-⟩ := ContractingWith.exists_fixedPoint'
    (isClosed_closedBall.inter hPc).isComplete hmapsP hcontract
    ⟨mem_closedBall_zero_iff.mpr (by simpa only [norm_zero] using hR), hP0⟩
    (edist_ne_top (0 : analyticDisk) (T 0))
  refine ⟨f,hf.2,mem_closedBall_zero_iff.mp hf.1,?_,?_⟩
  · have he : extend (f : DiskMap) = (r : ℂ) • extend (inverse c (H f) : DiskMap) := by
      calc
        extend (f : DiskMap) = extend (T f : DiskMap) := congrArg (fun g : analyticDisk => extend (g : DiskMap)) hfix.eq.symm
        _ = (r : ℂ) • extend (inverse c (H f) : DiskMap) := extend_smul _ _
    rw [he, Pi.smul_apply, inverse_zero, smul_zero]
  · intro z hz
    have he : extend (f : DiskMap) = (r : ℂ) • extend (inverse c (H f) : DiskMap) := by
      calc
        extend (f : DiskMap) = extend (T f : DiskMap) := congrArg (fun g : analyticDisk => extend (g : DiskMap)) hfix.eq.symm
        _ = (r : ℂ) • extend (inverse c (H f) : DiskMap) := extend_smul _ _
    rw [he, deriv_const_smul _ (differentiableAt_extend (inverse c (H f)) hz)]
    simp only [Pi.smul_apply, smul_eq_mul]
    have h := inverse_ode hc (H f) hz
    calc
      z * ((r : ℂ) * deriv (extend (inverse c (H f) : DiskMap)) z) +
          (c : ℂ) * ((r : ℂ) * extend (inverse c (H f) : DiskMap) z) =
          (r : ℂ) * (z * deriv (extend (inverse c (H f) : DiskMap)) z +
            (c : ℂ) * extend (inverse c (H f) : DiskMap) z) := by ring
      _ = (r : ℂ) * z * extend (H f : DiskMap) z := by rw [h, mul_assoc]

 theorem exists_fuchsian_disk {c r R M L : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hR : 0 ≤ R) (hrM : r * M ≤ R) (hrL : r * L ≤ 1/2)
    (H : analyticDisk → analyticDisk)
    (hbound : ∀ f, ‖f‖ ≤ R → ‖H f‖ ≤ M)
    (hlip : ∀ f g, ‖f‖ ≤ R → ‖g‖ ≤ R → ‖H f - H g‖ ≤ L * ‖f-g‖) :
    ∃ f : analyticDisk, ‖f‖ ≤ R ∧ extend (f : DiskMap) 0 = 0 ∧
      ∀ z ∈ ball (0 : ℂ) 1,
        z * deriv (extend (f : DiskMap)) z + (c : ℂ) * extend (f : DiskMap) z =
          (r : ℂ) * z * extend (H f : DiskMap) z := by
  obtain ⟨f,-,hf⟩ := exists_fuchsian_disk_invariant hc hr hR hrM hrL H hbound hlip
    univ isClosed_univ (mem_univ _) (fun _ _ _ => mem_univ _)
  exact ⟨f,hf⟩

 theorem inputBound {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    (f : analyticDisk) (hf : ‖f‖ ≤ R) (z : Disk) :
    ((r : ℂ) * (z : ℂ), (f : DiskMap) z) ∈ closedBall (0 : ℂ × ℂ) R := by
  rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff]
  refine ⟨?_, ((f : DiskMap).norm_coe_le_norm z).trans hf⟩
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp z.property) hr).trans
    (by simpa only [mul_one] using hrR)

 def composeMap {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    (h : ℂ × ℂ → ℂ) (hcont : ContinuousOn h (closedBall 0 R))
    (f : analyticDisk) (hf : ‖f‖ ≤ R) : DiskMap :=
  ⟨fun z => h ((r : ℂ) * (z : ℂ), (f : DiskMap) z),
    hcont.comp_continuous ((continuous_const.mul continuous_subtype_val).prodMk
      (f : DiskMap).continuous) (inputBound hr hrR f hf)⟩

 theorem extend_composeMap {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    (h : ℂ × ℂ → ℂ) (hcont : ContinuousOn h (closedBall 0 R))
    (f : analyticDisk) (hf : ‖f‖ ≤ R) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    extend (composeMap hr hrR h hcont f hf) z = h ((r : ℂ) * z, extend (f : DiskMap) z) := by
  have hz' := ball_subset_closedBall hz
  simp only [extend, dite_eq_left hz']
  rfl

 def composeDisk {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    (h : ℂ × ℂ → ℂ) (hdiff : DifferentiableOn ℂ h (closedBall 0 R))
    (f : analyticDisk) (hf : ‖f‖ ≤ R) : analyticDisk :=
  ⟨composeMap hr hrR h hdiff.continuousOn f hf, by
    change DifferentiableOn ℂ (extend (composeMap hr hrR h hdiff.continuousOn f hf))
      (ball 0 1)
    have hi : DifferentiableOn ℂ (fun z : ℂ => ((r : ℂ)*z, extend (f : DiskMap) z))
        (ball 0 1) := (differentiableOn_id.const_mul (r : ℂ)).prodMk f.property
    have hb : MapsTo (fun z : ℂ => ((r : ℂ)*z, extend (f : DiskMap) z))
        (ball 0 1) (closedBall 0 R) := by
      intro z hz
      have hb := inputBound hr hrR f hf ⟨z,ball_subset_closedBall hz⟩
      rw [← extend_coe] at hb
      exact hb
    exact (hdiff.comp hi hb).congr (fun z hz => extend_composeMap hr hrR h hdiff.continuousOn f hf hz)⟩

 def nonlinearDisk {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    (h : ℂ × ℂ → ℂ) (hdiff : DifferentiableOn ℂ h (closedBall 0 R))
    (f : analyticDisk) : analyticDisk := by
  classical
  exact if hf : ‖f‖ ≤ R then composeDisk hr hrR h hdiff f hf else 0

 theorem nonlinearDisk_apply {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    (h : ℂ × ℂ → ℂ) (hdiff : DifferentiableOn ℂ h (closedBall 0 R))
    (f : analyticDisk) (hf : ‖f‖ ≤ R) (z : Disk) :
    (nonlinearDisk hr hrR h hdiff f : DiskMap) z = h ((r : ℂ)*(z : ℂ), (f : DiskMap) z) := by
  classical
  simp only [nonlinearDisk, dite_eq_left hf]
  rfl

 theorem norm_nonlinearDisk_le {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) (hR : 0 ≤ R)
    (h : ℂ × ℂ → ℂ) (hdiff : DifferentiableOn ℂ h (closedBall 0 R)) {K : ℝ≥0}
    (hlip : LipschitzOnWith K h (closedBall 0 R)) (f : analyticDisk) (hf : ‖f‖ ≤ R) :
    ‖nonlinearDisk hr hrR h hdiff f‖ ≤ ‖h 0‖ + (K : ℝ)*R := by
  change ‖(nonlinearDisk hr hrR h hdiff f : DiskMap)‖ ≤ _
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro z
  rw [nonlinearDisk_apply hr hrR h hdiff f hf]
  have hl := hlip.dist_le_mul ((r : ℂ)*(z : ℂ), (f : DiskMap) z) (inputBound hr hrR f hf z) 0 (mem_closedBall_self hR)
  rw [dist_zero_right] at hl
  have hnorm := mem_closedBall_zero_iff.mp (inputBound hr hrR f hf z)
  calc
    ‖h ((r : ℂ)*(z : ℂ), (f : DiskMap) z)‖ ≤
        dist (h ((r : ℂ)*(z : ℂ), (f : DiskMap) z)) (h 0) + ‖h 0‖ := by
          simpa only [dist_eq_norm, sub_add_cancel] using
            norm_add_le (h ((r : ℂ)*(z : ℂ), (f : DiskMap) z) - h 0) (h 0)
    _ ≤ (K : ℝ) * R + ‖h 0‖ := by
      have hb := hl.trans (mul_le_mul_of_nonneg_left hnorm K.coe_nonneg)
      linarith only [hb]
    _ = ‖h 0‖ + (K : ℝ) * R := add_comm _ _

 theorem nonlinearDisk_lip {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    (h : ℂ × ℂ → ℂ) (hdiff : DifferentiableOn ℂ h (closedBall 0 R)) {K : ℝ≥0}
    (hlip : LipschitzOnWith K h (closedBall 0 R))
    (f g : analyticDisk) (hf : ‖f‖ ≤ R) (hg : ‖g‖ ≤ R) :
    ‖nonlinearDisk hr hrR h hdiff f - nonlinearDisk hr hrR h hdiff g‖ ≤
      (K : ℝ) * ‖f-g‖ := by
  change ‖(nonlinearDisk hr hrR h hdiff f : DiskMap) -
    (nonlinearDisk hr hrR h hdiff g : DiskMap)‖ ≤ _
  apply (ContinuousMap.norm_le _ (mul_nonneg K.coe_nonneg (norm_nonneg _))).2
  intro z
  simp only [ContinuousMap.sub_apply, nonlinearDisk_apply hr hrR h hdiff f hf,
    nonlinearDisk_apply hr hrR h hdiff g hg]
  have hl := hlip.dist_le_mul ((r : ℂ)*(z : ℂ), (f : DiskMap) z) (inputBound hr hrR f hf z)
    ((r : ℂ)*(z : ℂ), (g : DiskMap) z) (inputBound hr hrR g hg z)
  rw [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg), dist_eq_norm, dist_eq_norm] at hl
  exact hl.trans (mul_le_mul_of_nonneg_left (((f-g : analyticDisk) : DiskMap).norm_coe_le_norm z)
    K.coe_nonneg)

 theorem exists_scaled_fuchsian {c : ℝ} (hc : 0 ≤ c) (h : ℂ × ℂ → ℂ)
    (ha : AnalyticAt ℂ h 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ f : analyticDisk,
      extend (f : DiskMap) 0 = 0 ∧
      ∀ z ∈ ball (0 : ℂ) 1,
        z * deriv (extend (f : DiskMap)) z + (c : ℂ) * extend (f : DiskMap) z =
          (r : ℂ) * z * h ((r : ℂ)*z, extend (f : DiskMap) z) := by
  obtain ⟨K,t,ht,hKt⟩ := (ha.contDiffAt (n := 1)).exists_lipschitzOnWith
  have hnhds : t ∩ {p | AnalyticAt ℂ h p} ∈ 𝓝 (0 : ℂ × ℂ) :=
    inter_mem ht ha.eventually_analyticAt
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp hnhds
  let R : ℝ := ε/2
  have hR : 0 < R := by dsimp [R]; linarith
  have hsub : closedBall (0 : ℂ × ℂ) R ⊆ t ∩ {p | AnalyticAt ℂ h p} := by
    intro p hp
    apply hεsub
    exact mem_ball.mpr ((mem_closedBall.mp hp).trans_lt (by dsimp [R]; linarith))
  have hdiff : DifferentiableOn ℂ h (closedBall 0 R) := fun p hp =>
    (hsub hp).2.differentiableAt.differentiableWithinAt
  have hK : LipschitzOnWith K h (closedBall 0 R) := hKt.mono (fun _ hp => (hsub hp).1)
  let M : ℝ := ‖h 0‖ + (K : ℝ)*R
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let r : ℝ := min (R/(M+1)) (min R (1/(2*((K : ℝ)+1))))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r ≤ R := (min_le_right _ _).trans (min_le_left _ _)
  have hrM' : r * (M+1) ≤ R :=
    (le_div_iff₀ (by linarith : 0 < M+1)).mp (min_le_left _ _)
  have hrM : r * M ≤ R := by nlinarith
  have hrK' : r * (2*((K : ℝ)+1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 2*((K : ℝ)+1))).mp
      ((min_le_right _ _).trans (min_le_right _ _))
  have hrK : r * (K : ℝ) ≤ 1/2 := by nlinarith
  let H := nonlinearDisk hr.le hrR h hdiff
  obtain ⟨f,hf,hf0,hode⟩ := exists_fuchsian_disk hc hr.le hR.le hrM hrK H
    (fun f hf => norm_nonlinearDisk_le hr.le hrR hR.le h hdiff hK f hf)
    (fun f g hf hg => nonlinearDisk_lip hr.le hrR h hdiff hK f g hf hg)
  refine ⟨r,hr,f,hf0,?_⟩
  intro z hz
  have he : extend (H f : DiskMap) z = h ((r : ℂ)*z, extend (f : DiskMap) z) := by
    have he := nonlinearDisk_apply hr.le hrR h hdiff f hf ⟨z,ball_subset_closedBall hz⟩
    rw [← extend_coe, ← extend_coe] at he
    exact he
  rw [← he]
  exact hode z hz

def realDisk : Set analyticDisk := {f | ∀ z : Disk, (z : ℂ).im = 0 → ((f : DiskMap) z).im = 0}

 theorem realDisk_closed : IsClosed realDisk := by
  simp only [realDisk, ofPred_forall]
  exact isClosed_iInter (fun z => isClosed_iInter (fun _ =>
    isClosed_eq (Complex.continuous_im.comp (eval z).continuous) continuous_const))

 theorem realDisk_zero : (0 : analyticDisk) ∈ realDisk := by
  intro z hz
  rfl

 theorem realDisk_real_smul {f : analyticDisk} (hf : f ∈ realDisk) (r : ℝ) :
    (r : ℂ) • f ∈ realDisk := by
  intro z hz
  change ((r : ℂ) * (f : DiskMap) z).im = 0
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hf z hz, mul_zero,
    zero_mul, add_zero]

 theorem realDisk_radialIntegral {f : analyticDisk} (hf : f ∈ realDisk)
    {c : ℝ} (hc : 0 ≤ c) : radialIntegral c f ∈ realDisk := by
  intro z hz
  let L : analyticDisk →L[ℝ] ℝ := Complex.imCLM.comp ((eval z).restrictScalars ℝ)
  have he : ((radialIntegral c f : DiskMap) z).im =
      ∫ t : ℝ in 0..1, L (radialIntegrand c f t) := by
    exact (L.intervalIntegral_comp_comm ((continuous_radialIntegrand hc f).intervalIntegrable (μ := volume) 0 1)).symm
  rw [he]
  have hzero : ∀ t, L (radialIntegrand c f t) = 0 := by
    intro t
    change ((radialIntegrand c f t : DiskMap) z).im = 0
    have ht : ((diskScale (clip t) z : Disk) : ℂ).im = 0 := by
      change (((clip t : ℝ) : ℂ) * (z : ℂ)).im = 0
      simp [hz]
    change ((t ^ c : ℝ) • (f : DiskMap) (diskScale (clip t) z)).im = 0
    rw [Complex.smul_im, hf _ ht, smul_zero]
  simp only [hzero, intervalIntegral.integral_zero]

 theorem realDisk_inverse {f : analyticDisk} (hf : f ∈ realDisk)
    {c : ℝ} (hc : 0 ≤ c) : inverse c f ∈ realDisk := by
  intro z hz
  change ((z : ℂ) * (radialIntegral c f : DiskMap) z).im = 0
  simp only [Complex.mul_im, realDisk_radialIntegral hf hc z hz, hz, mul_zero, zero_mul,
    add_zero]

 theorem exists_scaled_real_fuchsian {c : ℝ} (hc : 0 ≤ c) (h : ℂ × ℂ → ℂ)
    (ha : AnalyticAt ℂ h 0)
    (hreal : ∀ p : ℂ × ℂ, p.1.im = 0 → p.2.im = 0 → (h p).im = 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ f : analyticDisk, f ∈ realDisk ∧
      extend (f : DiskMap) 0 = 0 ∧
      ∀ z ∈ ball (0 : ℂ) 1,
        z * deriv (extend (f : DiskMap)) z + (c : ℂ) * extend (f : DiskMap) z =
          (r : ℂ) * z * h ((r : ℂ)*z, extend (f : DiskMap) z) := by
  obtain ⟨K,t,ht,hKt⟩ := (ha.contDiffAt (n := 1)).exists_lipschitzOnWith
  have hnhds : t ∩ {p | AnalyticAt ℂ h p} ∈ 𝓝 (0 : ℂ × ℂ) :=
    inter_mem ht ha.eventually_analyticAt
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp hnhds
  let R : ℝ := ε/2
  have hR : 0 < R := by dsimp [R]; linarith
  have hsub : closedBall (0 : ℂ × ℂ) R ⊆ t ∩ {p | AnalyticAt ℂ h p} := by
    intro p hp
    apply hεsub
    exact mem_ball.mpr ((mem_closedBall.mp hp).trans_lt (by dsimp [R]; linarith))
  have hdiff : DifferentiableOn ℂ h (closedBall 0 R) := fun p hp =>
    (hsub hp).2.differentiableAt.differentiableWithinAt
  have hK : LipschitzOnWith K h (closedBall 0 R) := hKt.mono (fun _ hp => (hsub hp).1)
  let M : ℝ := ‖h 0‖ + (K : ℝ)*R
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let r : ℝ := min (R/(M+1)) (min R (1/(2*((K : ℝ)+1))))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r ≤ R := (min_le_right _ _).trans (min_le_left _ _)
  have hrM' : r * (M+1) ≤ R :=
    (le_div_iff₀ (by linarith : 0 < M+1)).mp (min_le_left _ _)
  have hrM : r * M ≤ R := by nlinarith
  have hrK' : r * (2*((K : ℝ)+1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 2*((K : ℝ)+1))).mp
      ((min_le_right _ _).trans (min_le_right _ _))
  have hrK : r * (K : ℝ) ≤ 1/2 := by nlinarith
  let H := nonlinearDisk hr.le hrR h hdiff
  obtain ⟨f,hfreal,hf,hf0,hode⟩ := exists_fuchsian_disk_invariant hc hr.le hR.le hrM hrK H
    (fun f hf => norm_nonlinearDisk_le hr.le hrR hR.le h hdiff hK f hf)
    (fun f g hf hg => nonlinearDisk_lip hr.le hrR h hdiff hK f g hf hg)
    realDisk realDisk_closed realDisk_zero (by
      intro f hf hfR
      apply realDisk_real_smul _ r
      apply realDisk_inverse _ hc
      intro z hz
      change ((nonlinearDisk hr.le hrR h hdiff f : DiskMap) z).im = 0
      rw [nonlinearDisk_apply hr.le hrR h hdiff f hfR]
      exact hreal _ (by simp [hz]) (hf z hz))
  refine ⟨r,hr,f,hfreal,hf0,?_⟩
  intro z hz
  have he : extend (H f : DiskMap) z = h ((r : ℂ)*z, extend (f : DiskMap) z) := by
    have he := nonlinearDisk_apply hr.le hrR h hdiff f hf ⟨z,ball_subset_closedBall hz⟩
    rw [← extend_coe, ← extend_coe] at he
    exact he
  rw [← he]
  exact hode z hz

/-- Real analytic local solvability of the post-jet regular-singular equation.
The radius is constructed and positive; existence is not an input hypothesis. -/
 theorem exists_real_fuchsian_germ {c : ℝ} (hc : 0 ≤ c) (h : ℂ × ℂ → ℂ)
    (ha : AnalyticAt ℂ h 0)
    (hreal : ∀ p : ℂ × ℂ, p.1.im = 0 → p.2.im = 0 → (h p).im = 0) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧ F 0 = 0 ∧
      (∀ x : ℝ, (F x).im = 0) ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), z * deriv F z + (c : ℂ)*F z = z*h (z,F z) := by
  obtain ⟨r,hr,f,hfr,hf0,hode⟩ := exists_scaled_real_fuchsian hc h ha hreal
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  let F : ℂ → ℂ := fun z => extend (f : DiskMap) (z/(r : ℂ))
  have hmem {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) : z/(r : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact (div_lt_one hr).mpr hz
  refine ⟨F,?_,?_,?_,?_⟩
  · have han : AnalyticAt ℂ (extend (f : DiskMap)) (0/(r : ℂ)) := by
      simpa only [zero_div] using f.property.analyticAt (ball_mem_nhds (0 : ℂ) (by norm_num : (0:ℝ)<1))
    exact han.comp (f := fun z : ℂ => z/(r : ℂ)) (x := 0)
      (analyticAt_id.div_const (c := (r : ℂ)))
  · simpa only [F, zero_div] using hf0
  · intro x
    dsimp [F]
    unfold extend
    split
    · apply hfr
      simp
    · rfl
  · filter_upwards [ball_mem_nhds (0 : ℂ) hr] with z hz
    have hm := hmem hz
    have he : deriv F z = deriv (extend (f : DiskMap)) (z/(r : ℂ)) / (r : ℂ) := by
      simpa only [F, Function.comp_def, id_eq, one_div, div_eq_mul_inv, one_mul] using
        (((differentiableAt_extend f hm).hasDerivAt).comp z
          ((hasDerivAt_id z).div_const (r : ℂ))).deriv
    have hd := hode (z/(r : ℂ)) hm
    have hzdiv : (r : ℂ)*(z/(r : ℂ)) = z := by field_simp
    rw [hzdiv] at hd
    change z * deriv F z + (c : ℂ)*extend (f : DiskMap) (z/(r : ℂ)) = _
    rw [he]
    (convert hd using 1; ring)

end SepticProfile.Fuchsian


/- Sonic jet algebra over an arbitrary commutative ring. -/
noncomputable section SourceNoncomp
namespace SepticProfile.Formal
open PowerSeries

variable {K : Type*} [CommRing K]
abbrev Series (K : Type*) := PowerSeries K

def z : Series K := 1 + X

def prefactor (sigma : K) : Series K := z * (1 - C sigma*z^2)
def den (sigma : K) (u : Series K) : Series K := prefactor sigma * (1-u^2)
def r (c : K) (u : Series K) : Series K := 1-C c*u^2
def t (kappa : K) (u : Series K) : Series K := C kappa*z*(1-u^2)+3*(z-u)
def residual (sigma kappa c : K) (u : Series K) : Series K :=
  den sigma u * derivative u - r c u * t kappa u

def lin (sigma kappa c : K) (u : Series K) : Series K :=
  -2*prefactor sigma*u*derivative u +
    2*C c*u*t kappa u + r c u*(2*C kappa*z*u+3)

lemma coefficient_shift_zero (N M : ℕ) (h : N < M) (p : Series K) :
    coeff N (p*X^M) = 0 := by
  rw [coeff_mul_X_pow']
  simp only [not_le.mpr h, ite_false]

lemma coefficient_shift_same (N : ℕ) (p : Series K) :
    coeff N (p*X^N) = constantCoeff p := by
  simpa using coeff_mul_X_pow p N 0

lemma coefficient_monomial_second_order (n : ℕ) (a : K) (p : Series K) :
    coeff (n+2) ((C a*X^(n+2))^2*p) = 0 := by
  rw [mul_pow, ← pow_mul]
  have he : (C a ^ 2 * X ^ ((n + 2) * 2)) * p =
      (C a ^ 2 * p) * X ^ ((n + 2) * 2) := by ring
  rw [he]
  exact coefficient_shift_zero _ _ (by omega) _

lemma derivative_monomial (n : ℕ) (a : K) :
    derivative (C a*X^(n+1)) = C ((n+1)*a)*X^n := by
  simp only [Derivation.leibniz, derivative_C, derivative_pow, derivative_X]
  simp only [smul_eq_mul, mul_zero, add_zero, mul_one, Nat.add_sub_cancel]
  rw [← map_natCast C, ← mul_assoc, ← map_mul]
  congr 2
  push_cast
  ring

lemma coefficient_monomial_derivative (n : ℕ) (a : K) (p : Series K) :
    coeff (n+2) ((C a*X^(n+2))*derivative (C a*X^(n+2))*p) = 0 := by
  rw [show n+2 = (n+1)+1 by omega, derivative_monomial]
  have he : C a * X ^ (n + 1 + 1) * (C ((↑(n + 1) + 1) * a) * X ^ (n + 1)) * p =
      (C a * C ((↑(n + 1) + 1)*a)*p)*X^((n+1+1)+(n+1)) := by
    rw [pow_add]
    ring
  rw [he]
  exact coefficient_shift_zero _ _ (by omega) _

lemma residual_linearization (sigma kappa c : K) (u d : Series K) :
    residual sigma kappa c (u+d) - residual sigma kappa c u =
      den sigma u * derivative d + lin sigma kappa c u * d +
      d^2 * (-prefactor sigma * derivative u +
        C c*t kappa u + 2*C c*u*(-2*C kappa*z*u-3) +
        r c u*C kappa*z +
        (-2*C c*u*C kappa*z + C c*(-2*C kappa*z*u-3))*d -
        C c*C kappa*z*d^2) +
      d*derivative d*(-prefactor sigma*(2*u+d)) := by
  simp only [residual, den, lin, r, t, map_add]
  ring

lemma residual_monomial_perturbation (sigma kappa c : K) (u : Series K)
    (n : ℕ) (a : K) :
    coeff (n+2) (residual sigma kappa c (u+C a*X^(n+2))) -
      coeff (n+2) (residual sigma kappa c u) =
        coeff (n+2) (den sigma u * derivative (C a*X^(n+2))) +
        coeff (n+2) (lin sigma kappa c u * (C a*X^(n+2))) := by
  rw [← map_sub, residual_linearization]
  simp only [map_add, coefficient_monomial_second_order,
    coefficient_monomial_derivative, add_zero]


lemma coeff_den_one (sigma : K) {u : Series K} {s : K}
    (hu0 : constantCoeff u = 1) (hu1 : coeff 1 u = s) :
    coeff 1 (den sigma u) = -2*(1-sigma)*s := by
  simp only [den, prefactor, z, coeff_one_mul, coeff_one_pow, map_sub,
    map_add, map_mul, map_pow, constantCoeff_C, hu0, hu1]
  norm_num
  ring

lemma coeff_lin_zero (sigma kappa c : K) {u : Series K} {s : K}
    (hu0 : constantCoeff u = 1) (hu1 : coeff 1 u = s) :
    constantCoeff (lin sigma kappa c u) =
      -2*(1-sigma)*s + (1-c)*(2*kappa+3) := by
  have hd : constantCoeff (derivative u) = s := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_derivative]
    simpa using hu1
  simp only [lin, prefactor, z, r, t, map_add, map_sub, map_mul, map_neg,
    map_pow, constantCoeff_C, constantCoeff_one, constantCoeff_X, map_ofNat, hu0, hd]
  ring

lemma coeff_den_derivative_monomial (sigma : K) (u : Series K)
    (s : K) (hu0 : constantCoeff u = 1) (hu1 : coeff 1 u = s)
    (n : ℕ) (a : K) :
    coeff (n+2) (den sigma u * derivative (C a*X^(n+2))) =
      ((n+2)*a)*(-2*(1-sigma)*s) := by
  rw [show n+2 = (n+1)+1 by omega, derivative_monomial]
  rw [show den sigma u * (C ((↑(n+1)+1)*a)*X^(n+1)) =
    C ((↑(n+1)+1)*a)*(den sigma u*X^(n+1)) by ring]
  rw [coeff_C_mul, show n+1+1 = 1+(n+1) by omega, coeff_mul_X_pow,
    coeff_den_one sigma hu0 hu1]
  push_cast
  ring

lemma coeff_lin_monomial (sigma kappa c : K) (u : Series K)
    (s : K) (hu0 : constantCoeff u = 1) (hu1 : coeff 1 u = s)
    (n : ℕ) (a : K) :
    coeff (n+2) (lin sigma kappa c u * (C a*X^(n+2))) =
      a*(-2*(1-sigma)*s+(1-c)*(2*kappa+3)) := by
  rw [show lin sigma kappa c u * (C a*X^(n+2)) =
    C a*(lin sigma kappa c u*X^(n+2)) by ring]
  rw [coeff_C_mul, coefficient_shift_same, coeff_lin_zero sigma kappa c hu0 hu1]

/-- The exact nth-jet coefficient includes all nonlinear terms in the
normalization. Its multiplier vanishes at an integral slope ratio. -/
lemma coefficient_step (sigma kappa c : K) (u : Series K) (s : K)
    (hu0 : constantCoeff u = 1) (hu1 : coeff 1 u = s) (n : ℕ) (a : K) :
    coeff (n+2) (residual sigma kappa c (u+C a*X^(n+2))) =
      coeff (n+2) (residual sigma kappa c u) +
        ((1-c)*(2*kappa+3)-2*(1-sigma)*s*(n+3))*a := by
  have h := residual_monomial_perturbation sigma kappa c u n a
  rw [coeff_den_derivative_monomial sigma u s hu0 hu1,
    coeff_lin_monomial sigma kappa c u s hu0 hu1] at h
  linear_combination h

/- Coefficient locality at the singular point.  Although differentiating costs
one coefficient, its multiplier has zero constant term, so the nth residual
coefficient only depends on coefficients through n. -/
def Agree (n : ℕ) (u v : Series K) : Prop :=
  ∀ i ≤ n, coeff i u = coeff i v

lemma Agree.refl (n : ℕ) (u : Series K) : Agree n u u := fun _ _ => rfl

lemma Agree.add {n : ℕ} {u v p q : Series K} (h : Agree n u v) (h' : Agree n p q) :
    Agree n (u+p) (v+q) := by
  intro i hi
  simp only [map_add, h i hi, h' i hi]

lemma Agree.sub {n : ℕ} {u v p q : Series K} (h : Agree n u v) (h' : Agree n p q) :
    Agree n (u-p) (v-q) := by
  intro i hi
  simp only [map_sub, h i hi, h' i hi]

lemma Agree.mul {n : ℕ} {u v p q : Series K} (h : Agree n u v) (h' : Agree n p q) :
    Agree n (u*p) (v*q) := by
  intro i hi
  simp only [coeff_mul]
  apply Finset.sum_congr rfl
  intro ab hab
  have hh := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  rw [h ab.1 (by omega), h' ab.2 (by omega)]

lemma Agree.pow {n : ℕ} {u v : Series K} (h : Agree n u v) (k : ℕ) :
    Agree n (u^k) (v^k) := by
  induction k with
  | zero => simpa only [pow_zero] using Agree.refl n (1 : Series K)
  | succ k hk => simpa only [pow_succ] using hk.mul h

lemma Agree.mul_derivative {n : ℕ} {u v p q : Series K}
    (h : Agree n u v) (h' : Agree n p q)
    (hp : constantCoeff p = 0) (hq : constantCoeff q = 0) :
    Agree n (p*derivative u) (q*derivative v) := by
  intro i hi
  simp only [coeff_mul]
  apply Finset.sum_congr rfl
  intro ab hab
  have hh := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  by_cases hz : ab.1 = 0
  · simp only [hz, coeff_zero_eq_constantCoeff_apply, hp, hq, zero_mul]
  · rw [h' ab.1 (by omega), coeff_derivative, coeff_derivative,
      h (ab.2+1) (by omega)]

lemma residual_agree (sigma kappa c : K) {n : ℕ} {u v : Series K}
    (h : Agree n u v) (hu : constantCoeff u = 1) (hv : constantCoeff v = 1) :
    Agree n (residual sigma kappa c u) (residual sigma kappa c v) := by
  have hn : Agree n (1-u^2) (1-v^2) := (Agree.refl n 1).sub (h.pow 2)
  have hd : Agree n (den sigma u) (den sigma v) :=
    (Agree.refl n (prefactor sigma)).mul hn
  have hd0 : constantCoeff (den sigma u) = 0 := by simp [den, hu]
  have hd0' : constantCoeff (den sigma v) = 0 := by simp [den, hv]
  have hr : Agree n (r c u) (r c v) :=
    (Agree.refl n 1).sub ((Agree.refl n (C c)).mul (h.pow 2))
  have ht : Agree n (t kappa u) (t kappa v) :=
    ((Agree.refl n (C kappa*z)).mul hn).add
      ((Agree.refl n 3).mul ((Agree.refl n z).sub h))
  exact (h.mul_derivative hd hd0 hd0').sub (hr.mul ht)

def before (n : ℕ) (u : Series K) : Series K :=
  mk fun i => if i < n then coeff i u else 0

lemma coeff_before (n : ℕ) (u : Series K) (i : ℕ) :
    coeff i (before n u) = if i < n then coeff i u else 0 := by simp [before]

lemma before_zero (n : ℕ) (u : Series K) (hn : 0 < n) :
    constantCoeff (before n u) = constantCoeff u := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_before, ite_eq_left hn,
    coeff_zero_eq_constantCoeff_apply]

lemma before_one (n : ℕ) (u : Series K) (hn : 1 < n) :
    coeff 1 (before n u) = coeff 1 u := by rw [coeff_before, ite_eq_left hn]

lemma agree_before_next (n : ℕ) (u : Series K) :
    Agree n u (before n u + C (coeff n u)*X^n) := by
  intro i hi
  rw [map_add, coeff_before, coeff_C_mul, coeff_X_pow]
  by_cases h : i = n
  · subst i; simp
  · simp [h, show i < n by omega]

lemma step_at (sigma kappa c : K) (u : Series K) (s : K)
    (hu0 : constantCoeff u = 1) (hu1 : coeff 1 u = s) (n : ℕ) :
    coeff (n+2) (residual sigma kappa c u) =
      coeff (n+2) (residual sigma kappa c (before (n+2) u)) +
        ((1-c)*(2*kappa+3)-2*(1-sigma)*s*(n+3))*coeff (n+2) u := by
  have h0 : constantCoeff (before (n+2) u) = 1 := by
    rw [before_zero _ _ (by omega), hu0]
  have h1 : coeff 1 (before (n+2) u) = s := by
    rw [before_one _ _ (by omega), hu1]
  have hv : constantCoeff (before (n+2) u+C (coeff (n+2) u)*X^(n+2)) = 1 := by
    simp [h0]
  rw [(residual_agree sigma kappa c (agree_before_next (n+2) u) hu0 hv) _ le_rfl,
    coefficient_step sigma kappa c (before (n+2) u) s h0 h1]

end SepticProfile.Formal


namespace SepticProfile.SourceJets
open Polynomial

variable {K : Type*} [Field K]

/-- The literal normalized source polynomial residual, expanded about z=1. -/
def residualP (sigma kappa c : K) (u : Polynomial K) : Polynomial K :=
  (1+X)*(1-C sigma*(1+X)^2)*(1-u^2)*u.derivative -
    (1-C c*u^2)*(C kappa*(1+X)*(1-u^2)+3*((1+X)-u))

 theorem coe_residualP (sigma kappa c : K) (u : Polynomial K) :
    (residualP sigma kappa c u : PowerSeries K) = Formal.residual sigma kappa c u := by
  simp only [residualP, Formal.residual, Formal.den, Formal.prefactor, Formal.z,
    Formal.r, Formal.t, coe_sub, coe_mul, coe_add, coe_pow, coe_one, coe_X, coe_C,
    ← PowerSeries.derivative_coe]
  have h3 : ((3 : Polynomial K) : PowerSeries K) = 3 := by
    rw [show (3 : Polynomial K) = 1+1+1 by ring, coe_add, coe_add, coe_one]
    ring
  rw [h3]

 theorem coeff_residual_one (sigma kappa c : K) {u : PowerSeries K} {s : K}
    (hu0 : PowerSeries.constantCoeff u=1) (hu1 : PowerSeries.coeff 1 u=s) :
    PowerSeries.coeff 1 (Formal.residual sigma kappa c u) =
      -2*(1-sigma)*s^2+(1-c)*(2*kappa+3)*s-3*(1-c) := by
  have hd : PowerSeries.constantCoeff (PowerSeries.derivative u)=s := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
    simpa using hu1
  simp only [Formal.residual, Formal.den, Formal.prefactor, Formal.z, Formal.r,
    Formal.t, map_sub, map_add, map_mul, map_pow, PowerSeries.coeff_one_mul,
    PowerSeries.coeff_one_pow, PowerSeries.constantCoeff_C, map_ofNat, hu0, hu1, hd]
  norm_num
  ring

 theorem constantCoeff_residual (sigma kappa c : K) {u : PowerSeries K}
    (hu0 : PowerSeries.constantCoeff u=1) :
    PowerSeries.constantCoeff (Formal.residual sigma kappa c u) = 0 := by
  simp [Formal.residual, Formal.den, Formal.prefactor, Formal.z, Formal.r,
    Formal.t, hu0]

/-- Construct all required finite sonic jets at a nonresonant weak slope.
There is no assumed formal series. The zero multiplier at a resonance is
explicitly excluded; this is why the resonant parameter cannot be used as a
selected analytic profile parameter. -/
 theorem exists_finite_jet (sigma kappa c s : K)
    (hs : 2*(1-sigma)*s^2-(1-c)*(2*kappa+3)*s+3*(1-c)=0)
    (N : ℕ)
    (hne : ∀ n < N, (1-c)*(2*kappa+3)-2*(1-sigma)*s*(n+3) ≠ 0) :
    ∃ p : Polynomial K, p.coeff 0=1 ∧ p.coeff 1=s ∧
      ∀ i ≤ N+1, (residualP sigma kappa c p).coeff i=0 := by
  induction N with
  | zero =>
    let p : Polynomial K := 1+C s*X
    have hp0 : p.coeff 0=1 := by simp [p]
    have hp1 : p.coeff 1=s := by simp [p, Polynomial.coeff_one]
    have hp0' : PowerSeries.constantCoeff (p : PowerSeries K)=1 := by simpa using hp0
    have hp1' : PowerSeries.coeff 1 (p : PowerSeries K)=s := by simpa using hp1
    refine ⟨p,hp0,hp1,?_⟩
    intro i hi
    have hi' : i=0 ∨ i=1 := by omega
    rcases hi' with rfl | rfl
    · rw [← Polynomial.coeff_coe, coe_residualP, PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact constantCoeff_residual sigma kappa c hp0'
    · rw [← Polynomial.coeff_coe, coe_residualP, coeff_residual_one sigma kappa c hp0' hp1']
      linear_combination -hs
  | succ n ih =>
    obtain ⟨p,hp0,hp1,hp⟩ := ih (fun i hi => hne i (by omega))
    let d : K := (1-c)*(2*kappa+3)-2*(1-sigma)*s*(n+3)
    have hd : d ≠ 0 := hne n (by omega)
    let a : K := -(residualP sigma kappa c p).coeff (n+2)/d
    let q : Polynomial K := p+C a*X^(n+2)
    have hq0 : q.coeff 0=1 := by simp [q,hp0]
    have hq1 : q.coeff 1=s := by simp [q,hp1]
    have hp0' : PowerSeries.constantCoeff (p : PowerSeries K)=1 := by simpa using hp0
    have hp1' : PowerSeries.coeff 1 (p : PowerSeries K)=s := by simpa using hp1
    have hq0' : PowerSeries.constantCoeff (q : PowerSeries K)=1 := by simpa using hq0
    have hag : Formal.Agree (n+1) (q : PowerSeries K) (p : PowerSeries K) := by
      intro i hi
      simp only [Polynomial.coeff_coe]
      change q.coeff i = p.coeff i
      simp [q, show ¬i=n+2 by omega]
    refine ⟨q,hq0,hq1,?_⟩
    intro i hi
    by_cases hi' : i=n+2
    · subst i
      have he := Formal.coefficient_step sigma kappa c (p : PowerSeries K) s hp0' hp1' n a
      have hq : (q : PowerSeries K) = (p : PowerSeries K)+PowerSeries.C a*PowerSeries.X^(n+2) := by
        simp [q]
      rw [← hq, ← coe_residualP, ← coe_residualP, Polynomial.coeff_coe,
        Polynomial.coeff_coe] at he
      rw [he]
      change (residualP sigma kappa c p).coeff (n+2) + d * a = 0
      dsimp only [a]
      (field_simp [hd]; ring)
    · have he := Formal.residual_agree sigma kappa c hag hq0' hp0' i (by omega)
      rw [← coe_residualP, ← coe_residualP, Polynomial.coeff_coe,
        Polynomial.coeff_coe] at he
      exact he.trans (hp i (by omega))

 theorem exists_finite_jet_divisible (sigma kappa c s : K)
    (hs : 2*(1-sigma)*s^2-(1-c)*(2*kappa+3)*s+3*(1-c)=0)
    (N : ℕ)
    (hne : ∀ n < N, (1-c)*(2*kappa+3)-2*(1-sigma)*s*(n+3) ≠ 0) :
    ∃ p : Polynomial K, p.coeff 0=1 ∧ p.coeff 1=s ∧
      (X : Polynomial K)^(N+2) ∣ residualP sigma kappa c p := by
  obtain ⟨p,hp0,hp1,hp⟩ := exists_finite_jet sigma kappa c s hs N hne
  exact ⟨p,hp0,hp1,X_pow_dvd_iff.mpr (fun i hi => hp i (by omega))⟩

end SepticProfile.SourceJets


/- Algebraic finite-jet subtraction for the sonic germ. -/
noncomputable section SourceNoncomp
namespace SepticProfile.Remainder
variable {K : Type*} [CommRing K]

def pref (sigma x : K) : K := (1+x)*(1-sigma*(1+x)^2)
def den (sigma x u : K) : K := pref sigma x*(1-u^2)
def amp (c u : K) : K := 1-c*u^2
def trans (kappa x u : K) : K := kappa*(1+x)*(1-u^2)+3*((1+x)-u)
def res (sigma kappa c x u du : K) : K := den sigma x u*du - amp c u*trans kappa x u

def lin (sigma kappa c x u du : K) : K :=
  -2*pref sigma x*u*du + 2*c*u*trans kappa x u + amp c u*(2*kappa*(1+x)*u+3)
def quad (sigma kappa c x u du d : K) : K :=
  -pref sigma x*du + c*trans kappa x u + 2*c*u*(-2*kappa*(1+x)*u-3) +
    amp c u*kappa*(1+x) +
    (-2*c*u*kappa*(1+x)+c*(-2*kappa*(1+x)*u-3))*d - c*kappa*(1+x)*d^2
def denDiff (sigma x u d : K) : K := -pref sigma x*(2*u+d)

theorem den_expansion (sigma x u d : K) :
    den sigma x (u+d) = den sigma x u+d*denDiff sigma x u d := by
  unfold den denDiff
  ring

theorem res_expansion (sigma kappa c x u du d dd : K) :
    res sigma kappa c x (u+d) (du+dd) =
      res sigma kappa c x u du + den sigma x (u+d)*dd +
        lin sigma kappa c x u du*d + d^2*quad sigma kappa c x u du d := by
  simp only [res, den, lin, quad, amp, trans]
  ring

def denQuot (sigma x p1 : K) : K := pref sigma x*(-2*p1-x*p1^2)

theorem den_factor (sigma x p1 : K) :
    den sigma x (1+x*p1) = x*denQuot sigma x p1 := by
  simp only [den, denQuot]
  ring

def jetA (sigma x p p1 g : K) (m : ℕ) : K :=
  denQuot sigma x p1 + x^(m+1)*g*denDiff sigma x p (x^(m+2)*g)

def jetE (sigma kappa c rho x p dp s e g : K) (m : ℕ) : K :=
  s+e*g+x^(m+1)*g^2*quad sigma kappa c x p dp (x^(m+2)*g)+
    rho*x^m*g^2*denDiff sigma x p (x^(m+2)*g)

/-- Exact cleared algebraic identity; no small-denominator approximation. -/
theorem jet_identity (sigma kappa c rho x p p1 dp s e g dg : K) (m : ℕ)
    (hp : p=1+x*p1)
    (hr : res sigma kappa c x p dp=x^(m+3)*s)
    (hl : rho*denQuot sigma x p1+lin sigma kappa c x p dp=x*e) :
    res sigma kappa c x (p+x^(m+2)*g)
      (dp+(m+2)*x^(m+1)*g+x^(m+2)*dg) =
      x^(m+2)*(jetA sigma x p p1 g m * (x*dg+((m+2)-rho)*g)+
        x*jetE sigma kappa c rho x p dp s e g m) := by
  have hd : den sigma x p=x*denQuot sigma x p1 := by rw [hp, den_factor]
  rw [show dp+(m+2)*x^(m+1)*g+x^(m+2)*dg =
    dp+((m+2)*x^(m+1)*g+x^(m+2)*dg) by ring, res_expansion, hr, den_expansion, hd]
  have hl' : lin sigma kappa c x p dp=x*e-rho*denQuot sigma x p1 := by
    linear_combination hl
  rw [hl']
  simp only [jetA, jetE, pow_succ]
  ring

 theorem jetA_zero (sigma p p1 g : K) (m : ℕ) :
    jetA sigma 0 p p1 g m = -2*(1-sigma)*p1 := by
  simp [jetA, denQuot, pref]
  ring

end SepticProfile.Remainder

namespace SepticProfile.SourceSonic
open Polynomial

def prefP (sigma : ℝ) : Polynomial ℝ := (1+X)*(1-C sigma*(1+X)^2)
def denQuotP (sigma : ℝ) (p1 : Polynomial ℝ) : Polynomial ℝ := prefP sigma*(-2*p1-X*p1^2)
def transP (kappa : ℝ) (p : Polynomial ℝ) : Polynomial ℝ :=
  C kappa*(1+X)*(1-p^2)+3*((1+X)-p)
def linP (sigma kappa c : ℝ) (p : Polynomial ℝ) : Polynomial ℝ :=
  -2*prefP sigma*p*p.derivative+2*C c*p*transP kappa p+
    (1-C c*p^2)*(2*C kappa*(1+X)*p+3)

 theorem split_polynomial {p : Polynomial ℝ} {s : ℝ}
    (hp0 : p.coeff 0=1) (hp1 : p.coeff 1=s) :
    ∃ p1 : Polynomial ℝ, p=1+X*p1 ∧ p1.coeff 0=s := by
  have hd : (X : Polynomial ℝ) ∣ p-1 := X_dvd_iff.mpr (by simp [hp0])
  obtain ⟨p1,hp1'⟩ := hd
  have he : p=1+X*p1 := by linear_combination hp1'
  refine ⟨p1,he,?_⟩
  rw [he] at hp1
  simpa [coeff_one] using hp1

 theorem coeff_denQuotP {p1 : Polynomial ℝ} {s : ℝ} (h : p1.coeff 0=s) (sigma : ℝ) :
    (denQuotP sigma p1).coeff 0 = -2*(1-sigma)*s := by
  rw [coeff_zero_eq_eval_zero]
  have he : p1.eval 0=s := by simpa only [coeff_zero_eq_eval_zero] using h
  simp [denQuotP, prefP, he]
  ring

 theorem coeff_linP {p : Polynomial ℝ} {s : ℝ}
    (hp0 : p.coeff 0=1) (hp1 : p.coeff 1=s) (sigma kappa c : ℝ) :
    (linP sigma kappa c p).coeff 0 = -2*(1-sigma)*s+(1-c)*(2*kappa+3) := by
  rw [coeff_zero_eq_eval_zero]
  have he0 : p.eval 0=1 := by simpa only [coeff_zero_eq_eval_zero] using hp0
  have he1 : p.derivative.eval 0=s := by
    rw [← coeff_zero_eq_eval_zero, coeff_derivative]
    simpa using hp1
  simp [linP, prefP, transP, he0, he1]

 theorem split_linearization {p p1 : Polynomial ℝ} {s rho sigma kappa c : ℝ}
    (hp0 : p.coeff 0=1) (hp1 : p.coeff 1=s) (hp10 : p1.coeff 0=s)
    (hrho : rho*(2*(1-sigma)*s)=(1-c)*(2*kappa+3)-2*(1-sigma)*s) :
    ∃ e : Polynomial ℝ, C rho*denQuotP sigma p1+linP sigma kappa c p=X*e := by
  apply X_dvd_iff.mpr
  rw [coeff_add, coeff_C_mul, coeff_denQuotP hp10,
    coeff_linP hp0 hp1]
  linear_combination -hrho

 theorem aeval_prefP (sigma : ℝ) (z : ℂ) :
    aeval z (prefP sigma)=Remainder.pref (sigma : ℂ) z := by simp [prefP, Remainder.pref]
 theorem aeval_denQuotP (sigma : ℝ) (p1 : Polynomial ℝ) (z : ℂ) :
    aeval z (denQuotP sigma p1)=Remainder.denQuot (sigma : ℂ) z (aeval z p1) := by
  simp [denQuotP, Remainder.denQuot, aeval_prefP, map_ofNat]
 theorem aeval_transP (kappa : ℝ) (p : Polynomial ℝ) (z : ℂ) :
    aeval z (transP kappa p)=Remainder.trans (kappa : ℂ) z (aeval z p) := by
  simp [transP, Remainder.trans, map_ofNat]
 theorem aeval_linP (sigma kappa c : ℝ) (p : Polynomial ℝ) (z : ℂ) :
    aeval z (linP sigma kappa c p)=Remainder.lin (sigma : ℂ) (kappa : ℂ) (c : ℂ) z (aeval z p)
      (aeval z p.derivative) := by
  simp [linP, Remainder.lin, Remainder.amp, aeval_prefP, aeval_transP, map_ofNat]
 theorem aeval_residualP (sigma kappa c : ℝ) (p : Polynomial ℝ) (z : ℂ) :
    aeval z (SourceJets.residualP sigma kappa c p)=Remainder.res (sigma : ℂ) (kappa : ℂ) (c : ℂ) z (aeval z p)
      (aeval z p.derivative) := by
  simp [SourceJets.residualP, Remainder.res, Remainder.den, Remainder.pref, Remainder.amp,
    Remainder.trans, map_ofNat]

 theorem aeval_real (p : Polynomial ℝ) {z : ℂ} (hz : z.im=0) : (aeval z p : ℂ).im=0 := by
  have he : z=(z.re : ℂ) := by apply Complex.ext <;> simp [hz]
  rw [he]
  have he' : aeval ((z.re : ℝ) : ℂ) p = ((p.eval z.re : ℝ) : ℂ) :=
    aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) _ _
  rw [he']
  rfl

end SepticProfile.SourceSonic

namespace SepticProfile.SourceSonic
open Polynomial Set Filter
open scoped Topology

def sourceH (sigma kappa c rho : ℝ) (p p1 S E : Polynomial ℝ) (m : ℕ) (v : ℂ × ℂ) : ℂ :=
  -Remainder.jetE (sigma : ℂ) (kappa : ℂ) (c : ℂ) (rho : ℂ) v.1
      (aeval v.1 p) (aeval v.1 p.derivative) (aeval v.1 S) (aeval v.1 E) v.2 m /
    Remainder.jetA (sigma : ℂ) v.1 (aeval v.1 p) (aeval v.1 p1) v.2 m

 theorem sourceH_analytic (sigma kappa c rho s : ℝ) (p p1 S E : Polynomial ℝ) (m : ℕ)
    (hp10 : p1.coeff 0=s) (hd : 2*(1-sigma)*s≠0) :
    AnalyticAt ℂ (sourceH sigma kappa c rho p p1 S E m) 0 := by
  have hf (a : ℂ × ℂ) : AnalyticAt ℂ (fun v : ℂ × ℂ => v.1) a := analyticAt_fst
  have hg (a : ℂ × ℂ) : AnalyticAt ℂ (fun v : ℂ × ℂ => v.2) a := analyticAt_snd
  have han (q : Polynomial ℝ) (a : ℂ × ℂ) : AnalyticAt ℂ (fun v : ℂ × ℂ => aeval v.1 q) a :=
    (hf a).aeval_polynomial q
  have hden : Remainder.jetA (sigma : ℂ) (0 : ℂ × ℂ).1
      (aeval (0 : ℂ × ℂ).1 p) (aeval (0 : ℂ × ℂ).1 p1) (0 : ℂ × ℂ).2 m ≠ 0 := by
    rw [Prod.fst_zero, Prod.snd_zero, Remainder.jetA_zero,
      ← coeff_zero_eq_aeval_zero', hp10]
    change -2*(1-(sigma : ℂ))*(s : ℂ) ≠ 0
    have hdc : (2 : ℂ)*(1-(sigma : ℂ))*(s : ℂ) ≠ 0 := by exact_mod_cast hd
    simpa only [neg_mul] using neg_ne_zero.mpr hdc
  unfold sourceH
  apply AnalyticAt.div
  · simp only [Remainder.jetE, Remainder.quad, Remainder.pref, Remainder.trans, Remainder.amp,
      Remainder.denDiff]
    fun_prop
  · simp only [Remainder.jetA, Remainder.denQuot, Remainder.pref, Remainder.denDiff]
    fun_prop
  · exact hden

 theorem sourceH_real (sigma kappa c rho : ℝ) (p p1 S E : Polynomial ℝ) (m : ℕ)
    (v : ℂ × ℂ) (hx : v.1.im=0) (hy : v.2.im=0) :
    (sourceH sigma kappa c rho p p1 S E m v).im=0 := by
  apply Complex.conj_eq_iff_im.mp
  have ha (q : Polynomial ℝ) : starRingEnd ℂ (aeval v.1 q)=aeval v.1 q :=
    Complex.conj_eq_iff_im.mpr (aeval_real q hx)
  have hx' := Complex.conj_eq_iff_im.mpr hx
  have hy' := Complex.conj_eq_iff_im.mpr hy
  simp only [sourceH, Remainder.jetE, Remainder.jetA, Remainder.quad, Remainder.pref,
    Remainder.trans, Remainder.amp, Remainder.denDiff, Remainder.denQuot,
    map_add, map_sub, map_mul, map_pow, map_neg, map_div₀, map_ofNat, map_one,
    Complex.conj_ofReal, hx', hy', ha]

end SepticProfile.SourceSonic

namespace SepticProfile.SourceSonic
open Polynomial Set Filter
open scoped Topology

 theorem derivative_jet_add (p : Polynomial ℝ) (F : ℂ → ℂ) (m : ℕ) {z : ℂ}
    (hF : DifferentiableAt ℂ F z) :
    HasDerivAt (fun x : ℂ => aeval x p+x^(m+2)*F x)
      (aeval z p.derivative+((m : ℂ)+2)*z^(m+1)*F z+z^(m+2)*deriv F z) z := by
  convert (p.hasDerivAt_aeval z).add (((hasDerivAt_id z).pow (m+2)).mul hF.hasDerivAt) using 1
  all_goals first | rfl | (simp [add_assoc])

/-- A nonresonant analytic transonic germ for the normalized residual. -/
 theorem exists_sonic_germ (sigma kappa c s rho : ℝ)
    (hs : 2*(1-sigma)*s^2-(1-c)*(2*kappa+3)*s+3*(1-c)=0)
    (hd : 2*(1-sigma)*s ≠ 0)
    (hrho : rho*(2*(1-sigma)*s)=(1-c)*(2*kappa+3)-2*(1-sigma)*s)
    (hnr : ∀ n : ℕ, rho ≠ (n : ℝ)+2) :
    ∃ U : ℂ → ℂ, AnalyticAt ℂ U 0 ∧ U 0=1 ∧ deriv U 0=(s : ℂ) ∧
      (∀ x : ℝ, (U x).im=0) ∧
      ∀ᶠ z in 𝓝 (0 : ℂ),
        (1+z)*(1-(sigma : ℂ)*(1+z)^2)*(1-(U z)^2)*deriv U z =
          (1-(c : ℂ)*(U z)^2)*((kappa : ℂ)*(1+z)*(1-(U z)^2)+3*((1+z)-U z)) := by
  obtain ⟨m,hm⟩ := exists_nat_gt rho
  have hcoef (n : ℕ) : (1-c)*(2*kappa+3)-2*(1-sigma)*s*((n : ℝ)+3) ≠ 0 := by
    intro he
    have hz : (2*(1-sigma)*s)*(rho-((n : ℝ)+2))=0 := by
      linear_combination hrho + he
    exact hnr n (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hd))
  obtain ⟨p,hp0,hp1,S,hS⟩ := SourceJets.exists_finite_jet_divisible sigma kappa c s hs
    (m+1) (fun n _ => hcoef n)
  have hS' : SourceJets.residualP sigma kappa c p=X^(m+3)*S := by
    simpa only [Nat.add_assoc] using hS
  obtain ⟨p1,hp,hp10⟩ := split_polynomial hp0 hp1
  obtain ⟨E,hE⟩ := split_linearization hp0 hp1 hp10 hrho
  have hc : 0 ≤ ((m : ℝ)+2)-rho := by linarith
  obtain ⟨F,hFa,hF0,hFr,hFe⟩ := Fuchsian.exists_real_fuchsian_germ hc
    (sourceH sigma kappa c rho p p1 S E m)
    (sourceH_analytic sigma kappa c rho s p p1 S E m hp10 hd)
    (sourceH_real sigma kappa c rho p p1 S E m)
  let U : ℂ → ℂ := fun z => aeval z p+z^(m+2)*F z
  have han : AnalyticAt ℂ U 0 :=
    (analyticAt_id.aeval_polynomial p).add ((analyticAt_id.pow (m+2)).mul hFa)
  have hdu {z : ℂ} (hz : DifferentiableAt ℂ F z) :
      deriv U z=aeval z p.derivative+((m : ℂ)+2)*z^(m+1)*F z+z^(m+2)*deriv F z :=
    (derivative_jet_add p F m hz).deriv
  have hdc : (2 : ℂ)*(1-(sigma : ℂ))*(s : ℂ) ≠ 0 := by exact_mod_cast hd
  let A : ℂ → ℂ := fun z => Remainder.jetA (sigma : ℂ) z (aeval z p) (aeval z p1) (F z) m
  have hAc : ContinuousAt A 0 := by
    have hf := hFa.continuousAt
    have hpq (q : Polynomial ℝ) : ContinuousAt (fun z : ℂ => aeval z q) 0 :=
      ((analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) 0).aeval_polynomial q).continuousAt
    dsimp only [A, Remainder.jetA, Remainder.denQuot, Remainder.denDiff, Remainder.pref]
    fun_prop
  have hA0 : A 0 ≠ 0 := by
    simp only [A, Remainder.jetA_zero, ← coeff_zero_eq_aeval_zero', hp10]
    change -2*(1-(sigma : ℂ))*(s : ℂ) ≠ 0
    simpa only [neg_mul] using neg_ne_zero.mpr hdc
  refine ⟨U,han,?_,?_,?_,?_⟩
  · simp only [U, zero_pow (by omega : m+2≠0), zero_mul, add_zero,
      ← coeff_zero_eq_aeval_zero', hp0, map_one]
  · rw [hdu hFa.differentiableAt]
    simp only [zero_pow (by omega : m+1≠0), zero_pow (by omega : m+2≠0),
      mul_zero, zero_mul, add_zero, ← coeff_zero_eq_aeval_zero', coeff_derivative]
    simp only [Nat.cast_zero, zero_add, mul_one, hp1]
    rfl
  · intro x
    apply Complex.conj_eq_iff_im.mp
    have hpconj := Complex.conj_eq_iff_im.mpr (aeval_real p (z := (x : ℂ)) (by simp))
    have hfconj := Complex.conj_eq_iff_im.mpr (hFr x)
    simp only [U, map_add, map_mul, map_pow, hpconj, hfconj, Complex.conj_ofReal]
  · filter_upwards [hFe,hFa.eventually_analyticAt,hAc.eventually_ne hA0] with z hfe hfz hAz
    have hpz : aeval z p=1+z*aeval z p1 := by rw [hp]; simp
    have hsz : Remainder.res (sigma : ℂ) (kappa : ℂ) (c : ℂ) z (aeval z p)
        (aeval z p.derivative)=z^(m+3)*aeval z S := by
      rw [← aeval_residualP, hS']; simp
    have hez : (rho : ℂ)*Remainder.denQuot (sigma : ℂ) z (aeval z p1)+
        Remainder.lin (sigma : ℂ) (kappa : ℂ) (c : ℂ) z (aeval z p) (aeval z p.derivative)=
        z*aeval z E := by
      rw [← aeval_denQuotP, ← aeval_linP]
      have he := congrArg (aeval z : Polynomial ℝ →ₐ[ℝ] ℂ) hE
      simpa using he
    have heq := Remainder.jet_identity (sigma : ℂ) (kappa : ℂ) (c : ℂ) (rho : ℂ)
      z (aeval z p) (aeval z p1) (aeval z p.derivative) (aeval z S) (aeval z E)
      (F z) (deriv F z) m hpz hsz hez
    have hcanc : A z*(z*deriv F z+((m : ℂ)+2-(rho : ℂ))*F z)+
        z*Remainder.jetE (sigma : ℂ) (kappa : ℂ) (c : ℂ) (rho : ℂ) z
          (aeval z p) (aeval z p.derivative) (aeval z S) (aeval z E) (F z) m=0 := by
      push_cast at hfe
      rw [hfe]
      change A z*(z*(-Remainder.jetE _ _ _ _ _ _ _ _ _ _ _ / A z))+_ = 0
      (field_simp [hAz]; ring)
    have hres : Remainder.res (sigma : ℂ) (kappa : ℂ) (c : ℂ) z (U z) (deriv U z)=0 := by
      rw [hdu hfz.differentiableAt]
      change Remainder.res _ _ _ _ (aeval z p+z^(m+2)*F z) _=0
      rw [heq]
      change z^(m+2)*(A z*(z*deriv F z+((m : ℂ)+2-(rho : ℂ))*F z)+_)=0
      rw [hcanc, mul_zero]
    exact sub_eq_zero.mp hres

end SepticProfile.SourceSonic

namespace SepticProfile.SourceSonic
open Filter
open scoped Topology ContDiff

 theorem exists_real_sonic_germ (sigma kappa c s rho : ℝ)
    (hs : 2*(1-sigma)*s^2-(1-c)*(2*kappa+3)*s+3*(1-c)=0)
    (hd : 2*(1-sigma)*s ≠ 0)
    (hrho : rho*(2*(1-sigma)*s)=(1-c)*(2*kappa+3)-2*(1-sigma)*s)
    (hnr : ∀ n : ℕ, rho ≠ (n : ℝ)+2) :
    ∃ u : ℝ → ℝ, AnalyticAt ℝ u 0 ∧ u 0=1 ∧ deriv u 0=s ∧
      ∀ᶠ x in 𝓝 (0 : ℝ),
        (1+x)*(1-sigma*(1+x)^2)*(1-(u x)^2)*deriv u x =
          (1-c*(u x)^2)*(kappa*(1+x)*(1-(u x)^2)+3*((1+x)-u x)) := by
  obtain ⟨U,hUa,hU0,hUd,hUr,hUe⟩ := exists_sonic_germ sigma kappa c s rho hs hd hrho hnr
  let u : ℝ → ℝ := fun x => (U x).re
  have hucont : AnalyticAt ℝ u 0 := by
    exact (show AnalyticAt ℂ U (0 : ℝ) by simpa only [Complex.ofReal_zero] using hUa).re_ofReal
  have hdu {x : ℝ} (hx : DifferentiableAt ℂ U x) : deriv u x=(deriv U (x : ℂ)).re :=
    hx.hasDerivAt.real_of_complex.deriv
  refine ⟨u,hucont,?_,?_,?_⟩
  · simpa only [u, Complex.ofReal_zero, hU0] using (Complex.one_re : (1 : ℂ).re=1)
  · rw [hdu (by simpa using hUa.differentiableAt)]
    simp [hUd]
  · have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝 0) (𝓝 (0 : ℂ)) := by
      simpa only [ContinuousAt, Complex.ofReal_zero] using
        (Complex.continuous_ofReal.continuousAt (x := (0 : ℝ)))
    filter_upwards [ht.eventually hUe,ht.eventually hUa.eventually_analyticAt] with x hxe hxa
    have huv : U (x : ℂ)=(u x : ℂ) := by
      apply Complex.ext <;> simp [u,hUr]
    have he := congrArg Complex.re hxe
    rw [huv] at he
    simp only [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_mul,
      ← Complex.ofReal_sub, ← Complex.ofReal_pow, ← Complex.ofReal_ofNat] at he
    rw [hdu hxa.differentiableAt]
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using he

end SepticProfile.SourceSonic

namespace SepticProfile.SourceEuler
open Filter
open scoped Topology

def changeOfVariable (h t : ℝ) : ℝ := -h*t/(1-t)
def A (t : ℝ) : ℝ := 1-t
def B (h t : ℝ) : ℝ := 1-(1+h)*t

def residual (sigma kappa c h t u du : ℝ) : ℝ :=
  B h t*((A t)^2-sigma*(B h t)^2)*(1-u^2)*du +
    h*(1-c*u^2)*(kappa*B h t*(1-u^2)+3*(B h t-A t*u))

lemma derivative_changeOfVariable (h t : ℝ) (ht : 1-t≠0) :
    HasDerivAt (changeOfVariable h) (-h/(1-t)^2) t := by
  have hd := (((hasDerivAt_id t).const_mul (-h)).div
    ((hasDerivAt_const t 1).sub (hasDerivAt_id t)) ht)
  convert hd using 1
  all_goals first | rfl | (dsimp [changeOfVariable]; congr 1; ring)

lemma transform_equation (sigma kappa c h t u du : ℝ) (ht : 1-t≠0)
    (he : (1+changeOfVariable h t)*(1-sigma*(1+changeOfVariable h t)^2)*(1-u^2)*du =
      (1-c*u^2)*(kappa*(1+changeOfVariable h t)*(1-u^2)+3*((1+changeOfVariable h t)-u))) :
    residual sigma kappa c h t u (du*(-h/(1-t)^2))=0 := by
  unfold changeOfVariable at he
  unfold residual A B
  field_simp at he ⊢
  linear_combination -h*he

 theorem exists_real_euler_germ (sigma kappa c h s rho : ℝ)
    (hs : 2*(1-sigma)*s^2-(1-c)*(2*kappa+3)*s+3*(1-c)=0)
    (hd : 2*(1-sigma)*s ≠ 0)
    (hrho : rho*(2*(1-sigma)*s)=(1-c)*(2*kappa+3)-2*(1-sigma)*s)
    (hnr : ∀ n : ℕ, rho ≠ (n : ℝ)+2) :
    ∃ u : ℝ → ℝ, AnalyticAt ℝ u 0 ∧ u 0=1 ∧ deriv u 0=-h*s ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), residual sigma kappa c h t (u t) (deriv u t)=0 := by
  obtain ⟨v,hva,hv0,hvd,hve⟩ :=
    SepticProfile.SourceSonic.exists_real_sonic_germ sigma kappa c s rho hs hd hrho hnr
  have hp0 : changeOfVariable h 0=0 := by simp [changeOfVariable]
  have hpa : AnalyticAt ℝ (changeOfVariable h) 0 := by
    unfold changeOfVariable
    fun_prop (disch := norm_num)
  let u := v ∘ changeOfVariable h
  have hua : AnalyticAt ℝ u 0 := by
    exact (hp0 ▸ hva).comp hpa
  have huder {t : ℝ} (ht : 1-t≠0) (hvt : DifferentiableAt ℝ v (changeOfVariable h t)) :
      deriv u t=deriv v (changeOfVariable h t)*(-h/(1-t)^2) := by
    exact ((hvt.hasDerivAt).comp t (derivative_changeOfVariable h t ht)).deriv
  refine ⟨u,hua,by simpa [u,hp0] using hv0,?_,?_⟩
  · rw [huder (by norm_num) (by simpa only [hp0] using hva.differentiableAt),hp0,hvd]
    ring
  · have hpt : Tendsto (changeOfVariable h) (𝓝 0) (𝓝 0) := by
      simpa only [ContinuousAt,hp0] using hpa.continuousAt
    have htn : ∀ᶠ t : ℝ in 𝓝 0, 1-t≠0 := by
      exact (continuous_const.sub continuous_id).continuousAt.eventually_ne (by norm_num)
    filter_upwards [hpt.eventually hve,hpt.eventually hva.eventually_analyticAt,htn]
      with t hte hta htn
    rw [huder htn hta.differentiableAt]
    exact transform_equation sigma kappa c h t (v (changeOfVariable h t))
      (deriv v (changeOfVariable h t)) htn hte

end SepticProfile.SourceEuler

end SourceNoncomp
end SourceNoncomp
end SourceNoncomp
end SourceConstruction

section ParameterBounds


/-! A rational chart on the sonic quadratic. The interval avoids integral
sonic resonances and satisfies the required parameter inequalities. -/
noncomputable section ParameterNoncomp
namespace SepticProfile.ShootingParameters

def leftEnd : ℝ := -706019/1000000
def rightEnd : ℝ := -705986/1000000

def a (t : ℝ) : ℝ := 27*t^2-5
def d (t : ℝ) : ℝ := 81*t^2-18*t-20
def e (t : ℝ) : ℝ := 81*t^2-9*t-21
def k (t : ℝ) : ℝ := 162*t^2+18*t-67

def beta (t : ℝ) : ℝ := 9*(1-9*t)/(2*d t)
def q (t : ℝ) : ℝ := 3*e t/d t
def sigma (t : ℝ) : ℝ := 3*(d t)^2/(5*(e t)^2)
def kappa (t : ℝ) : ℝ := (162*t^2+45*t-49)/(2*e t)
def slope (t : ℝ) : ℝ := e t/(3*a t)
def ratio (t : ℝ) : ℝ := 9*a t/k t

theorem rough_bounds {t : ℝ} (ht : t ∈ Set.Icc leftEnd rightEnd) :
    -(71/100 : ℝ)<t ∧ t< -(7/10 : ℝ) := by
  dsimp [leftEnd,rightEnd] at ht
  constructor <;> linarith [ht.1,ht.2]

theorem a_pos {t : ℝ} (ht : t ∈ Set.Icc leftEnd rightEnd) : 0<a t := by
  have h := rough_bounds ht
  dsimp [a]
  nlinarith [sq_nonneg (t+7/10)]

theorem d_pos {t : ℝ} (ht : t ∈ Set.Icc leftEnd rightEnd) : 0<d t := by
  have h := rough_bounds ht
  dsimp [d]
  nlinarith [sq_nonneg (t+7/10)]

theorem e_pos {t : ℝ} (ht : t ∈ Set.Icc leftEnd rightEnd) : 0<e t := by
  have h := rough_bounds ht
  dsimp [e]
  nlinarith [sq_nonneg (t+7/10)]

theorem k_pos {t : ℝ} (ht : t ∈ Set.Icc leftEnd rightEnd) : 0<k t := by
  have h := ht.2
  dsimp [rightEnd,k] at *
  nlinarith [sq_nonneg (t+705986/1000000)]

theorem parameter_identities {t : ℝ} (ht : t ∈ Set.Icc leftEnd rightEnd) :
    q t=3-2*beta t/3 ∧ sigma t=27/(5*(q t)^2) ∧
      kappa t=3*(1-beta t)/q t := by
  have hd := ne_of_gt (d_pos ht)
  have he := ne_of_gt (e_pos ht)
  simp only [q,beta,sigma,kappa]
  constructor
  · field_simp
    dsimp [d,e]
    ring
  constructor
  · (field_simp; ring)
  · field_simp
    dsimp [d,e]
    ring

theorem sonic_quadratic {t : ℝ} (ht : t ∈ Set.Icc leftEnd rightEnd) :
    2*(1-sigma t)*(slope t)^2-(1-(3/5:ℝ))*(2*kappa t+3)*slope t+3*(1-(3/5:ℝ))=0 := by
  have ha := ne_of_gt (a_pos ht)
  have he := ne_of_gt (e_pos ht)
  simp only [sigma,kappa,slope]
  field_simp
  dsimp [a,d,e]
  ring

theorem ratio_bounds {t : ℝ} (ht : t ∈ Set.Icc leftEnd rightEnd) :
    73 < ratio t ∧ ratio t < 74 := by
  have hk := k_pos ht
  have hr := rough_bounds ht
  have hleft : 0≤(t-leftEnd)*(-11583*(t+leftEnd)-1314) := by
    apply mul_nonneg (sub_nonneg.mpr ht.1)
    dsimp [leftEnd]
    linarith [hr.2]
  have hright : 0≤(rightEnd-t)*(-11745*(t+rightEnd)-1332) := by
    apply mul_nonneg (sub_nonneg.mpr ht.2)
    dsimp [rightEnd]
    linarith [hr.2]
  rw [ratio, lt_div_iff₀ hk, div_lt_iff₀ hk]
  dsimp [a,k,leftEnd,rightEnd] at *
  constructor <;> nlinarith

theorem nonresonance {t : ℝ} (ht : t ∈ Set.Icc leftEnd rightEnd) :
    ∀ n : ℕ, ratio t ≠ (n : ℝ)+2 := by
  intro n hn
  have h := ratio_bounds ht
  rw [hn] at h
  have hn1 : 71 < n := by exact_mod_cast (by linarith [h.1] : (71:ℝ)<(n:ℝ))
  have hn2 : n < 72 := by exact_mod_cast (by linarith [h.2] : (n:ℝ)<(72:ℝ))
  omega

theorem beta_bounds {t : ℝ} (ht : t ∈ Set.Icc leftEnd rightEnd) :
    1 < beta t ∧ beta t < 1001/1000 := by
  have hd := d_pos ht
  have hr := rough_bounds ht
  have hl : 0≤(t-leftEnd)*(-162*(t+leftEnd)-45) := by
    apply mul_nonneg (sub_nonneg.mpr ht.1)
    dsimp [leftEnd]
    linarith [hr.2]
  have hu : 0≤(rightEnd-t)*(-162162*(t+rightEnd)-44964) := by
    apply mul_nonneg (sub_nonneg.mpr ht.2)
    dsimp [rightEnd]
    linarith [hr.2]
  rw [beta,lt_div_iff₀ (by positivity),div_lt_iff₀ (by positivity)]
  dsimp [d,leftEnd,rightEnd] at *
  constructor <;> nlinarith

theorem sigma_bounds {t : ℝ} (ht : t ∈ Set.Icc leftEnd rightEnd) :
    0 < sigma t ∧ sigma t < 1 := by
  have hd := d_pos ht
  have he := e_pos ht
  have hb := beta_bounds ht
  have hi := parameter_identities ht
  have hq : 233/100 < q t := by rw [hi.1]; linarith [hb.2]
  constructor
  · dsimp [sigma]
    positivity
  · rw [hi.2.1,div_lt_one (by positivity)]
    nlinarith [sq_nonneg (q t-233/100)]

theorem slope_pos {t : ℝ} (ht : t ∈ Set.Icc leftEnd rightEnd) : 0 < slope t :=
  div_pos (e_pos ht) (mul_pos (by norm_num) (a_pos ht))

theorem sonic_divisor_ne {t : ℝ} (ht : t ∈ Set.Icc leftEnd rightEnd) :
    2*(1-sigma t)*slope t ≠ 0 :=
  ne_of_gt (mul_pos (mul_pos (by norm_num) (sub_pos.mpr (sigma_bounds ht).2)) (slope_pos ht))

theorem ratio_identity {t : ℝ} (ht : t ∈ Set.Icc leftEnd rightEnd) :
    ratio t*(2*(1-sigma t)*slope t) =
      (1-(3/5:ℝ))*(2*kappa t+3)-2*(1-sigma t)*slope t := by
  have ha := ne_of_gt (a_pos ht)
  have he := ne_of_gt (e_pos ht)
  have hk := ne_of_gt (k_pos ht)
  simp only [ratio,sigma,kappa,slope]
  field_simp
  dsimp [a,d,e,k]
  ring

theorem standing_beta_bound {t : ℝ} (ht : t ∈ Set.Icc leftEnd rightEnd) :
    1 < beta t ∧ beta t*((5/3:ℝ)+Real.sqrt (5/3:ℝ)) < 3 := by
  have hb := beta_bounds ht
  have hs : Real.sqrt (5/3:ℝ)<13/10 := by
    have he := Real.sq_sqrt (by norm_num : (0:ℝ)≤5/3)
    have hn := Real.sqrt_nonneg (5/3:ℝ)
    nlinarith
  refine ⟨hb.1,?_⟩
  have hm := mul_lt_mul_of_pos_left hs (by linarith [hb.1] : 0 < beta t)
  nlinarith [hb.2]


theorem shooting_coefficient_bounds {t : ℝ}
    (ht : t ∈ Set.Icc leftEnd rightEnd) :
    991/1000 < sigma t ∧ sigma t < 993/1000 ∧
      -(1/500:ℝ) < kappa t ∧ kappa t < 0 := by
  have hb := beta_bounds ht
  have hi := parameter_identities ht
  have hq1 : (3499/1500:ℝ) < q t := by rw [hi.1]; linarith [hb.2]
  have hq2 : q t < (7/3:ℝ) := by rw [hi.1]; linarith [hb.1]
  have hq : 0 < q t := by linarith
  have hqlo : (3499/1500:ℝ)^2 < (q t)^2 := by nlinarith [sq_nonneg (q t-3499/1500)]
  have hqhi : (q t)^2 < (7/3:ℝ)^2 := by nlinarith [mul_pos (sub_pos.mpr hq2) (by linarith : 0 < 7/3+q t)]
  rw [hi.2.1,hi.2.2]
  constructor
  · rw [lt_div_iff₀ (by positivity)]
    nlinarith
  constructor
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith
  constructor
  · rw [lt_div_iff₀ hq]
    linarith [hb.2]
  · exact div_neg_of_neg_of_pos (by linarith [hb.1]) hq

end SepticProfile.ShootingParameters

end ParameterNoncomp
end ParameterBounds



/-! The sonic formal series is the Taylor jet of a smooth profile;
this construction does not assume analyticity. -/
noncomputable section
namespace SepticProfile.SonicJet
open PowerSeries Filter
open scoped Topology ContDiff
abbrev Series := PowerSeries ℝ

def jet (f : ℝ → ℝ) : Series := mk fun n => iteratedDeriv n f 0 / n.factorial

lemma coeff_jet (f : ℝ → ℝ) (n : ℕ) :
    coeff n (jet f) = iteratedDeriv n f 0 / n.factorial := by
  simp [jet]

lemma jet_congr {f g : ℝ → ℝ} (h : f =ᶠ[𝓝 0] g) : jet f = jet g := by
  ext n
  rw [coeff_jet, coeff_jet, (h.iteratedDeriv n).eq_of_nhds]

lemma jet_const (a : ℝ) : jet (fun _ => a) = C a := by
  ext n
  by_cases hn : n = 0 <;> simp [coeff_jet, iteratedDeriv_const, coeff_C, hn]

lemma jet_add {f g : ℝ → ℝ} (hf : ContDiffAt ℝ ∞ f 0) (hg : ContDiffAt ℝ ∞ g 0) :
    jet (fun x => f x + g x) = jet f + jet g := by
  ext n
  rw [map_add, coeff_jet, coeff_jet, coeff_jet,
    iteratedDeriv_fun_add (hf.of_le (show (n : ℕ∞ω) ≤ ∞ from by exact_mod_cast le_top)) (hg.of_le (show (n : ℕ∞ω) ≤ ∞ from by exact_mod_cast le_top)), add_div]

lemma jet_sub {f g : ℝ → ℝ} (hf : ContDiffAt ℝ ∞ f 0) (hg : ContDiffAt ℝ ∞ g 0) :
    jet (fun x => f x - g x) = jet f - jet g := by
  ext n
  rw [map_sub, coeff_jet, coeff_jet, coeff_jet,
    iteratedDeriv_fun_sub (hf.of_le (show (n : ℕ∞ω) ≤ ∞ from by exact_mod_cast le_top)) (hg.of_le (show (n : ℕ∞ω) ≤ ∞ from by exact_mod_cast le_top)), sub_div]

lemma jet_mul {f g : ℝ → ℝ} (hf : ContDiffAt ℝ ∞ f 0) (hg : ContDiffAt ℝ ∞ g 0) :
    jet (fun x => f x*g x) = jet f * jet g := by
  ext n
  simp only [coeff_jet, iteratedDeriv_fun_mul (hf.of_le (show (n : ℕ∞ω) ≤ ∞ from by exact_mod_cast le_top)) (hg.of_le (show (n : ℕ∞ω) ≤ ∞ from by exact_mod_cast le_top)),
    Finset.sum_div, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.succ_eq_add_one]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Nat.cast_choose _ (by have := Finset.mem_range.mp hi; omega)]
  field_simp [Nat.factorial_ne_zero]

lemma jet_pow {f : ℝ → ℝ} (hf : ContDiffAt ℝ ∞ f 0) (n : ℕ) :
    jet (fun x => f x^n) = (jet f)^n := by
  induction n with
  | zero => simp only [pow_zero]; rw [jet_const, map_one]
  | succ n hn =>
    simp only [pow_succ]
    rw [jet_mul (hf.pow n) hf, hn]

lemma jet_deriv (f : ℝ → ℝ) : jet (deriv f) = derivative (jet f) := by
  ext n
  rw [coeff_derivative, coeff_jet, coeff_jet, ← iteratedDeriv_succ', Nat.factorial_succ]
  push_cast
  field_simp

lemma jet_id : jet (fun x => x) = X := by
  ext n
  cases n with
  | zero => simp [coeff_jet]
  | succ n =>
    rw [coeff_jet, iteratedDeriv_succ']
    have hd : deriv (fun x : ℝ => x) = fun _ => (1 : ℝ) := by ext x; simp
    rw [hd, iteratedDeriv_const]
    cases n <;> simp [coeff_X]

lemma jet_z : jet (fun x : ℝ => 1+x) = 1+X := by
  rw [jet_add (by fun_prop) (by fun_prop), jet_const, map_one, jet_id]

lemma jet_zero (f : ℝ → ℝ) (h : f =ᶠ[𝓝 0] fun _ => 0) : jet f = 0 := by
  rw [jet_congr h, jet_const, map_zero]

def z : Series := 1 + X
def prefactor (sigma : ℝ) : Series := z * (1 - C sigma*z^2)
def den (sigma : ℝ) (u : Series) : Series := prefactor sigma * (1-u^2)
def r (u : Series) : Series := 1-C (3/5)*u^2
def t (kappa : ℝ) (u : Series) : Series := C kappa*z*(1-u^2)+3*(z-u)
def residual (sigma kappa : ℝ) (u : Series) : Series :=
  den sigma u * derivative u - r u * t kappa u

def profileResidual (sigma kappa : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1+x)*(1-sigma*(1+x)^2)*(1-(f x)^2)*deriv f x -
    (1-(3/5)*(f x)^2)*(kappa*(1+x)*(1-(f x)^2)+3*((1+x)-f x))

lemma jet_residual (sigma kappa : ℝ) {f : ℝ → ℝ}
    (hf : ContDiffAt ℝ ∞ f 0) :
    jet (profileResidual sigma kappa f) = residual sigma kappa (jet f) := by
  have hfd : ContDiffAt ℝ ∞ (deriv f) 0 := hf.derivWithin (by simp)
  unfold profileResidual residual den prefactor r t z
  simp (disch := fun_prop) only [jet_sub, jet_mul, jet_add, jet_pow, jet_const,
    jet_z, jet_deriv, map_one, map_ofNat]

/-- Every smooth local solution supplies an exact formal jet solution, without
assuming convergence of its Taylor expansion. -/
lemma residual_of_smooth_solution (sigma kappa : ℝ) {f : ℝ → ℝ}
    (hf : ContDiffAt ℝ ∞ f 0)
    (heq : profileResidual sigma kappa f =ᶠ[𝓝 0] fun _ => 0) :
    residual sigma kappa (jet f) = 0 := by
  rw [← jet_residual sigma kappa hf]
  exact jet_zero _ heq

end SepticProfile.SonicJet

namespace SepticProfile.EulerFormal
open PowerSeries Filter
open scoped Topology ContDiff
abbrev Series := PowerSeries ℝ

def A : Series := 1-X
def B (h : ℝ) : Series := 1-C (1+h)*X
def pref (sigma h : ℝ) : Series := B h*(A^2-C sigma*(B h)^2)
def residual (sigma kappa c h : ℝ) (u : Series) : Series :=
  pref sigma h*(1-u^2)*derivative u+
    C h*(1-C c*u^2)*(C kappa*B h*(1-u^2)+3*(B h-A*u))

def profileResidual (sigma kappa c h : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1-(1+h)*x)*((1-x)^2-sigma*(1-(1+h)*x)^2)*(1-(u x)^2)*deriv u x+
    h*(1-c*(u x)^2)*(kappa*(1-(1+h)*x)*(1-(u x)^2)+3*((1-(1+h)*x)-(1-x)*u x))

lemma jet_A : SonicJet.jet (fun x : ℝ => 1-x)=A := by
  rw [SonicJet.jet_sub (by fun_prop) (by fun_prop),SonicJet.jet_const,
    SonicJet.jet_id,map_one]
  rfl

lemma jet_B (h : ℝ) : SonicJet.jet (fun x : ℝ => 1-(1+h)*x)=B h := by
  rw [SonicJet.jet_sub (by fun_prop) (by fun_prop),SonicJet.jet_const,
    SonicJet.jet_mul (by fun_prop) (by fun_prop),SonicJet.jet_const,SonicJet.jet_id,map_one]
  rfl

lemma jet_linear (a : ℝ) : SonicJet.jet (fun x : ℝ => a*x)=C a*X := by
  rw [SonicJet.jet_mul (by fun_prop) (by fun_prop),SonicJet.jet_const,SonicJet.jet_id]

lemma jet_residual (sigma kappa c h : ℝ) {u : ℝ → ℝ}
    (hu : ContDiffAt ℝ ∞ u 0) :
    SonicJet.jet (profileResidual sigma kappa c h u)=residual sigma kappa c h (SonicJet.jet u) := by
  have hud : ContDiffAt ℝ ∞ (deriv u) 0 := hu.derivWithin (by simp)
  unfold profileResidual residual pref
  simp (disch := fun_prop) only [SonicJet.jet_add,SonicJet.jet_sub,SonicJet.jet_mul,
    SonicJet.jet_pow,SonicJet.jet_const,jet_linear,jet_A,SonicJet.jet_deriv,map_one,map_ofNat]
  rfl

lemma residual_of_solution (sigma kappa c h : ℝ) {u : ℝ → ℝ}
    (hu : ContDiffAt ℝ ∞ u 0)
    (he : profileResidual sigma kappa c h u=ᶠ[𝓝 0] fun _ => 0) :
    residual sigma kappa c h (SonicJet.jet u)=0 := by
  rw [← jet_residual sigma kappa c h hu]
  exact SonicJet.jet_zero _ he

def p0 (sigma _h : ℝ) : ℝ := 1-sigma
def p1 (sigma h : ℝ) : ℝ := -2-(1+h)+3*sigma*(1+h)
def p2 (sigma h : ℝ) : ℝ := 1+2*(1+h)-3*sigma*(1+h)^2
def p3 (sigma h : ℝ) : ℝ := -(1+h)+sigma*(1+h)^3

def i10 (kappa c _h : ℝ) : ℝ := -(1-c)*(2*kappa+3)
def i11 (kappa c h : ℝ) : ℝ := (1-c)*(2*kappa*(1+h)+3)+6*c*h
def i20 (kappa c _h : ℝ) : ℝ := kappa*(-(1-c)+4*c)+6*c
def i21 (kappa c h : ℝ) : ℝ := -kappa*(-(1-c)+4*c)*(1+h)-6*c+3*c*h
def i30 (kappa c _h : ℝ) : ℝ := 4*c*kappa+3*c
def i31 (kappa c h : ℝ) : ℝ := -4*c*kappa*(1+h)-3*c
def i40 (kappa c _h : ℝ) : ℝ := c*kappa
def i41 (kappa c h : ℝ) : ℝ := -c*kappa*(1+h)

lemma pref_expansion (sigma h : ℝ) :
    pref sigma h=C (p0 sigma h)+C (p1 sigma h)*X+C (p2 sigma h)*X^2+C (p3 sigma h)*X^3 := by
  unfold pref A B p0 p1 p2 p3
  simp only [map_add,map_sub,map_neg,map_mul,map_pow,map_one,map_ofNat]
  ring

/-- This expansion is what the rational interval recurrence computes, including
all cubic/quartic terms and the Euler factors. -/
lemma residual_expansion (sigma kappa c h : ℝ) (w : Series) :
    residual sigma kappa c h (1+w) =
      -pref sigma h*(derivative (w^2)+C (1/3)*derivative (w^3))+
      C h*(-C (3*(1-c)*h)*X+
        (C (i10 kappa c h)+C (i11 kappa c h)*X)*w+
        (C (i20 kappa c h)+C (i21 kappa c h)*X)*w^2+
        (C (i30 kappa c h)+C (i31 kappa c h)*X)*w^3+
        (C (i40 kappa c h)+C (i41 kappa c h)*X)*w^4) := by
  unfold residual i10 i11 i20 i21 i30 i31 i40 i41
  simp only [map_add,derivative_one,zero_add,derivative_pow]
  norm_num only [Nat.cast_ofNat, map_mul,map_add,map_sub,map_neg,map_pow,map_one,map_ofNat]
  have hc : (C (1/3) : Series)*3=1 := by
    rw [← map_ofNat C 3,← map_mul]
    norm_num
  have h3 : ∀ v : Series, C (1/3)*(3*v)=v := by intro v; rw [← mul_assoc,hc,one_mul]
  simp only [mul_assoc,h3]
  unfold A B
  simp only [map_add,map_one]
  have hc' : (3 : Series)*C (1/3)=1 := by simpa only [mul_comm] using hc
  linear_combination (norm := ring_nf) -(pref sigma h*w^2*derivative w)*hc'
  simp only [mul_assoc,hc,mul_one,neg_add_cancel]

lemma coeff_X_mul_derivative (w : Series) (n : ℕ) :
    coeff n (X*derivative w)=(n : ℝ)*coeff n w := by
  cases n with
  | zero => simp
  | succ n => rw [coeff_succ_X_mul,coeff_derivative]; push_cast; ring

lemma coeff_pref_derivative (sigma h : ℝ) (w : Series) (n : ℕ) :
    coeff (n+2) (pref sigma h*derivative w)=
      p0 sigma h*(n+3)*coeff (n+3) w+
      p1 sigma h*(n+2)*coeff (n+2) w+
      p2 sigma h*(n+1)*coeff (n+1) w+
      p3 sigma h*n*coeff n w := by
  rw [pref_expansion]
  simp only [add_mul,map_add]
  have h0 : coeff (n+2) (C (p0 sigma h)*derivative w)=p0 sigma h*(n+3)*coeff (n+3) w := by
    rw [coeff_C_mul,coeff_derivative]
    push_cast
    ring
  have h1 : coeff (n+2) (C (p1 sigma h)*X*derivative w)=p1 sigma h*(n+2)*coeff (n+2) w := by
    rw [mul_assoc,coeff_C_mul,coeff_X_mul_derivative]
    push_cast
    ring
  have h2 : coeff (n+2) (C (p2 sigma h)*X^2*derivative w)=p2 sigma h*(n+1)*coeff (n+1) w := by
    rw [mul_assoc,coeff_C_mul,show X^2*derivative w=X*(X*derivative w) by ring,
      show n+2=(n+1)+1 by omega,coeff_succ_X_mul,coeff_X_mul_derivative]
    push_cast
    ring
  have h3 : coeff (n+2) (C (p3 sigma h)*X^3*derivative w)=p3 sigma h*n*coeff n w := by
    rw [mul_assoc,coeff_C_mul,show X^3*derivative w=X^2*(X*derivative w) by ring,
      coeff_X_pow_mul,coeff_X_mul_derivative]
    ring
  rw [h0,h1,h2,h3]

lemma coeff_affine_mul (a b : ℝ) (w : Series) (n : ℕ) :
    coeff (n+1) ((C a+C b*X)*w)=a*coeff (n+1) w+b*coeff n w := by
  rw [add_mul,map_add,coeff_C_mul,mul_assoc,coeff_C_mul,coeff_succ_X_mul]

lemma coefficient_equation (sigma kappa c h : ℝ) (w : Series) (n : ℕ)
    (he : residual sigma kappa c h (1+w)=0) :
    -(p0 sigma h*(n+3)*(coeff (n+3) (w^2)+coeff (n+3) (w^3)/3)+
      p1 sigma h*(n+2)*(coeff (n+2) (w^2)+coeff (n+2) (w^3)/3)+
      p2 sigma h*(n+1)*(coeff (n+1) (w^2)+coeff (n+1) (w^3)/3)+
      p3 sigma h*n*(coeff n (w^2)+coeff n (w^3)/3))+
      h*(i10 kappa c h*coeff (n+2) w+i11 kappa c h*coeff (n+1) w+
        i20 kappa c h*coeff (n+2) (w^2)+i21 kappa c h*coeff (n+1) (w^2)+
        i30 kappa c h*coeff (n+2) (w^3)+i31 kappa c h*coeff (n+1) (w^3)+
        i40 kappa c h*coeff (n+2) (w^4)+i41 kappa c h*coeff (n+1) (w^4))=0 := by
  have he' := congrArg (coeff (n+2) : Series → ℝ) he
  rw [residual_expansion] at he'
  have hs : -pref sigma h*(derivative (w^2)+C (1/3)*derivative (w^3)) =
      -(pref sigma h*derivative (w^2))-C (1/3)*(pref sigma h*derivative (w^3)) := by ring
  rw [hs] at he'
  simp only [map_add,map_sub,map_neg,map_zero,coeff_C_mul,coeff_pref_derivative,
    coeff_affine_mul] at he'
  have hx : coeff (n+2) (-C (3*(1-c)*h)*X)=0 := by
    rw [neg_mul,map_neg,coeff_C_mul]
    simp [coeff_X,show n+2≠1 by omega]
  rw [hx] at he'
  linear_combination he'

end SepticProfile.EulerFormal

namespace SepticProfile.EulerFormal
open PowerSeries Finset

lemma coeff_mul_Ico (f g : Series) (a b n : ℕ)
    (hf : ∀ i<a, coeff i f=0) (hg : ∀ i<b, coeff i g=0) :
    coeff n (f*g)=∑ i ∈ Ico a (n+1-b), coeff i f*coeff (n-i) g := by
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  symm
  apply Finset.sum_subset
  · intro i hi
    simp only [mem_Ico,mem_range] at hi ⊢
    omega
  · intro i hi hnot
    have hi' := mem_range.mp hi
    by_cases ha : i<a
    · rw [hf i ha,zero_mul]
    · have hb : n-i<b := by
        simp only [mem_Ico,not_and] at hnot
        have := hnot (by omega)
        omega
      rw [hg (n-i) hb,mul_zero]

lemma coeff_square_low (w : Series) (hw : coeff 0 w=0) (i : ℕ) (hi : i<2) :
    coeff i (w^2)=0 := by
  have hh : ∀ j<1, coeff j w=0 := by
    intro j hj
    have : j=0 := by omega
    simpa [this] using hw
  rw [pow_two,coeff_mul_Ico w w 1 1 i hh hh]
  have hs : Ico 1 (i+1-1)=∅ := by apply Ico_eq_empty_of_le; omega
  rw [hs,sum_empty]

lemma coeff_square (w : Series) (hw : coeff 0 w=0) (n : ℕ) :
    coeff n (w^2)=∑ i ∈ Ico 1 n, coeff i w*coeff (n-i) w := by
  have hh : ∀ j<1, coeff j w=0 := by
    intro j hj
    have : j=0 := by omega
    simpa [this] using hw
  simpa [pow_two] using coeff_mul_Ico w w 1 1 n hh hh

lemma coeff_cube (w : Series) (hw : coeff 0 w=0) (n : ℕ) :
    coeff n (w^3)=∑ i ∈ Ico 1 (n-1), coeff i w*coeff (n-i) (w^2) := by
  rw [show w^3=w*w^2 by ring]
  have hh : ∀ j<1, coeff j w=0 := by
    intro j hj
    have : j=0 := by omega
    simpa [this] using hw
  convert coeff_mul_Ico w (w^2) 1 2 n hh (coeff_square_low w hw) using 1
  congr 2

lemma coeff_fourth (w : Series) (hw : coeff 0 w=0) (n : ℕ) :
    coeff n (w^4)=∑ i ∈ Ico 2 (n-1), coeff i (w^2)*coeff (n-i) (w^2) := by
  rw [show w^4=w^2*w^2 by ring]
  convert coeff_mul_Ico (w^2) (w^2) 2 2 n (coeff_square_low w hw) (coeff_square_low w hw) using 1
  congr 2

lemma coeff_square_remainder (w : Series) (hw : coeff 0 w=0) (k : ℕ) (hk : 2≤k) :
    coeff (k+1) (w^2)=2*coeff 1 w*coeff k w+
      ∑ i ∈ Ico 2 k, coeff i w*coeff (k+1-i) w := by
  rw [coeff_square w hw,Finset.sum_Ico_succ_top (by omega),
    Finset.sum_eq_sum_Ico_succ_bot (by omega : 1<k)]
  simp only [Nat.add_sub_cancel_right,Nat.add_sub_cancel_left]
  ring

end SepticProfile.EulerFormal

/- Exact fixed-point interval arithmetic for sonic shooting bounds. -/
namespace SepticProfile.FixedInterval

structure Box where
  center : ℤ
  radius : ℤ
  deriving DecidableEq, Repr

def Holds (Q : ℤ) (b : Box) (x : ℝ) : Prop :=
  |(Q : ℝ)*x-(b.center : ℝ)| ≤ (b.radius : ℝ)

def zero : Box := ⟨0,0⟩
def neg (a : Box) : Box := ⟨-a.center,a.radius⟩
def add (a b : Box) : Box := ⟨a.center+b.center,a.radius+b.radius⟩
def sub (a b : Box) : Box := add a (neg b)
def grow (a : Box) (r : ℤ) : Box := ⟨a.center,a.radius+r⟩
def scale (a b : ℤ) (v : Box) : Box :=
  ⟨a*v.center/b, (|a| *v.radius)/b+2⟩
def mul (Q : ℤ) (a b : Box) : Box :=
  ⟨a.center*b.center/Q,
    (|a.center| *b.radius+|b.center| *a.radius+a.radius*b.radius)/Q+2⟩

def ofRat (Q a b : ℤ) : Box := ⟨Q*a/b,1⟩

lemma radius_nonneg {Q : ℤ} {b : Box} {x : ℝ} (hx : Holds Q b x) : 0 ≤ b.radius := by
  exact_mod_cast (le_trans (abs_nonneg _) hx)

lemma quotient_bounds (a b : ℤ) (hb : 0 < b) :
    (a/b : ℤ)*b ≤ a ∧ a < ((a/b : ℤ)+1)*b := by
  have hrem := Int.ediv_mul_add_emod a b
  have hl := Int.emod_nonneg a (ne_of_gt hb)
  have hu := Int.emod_lt_of_pos a hb
  constructor <;> nlinarith

lemma rounding_bound (a b : ℤ) (hb : 0 < b) :
    |(a : ℝ)-(b : ℝ)*(a/b : ℤ)| ≤ (b : ℝ) := by
  obtain ⟨hl,hu⟩ := quotient_bounds a b hb
  have hl' : ((a/b : ℤ) : ℝ)*(b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hl
  have hu' : (a : ℝ) < (((a/b : ℤ) : ℝ)+1)*(b : ℝ) := by exact_mod_cast hu
  rw [abs_of_nonneg (by nlinarith)]
  nlinarith

lemma holds_zero (Q : ℤ) : Holds Q zero 0 := by simp [Holds,zero]
lemma holds_neg {Q : ℤ} {b : Box} {x : ℝ} (hx : Holds Q b x) :
    Holds Q (neg b) (-x) := by
  unfold Holds neg
  push_cast
  calc
    _ = |(-((Q : ℝ)*x-b.center))| := by congr 1; ring
    _ = |(Q : ℝ)*x-b.center| := abs_neg _
    _ ≤ _ := hx

lemma holds_add {Q : ℤ} {a b : Box} {x y : ℝ}
    (hx : Holds Q a x) (hy : Holds Q b y) : Holds Q (add a b) (x+y) := by
  change |(Q : ℝ)*(x+y)-((a.center+b.center : ℤ) : ℝ)| ≤ ((a.radius+b.radius : ℤ) : ℝ)
  push_cast
  calc
    _ = |((Q : ℝ)*x-a.center)+((Q : ℝ)*y-b.center)| := by congr 1; ring
    _ ≤ |(Q : ℝ)*x-a.center| +|(Q : ℝ)*y-b.center| := abs_add_le _ _
    _ ≤ _ := add_le_add hx hy

lemma holds_sub {Q : ℤ} {a b : Box} {x y : ℝ}
    (hx : Holds Q a x) (hy : Holds Q b y) : Holds Q (sub a b) (x-y) := by
  simpa only [sub, sub_eq_add_neg] using holds_add hx (holds_neg hy)

lemma holds_scale {Q a b : ℤ} {v : Box} {x : ℝ} (hb : 0 < b)
    (hx : Holds Q v x) : Holds Q (scale a b v) ((a : ℝ)/(b : ℝ)*x) := by
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have hr := radius_nonneg hx
  have hround := rounding_bound (a*v.center) b hb
  have hrad := (quotient_bounds (|a| *v.radius) b hb).2
  have hrad' : (|a| : ℝ)*(v.radius : ℝ) <
      (((|a| *v.radius)/b : ℤ)+1 : ℝ)*(b : ℝ) := by exact_mod_cast hrad
  unfold Holds scale
  push_cast
  apply (mul_le_mul_iff_of_pos_left hb').mp
  rw [← abs_of_pos hb',← abs_mul]
  simp only [abs_of_pos hb']
  calc
    _ = |(a : ℝ)*((Q : ℝ)*x-v.center)+
        ((a*v.center : ℤ) : ℝ)-(b : ℝ)*((a*v.center/b : ℤ) : ℝ)| := by
      push_cast
      congr 1
      (field_simp; ring)
    _ ≤ |(a : ℝ)*((Q : ℝ)*x-v.center)| +
        |((a*v.center : ℤ) : ℝ)-(b : ℝ)*((a*v.center/b : ℤ) : ℝ)| := by
      convert abs_add_le ((a : ℝ)*((Q : ℝ)*x-v.center))
        (((a*v.center : ℤ) : ℝ)-(b : ℝ)*((a*v.center/b : ℤ) : ℝ)) using 1; congr 1; ring
    _ ≤ |(a : ℝ)| *(v.radius : ℝ)+(b : ℝ) := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg _)) hround
    _ ≤ _ := by
      rw [← Int.cast_abs] at hrad' ⊢
      nlinarith

lemma holds_mul {Q : ℤ} {a b : Box} {x y : ℝ} (hQ : 0 < Q)
    (hx : Holds Q a x) (hy : Holds Q b y) : Holds Q (mul Q a b) (x*y) := by
  have hQ' : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have ha := radius_nonneg hx
  have hb := radius_nonneg hy
  have har : (0 : ℝ) ≤ a.radius := by exact_mod_cast ha
  have hbr : (0 : ℝ) ≤ b.radius := by exact_mod_cast hb
  have hround := rounding_bound (a.center*b.center) Q hQ
  let E : ℤ := |a.center| *b.radius+|b.center| *a.radius+a.radius*b.radius
  have hrad := (quotient_bounds E Q hQ).2
  have hrad' : (E : ℝ) < (((E/Q : ℤ) : ℝ)+1)*(Q : ℝ) := by exact_mod_cast hrad
  have he : |(Q : ℝ)^2*(x*y)-(a.center : ℝ)*b.center| ≤ (E : ℝ) := by
    have hid : (Q : ℝ)^2*(x*y)-(a.center : ℝ)*b.center =
        (a.center : ℝ)*((Q : ℝ)*y-b.center) +
        (b.center : ℝ)*((Q : ℝ)*x-a.center) +
        ((Q : ℝ)*x-a.center)*((Q : ℝ)*y-b.center) := by ring
    rw [hid]
    calc
      _ ≤ |(a.center : ℝ)*((Q : ℝ)*y-b.center)| +
          |(b.center : ℝ)*((Q : ℝ)*x-a.center)| +
          |((Q : ℝ)*x-a.center)*((Q : ℝ)*y-b.center)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ |(a.center : ℝ)| *b.radius+|(b.center : ℝ)| *a.radius+
          (a.radius : ℝ)*b.radius := by
        simp only [abs_mul]
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hy (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hx (abs_nonneg _)))
          (mul_le_mul hx hy (abs_nonneg _) har)
      _ = _ := by simp [E]
  unfold Holds mul
  push_cast
  apply (mul_le_mul_iff_of_pos_left hQ').mp
  rw [← abs_of_pos hQ',← abs_mul]
  simp only [abs_of_pos hQ']
  calc
    _ = |((Q : ℝ)^2*(x*y)-(a.center : ℝ)*b.center)+
      ((a.center*b.center : ℤ) : ℝ)-(Q : ℝ)*((a.center*b.center/Q : ℤ) : ℝ)| := by
      push_cast
      congr 1
      ring
    _ ≤ |(Q : ℝ)^2*(x*y)-(a.center : ℝ)*b.center| +
      |((a.center*b.center : ℤ) : ℝ)-(Q : ℝ)*((a.center*b.center/Q : ℤ) : ℝ)| := by
      convert abs_add_le ((Q : ℝ)^2*(x*y)-(a.center : ℝ)*b.center)
        (((a.center*b.center : ℤ) : ℝ)-(Q : ℝ)*((a.center*b.center/Q : ℤ) : ℝ)) using 1; congr 1; ring
    _ ≤ (E : ℝ)+(Q : ℝ) := add_le_add he hround
    _ ≤ _ := by
      change (E : ℝ)+(Q : ℝ) ≤ (Q : ℝ)*(((E/Q : ℤ) : ℝ)+2)
      nlinarith

lemma holds_ofRat {Q a b : ℤ} (_hQ : 0 < Q) (hb : 0 < b) :
    Holds Q (ofRat Q a b) ((a : ℝ)/(b : ℝ)) := by
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have hr := rounding_bound (Q*a) b hb
  unfold Holds ofRat
  push_cast
  apply (mul_le_mul_iff_of_pos_left hb').mp
  rw [← abs_of_pos hb',← abs_mul]
  simp only [abs_of_pos hb']
  have hh : (b : ℝ)*((Q : ℝ)*((a : ℝ)/(b : ℝ))-((Q*a/b : ℤ) : ℝ)) =
      ((Q*a : ℤ) : ℝ)-(b : ℝ)*((Q*a/b : ℤ) : ℝ) := by
    push_cast
    field_simp
  rw [hh]
  simpa using hr

end SepticProfile.FixedInterval

namespace SepticProfile.FixedInterval
open Finset

def treeSumBox : ℕ → (ℕ → Box) → ℕ → Box
  | 0, f, a => f a
  | d+1, f, a => add (treeSumBox d f a) (treeSumBox d f (a+2^d))

lemma holds_treeSumBox {Q : ℤ} (d : ℕ) (f : ℕ → Box) (g : ℕ → ℝ) (a : ℕ)
    (hf : ∀ i<2^d, Holds Q (f (a+i)) (g (a+i))) :
    Holds Q (treeSumBox d f a) (∑ i ∈ range (2^d), g (a+i)) := by
  induction d generalizing a with
  | zero => simpa [treeSumBox] using hf 0 (by simp)
  | succ d ih =>
    rw [treeSumBox,pow_succ,Nat.mul_two,Finset.sum_range_add]
    have h1 := ih a (fun i hi => hf i (by rw [pow_succ,Nat.mul_two]; omega))
    have h2 := ih (a+2^d) (fun i hi => by
      simpa only [Nat.add_assoc] using hf (2^d+i) (by rw [pow_succ,Nat.mul_two]; omega))
    convert holds_add h1 h2 using 1
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    omega

def sumBox (d lo hi : ℕ) (f : ℕ → Box) : Box :=
  treeSumBox d (fun i => if lo ≤ i ∧ i < hi then f i else zero) 0

lemma holds_sumBox {Q : ℤ} (d lo hi : ℕ) (f : ℕ → Box) (g : ℕ → ℝ)
    (hbound : hi ≤ 2^d) (hf : ∀ i, lo ≤ i → i < hi → Holds Q (f i) (g i)) :
    Holds Q (sumBox d lo hi f) (∑ i ∈ Ico lo hi, g i) := by
  have hs := holds_treeSumBox d (fun i => if lo ≤ i ∧ i < hi then f i else zero)
    (fun i => if lo ≤ i ∧ i < hi then g i else 0) 0 (by
      intro i hi'
      simp only [zero_add]
      split_ifs with h
      · exact hf i h.1 h.2
      · exact holds_zero Q)
  change Holds Q (sumBox d lo hi f) _ at hs
  convert hs using 1
  simp only [zero_add]
  symm
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [mem_filter,mem_range,mem_Ico]
  omega

def convBox (Q : ℤ) (d lo hi : ℕ) (a b : ℕ → Box) (n : ℕ) : Box :=
  sumBox d lo hi (fun i => mul Q (a i) (b (n-i)))

lemma holds_convBox {Q : ℤ} (hQ : 0 < Q) (d lo hi : ℕ) (a b : ℕ → Box)
    (f g : ℕ → ℝ) (n : ℕ) (hbound : hi ≤ 2^d)
    (hf : ∀ i, lo ≤ i → i < hi → Holds Q (a i) (f i))
    (hg : ∀ i, lo ≤ i → i < hi → Holds Q (b (n-i)) (g (n-i))) :
    Holds Q (convBox Q d lo hi a b n) (∑ i ∈ Ico lo hi, f i*g (n-i)) := by
  apply holds_sumBox d lo hi _ _ hbound
  intro i hi hi'
  exact holds_mul hQ (hf i hi hi') (hg i hi hi')

lemma holds_exact (Q a : ℤ) : Holds Q ⟨Q*a,0⟩ (a : ℝ) := by
  simp [Holds]

lemma holds_enlarge {Q : ℤ} {a b : Box} {x : ℝ}
    (hab : |a.center-b.center|+a.radius ≤ b.radius)
    (hx : Holds Q a x) : Holds Q b x := by
  have hab' : |(a.center : ℝ)-b.center|+(a.radius : ℝ) ≤ b.radius := by exact_mod_cast hab
  calc
    _ = |((Q : ℝ)*x-a.center)+((a.center : ℝ)-b.center)| := by congr 1; ring
    _ ≤ |(Q : ℝ)*x-a.center|+|(a.center : ℝ)-b.center| := abs_add_le _ _
    _ ≤ _ := by unfold Holds at hx; linarith

end SepticProfile.FixedInterval

namespace SepticProfile.FixedInterval

def rscale (a : ℚ) (v : Box) : Box := scale a.num a.den v

def ratBox (Q : ℤ) (a : ℚ) : Box := ofRat Q a.num a.den

lemma holds_rscale {Q : ℤ} (a : ℚ) {v : Box} {x : ℝ}
    (hx : Holds Q v x) : Holds Q (rscale a v) ((a : ℝ)*x) := by
  have hd : (0 : ℤ)<a.den := by exact_mod_cast a.den_pos
  simpa only [rscale,Rat.cast_def,Int.cast_natCast] using holds_scale hd hx

lemma holds_ratBox {Q : ℤ} (hQ : 0<Q) (a : ℚ) :
    Holds Q (ratBox Q a) (a : ℝ) := by
  have hd : (0 : ℤ)<a.den := by exact_mod_cast a.den_pos
  simpa only [ratBox,Rat.cast_def,Int.cast_natCast] using holds_ofRat hQ hd (a := a.num)

end SepticProfile.FixedInterval

namespace SepticProfile.JetTrace
open FixedInterval Finset

structure Parameters where
  (p0 p1 p2 p3 i10 i11 i20 i21 i30 i31 i40 i41 h a : ℚ)

structure Trace where
  (w b c d br r : ℕ → Box)

def linear (p : Parameters) (k : ℕ) : ℚ := -2*p.p0*p.a*(k+1)+p.h*p.i10

def stepBox (p : Parameters) (t : Trace) (k : ℕ) : Box :=
  add (add (add (add
    (rscale (-p.p0*(k+1)) (add (t.br k) (rscale (1/3) (t.c (k+1)))))
    (rscale (-p.p1*k) (add (t.b k) (rscale (1/3) (t.c k)))))
    (rscale (-p.p2*(k-1)) (add (t.b (k-1)) (rscale (1/3) (t.c (k-1))))))
    (rscale (-p.p3*(k-2)) (add (t.b (k-2)) (rscale (1/3) (t.c (k-2))))))
    (rscale p.h (add (add (add (add (add (add
      (rscale p.i11 (t.w (k-1))) (rscale p.i20 (t.b k)))
      (rscale p.i21 (t.b (k-1)))) (rscale p.i30 (t.c k)))
      (rscale p.i31 (t.c (k-1)))) (rscale p.i40 (t.d k)))
      (rscale p.i41 (t.d (k-1)))))

def stepValue (p : Parameters) (w b c d br : ℕ → ℝ) (k : ℕ) : ℝ :=
  ((-p.p0*(k+1) : ℚ) : ℝ)*(br k+(1/3 : ℚ)*c (k+1))+
    ((-p.p1*k : ℚ) : ℝ)*(b k+(1/3 : ℚ)*c k)+
    ((-p.p2*(k-1) : ℚ) : ℝ)*(b (k-1)+(1/3 : ℚ)*c (k-1))+
    ((-p.p3*(k-2) : ℚ) : ℝ)*(b (k-2)+(1/3 : ℚ)*c (k-2))+
    (p.h : ℝ)*((p.i11 : ℝ)*w (k-1)+(p.i20 : ℝ)*b k+
      (p.i21 : ℝ)*b (k-1)+(p.i30 : ℝ)*c k+(p.i31 : ℝ)*c (k-1)+
      (p.i40 : ℝ)*d k+(p.i41 : ℝ)*d (k-1))

lemma holds_stepBox {Q : ℤ} (p : Parameters) (t : Trace) (w b c d br : ℕ → ℝ)
    (k : ℕ) (hw : Holds Q (t.w (k-1)) (w (k-1)))
    (hb : ∀ j≤k, Holds Q (t.b j) (b j))
    (hc : ∀ j≤k+1, Holds Q (t.c j) (c j))
    (hd : ∀ j≤k, Holds Q (t.d j) (d j))
    (hbr : Holds Q (t.br k) (br k)) :
    Holds Q (stepBox p t k) (stepValue p w b c d br k) := by
  unfold stepBox stepValue
  apply holds_add
  · apply holds_add
    · apply holds_add
      · apply holds_add
        · apply holds_rscale
          exact holds_add hbr (holds_rscale _ (hc _ (by omega)))
        · apply holds_rscale
          exact holds_add (hb _ (by omega)) (holds_rscale _ (hc _ (by omega)))
      · apply holds_rscale
        exact holds_add (hb _ (by omega)) (holds_rscale _ (hc _ (by omega)))
    · apply holds_rscale
      exact holds_add (hb _ (by omega)) (holds_rscale _ (hc _ (by omega)))
  · apply holds_rscale
    apply holds_add
    · apply holds_add
      · apply holds_add
        · apply holds_add
          · apply holds_add
            · apply holds_add
              · exact holds_rscale _ hw
              · exact holds_rscale _ (hb _ (by omega))
            · exact holds_rscale _ (hb _ (by omega))
          · exact holds_rscale _ (hc _ (by omega))
        · exact holds_rscale _ (hc _ (by omega))
      · exact holds_rscale _ (hd _ (by omega))
    · exact holds_rscale _ (hd _ (by omega))

structure Valid (Q : ℤ) (D N : ℕ) (p : Parameters) (t : Trace) : Prop where
  initial0 : t.w 0=zero
  initial1 : t.w 1=ratBox Q p.a
  square : ∀ n≤N, t.b n=convBox Q D 1 n t.w t.w n
  cube : ∀ n≤N+1, t.c n=convBox Q D 1 (n-1) t.w t.b n
  fourth : ∀ n≤N, t.d n=convBox Q D 2 (n-1) t.b t.b n
  squareR : ∀ n, 2≤n → n≤N → t.br n=convBox Q D 2 n t.w t.w (n+1)
  residue : ∀ n, 2≤n → n≤N → t.r n=stepBox p t n
  update : ∀ n, 2≤n → n≤N → t.w n=rscale (-1/linear p n) (t.r n)
  nonzero : ∀ n, 2≤n → n≤N → linear p n≠0

end SepticProfile.JetTrace

namespace SepticProfile.JetTrace
open FixedInterval Finset

/-- Soundness of the finite integer trace. Its hypotheses are arithmetic
identities checked from the data and the exact coefficient recurrence; no
profile or endpoint inequality is assumed. -/
theorem coefficients_enclosed {Q : ℤ} (hQ : 0<Q) (D N : ℕ) (hN : N+1≤2^D)
    (p : Parameters) (t : Trace) (ht : Valid Q D N p t)
    (w b c d br : ℕ → ℝ) (hw0 : w 0=0) (hw1 : w 1=(p.a : ℝ))
    (hb : ∀ j, b j=∑ i ∈ Ico 1 j, w i*w (j-i))
    (hc : ∀ j, c j=∑ i ∈ Ico 1 (j-1), w i*b (j-i))
    (hd : ∀ j, d j=∑ i ∈ Ico 2 (j-1), b i*b (j-i))
    (hbr : ∀ j, br j=∑ i ∈ Ico 2 j, w i*w (j+1-i))
    (he : ∀ j, 2≤j → j≤N → (linear p j : ℝ)*w j+stepValue p w b c d br j=0) :
    ∀ j≤N, Holds Q (t.w j) (w j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    by_cases hk0 : k=0
    · subst k
      rw [hw0,ht.initial0]
      exact holds_zero Q
    by_cases hk1 : k=1
    · subst k
      rw [hw1,ht.initial1]
      exact holds_ratBox hQ p.a
    have hk2 : 2≤k := by omega
    have hbk : ∀ j≤k, Holds Q (t.b j) (b j) := by
      intro j hj
      rw [ht.square j (by omega),hb j]
      apply holds_convBox hQ D 1 j _ _ w w j (by omega)
      · intro i hi hi'
        exact ih i (by omega) (by omega)
      · intro i hi hi'
        exact ih (j-i) (by omega) (by omega)
    have hck : ∀ j≤k+1, Holds Q (t.c j) (c j) := by
      intro j hj
      rw [ht.cube j (by omega),hc j]
      apply holds_convBox hQ D 1 (j-1) _ _ w b j (by omega)
      · intro i hi hi'
        exact ih i (by omega) (by omega)
      · intro i hi hi'
        exact hbk (j-i) (by omega)
    have hdk : ∀ j≤k, Holds Q (t.d j) (d j) := by
      intro j hj
      rw [ht.fourth j (by omega),hd j]
      apply holds_convBox hQ D 2 (j-1) _ _ b b j (by omega)
      · intro i hi hi'
        exact hbk i (by omega)
      · intro i hi hi'
        exact hbk (j-i) (by omega)
    have hbrk : Holds Q (t.br k) (br k) := by
      rw [ht.squareR k hk2 hk,hbr k]
      apply holds_convBox hQ D 2 k _ _ w w (k+1) (by omega)
      · intro i hi hi'
        exact ih i (by omega) (by omega)
      · intro i hi hi'
        exact ih (k+1-i) (by omega) (by omega)
    have hr := holds_stepBox p t w b c d br k
      (ih (k-1) (by omega) (by omega)) hbk hck hdk hbrk
    have he' := he k hk2 hk
    have hn : (linear p k : ℝ)≠0 := by exact_mod_cast ht.nonzero k hk2 hk
    have hf : w k=((-1/linear p k : ℚ) : ℝ)*stepValue p w b c d br k := by
      push_cast
      field_simp
      linear_combination he'
    rw [hf,ht.update k hk2 hk,ht.residue k hk2 hk]
    exact holds_rscale _ hr

end SepticProfile.JetTrace

namespace SepticProfile.JetTrace
open PowerSeries Finset

def sourceParams (sigma kappa c h a : ℚ) : Parameters where
  p0 := 1-sigma
  p1 := -2-(1+h)+3*sigma*(1+h)
  p2 := 1+2*(1+h)-3*sigma*(1+h)^2
  p3 := -(1+h)+sigma*(1+h)^3
  i10 := -(1-c)*(2*kappa+3)
  i11 := (1-c)*(2*kappa*(1+h)+3)+6*c*h
  i20 := kappa*(-(1-c)+4*c)+6*c
  i21 := -kappa*(-(1-c)+4*c)*(1+h)-6*c+3*c*h
  i30 := 4*c*kappa+3*c
  i31 := -4*c*kappa*(1+h)-3*c
  i40 := c*kappa
  i41 := -c*kappa*(1+h)
  h := h
  a := a

lemma source_recurrence (sigma kappa c h a : ℚ) (w : EulerFormal.Series)
    (hw0 : coeff 0 w=0) (hw1 : coeff 1 w=(a : ℝ))
    (he : EulerFormal.residual sigma kappa c h (1+w)=0) (k : ℕ) (hk : 2≤k) :
    (linear (sourceParams sigma kappa c h a) k : ℝ)*coeff k w+
      stepValue (sourceParams sigma kappa c h a)
        (fun i => coeff i w) (fun i => coeff i (w^2)) (fun i => coeff i (w^3))
        (fun i => coeff i (w^4))
        (fun j => ∑ i ∈ Ico 2 j, coeff i w*coeff (j+1-i) w) k=0 := by
  obtain ⟨n,rfl⟩ : ∃ n, k=n+2 := ⟨k-2,by omega⟩
  have hh := EulerFormal.coefficient_equation (sigma : ℝ) kappa c h w n he
  have hs := EulerFormal.coeff_square_remainder w hw0 (n+2) (by omega)
  rw [hw1] at hs
  rw [hs] at hh
  unfold linear stepValue sourceParams
  simp only [show n+2-1=n+1 by omega,Nat.add_sub_cancel_right]
  simp only [EulerFormal.p0,EulerFormal.p1,EulerFormal.p2,EulerFormal.p3,
    EulerFormal.i10,EulerFormal.i11,EulerFormal.i20,EulerFormal.i21,EulerFormal.i30,
    EulerFormal.i31,EulerFormal.i40,EulerFormal.i41] at hh
  push_cast
  linear_combination hh

theorem source_coefficients_enclosed {Q : ℤ} (hQ : 0<Q) (D N : ℕ) (hN : N+1≤2^D)
    (sigma kappa c h a : ℚ) (t : Trace)
    (ht : Valid Q D N (sourceParams sigma kappa c h a) t)
    (w : EulerFormal.Series) (hw0 : coeff 0 w=0) (hw1 : coeff 1 w=(a : ℝ))
    (he : EulerFormal.residual sigma kappa c h (1+w)=0) :
    ∀ j≤N, FixedInterval.Holds Q (t.w j) (coeff j w) := by
  apply coefficients_enclosed hQ D N hN (sourceParams sigma kappa c h a) t ht
    (fun i => coeff i w) (fun i => coeff i (w^2)) (fun i => coeff i (w^3))
    (fun i => coeff i (w^4))
    (fun j => ∑ i ∈ Ico 2 j, coeff i w*coeff (j+1-i) w) hw0 hw1
  · exact EulerFormal.coeff_square w hw0
  · exact EulerFormal.coeff_cube w hw0
  · exact EulerFormal.coeff_fourth w hw0
  · intro j
    rfl
  · intro j hj hj'
    exact source_recurrence sigma kappa c h a w hw0 hw1 he j hj

end SepticProfile.JetTrace

namespace SepticProfile.EulerFormal
open PowerSeries

lemma residual_direct (sigma kappa c h : ℝ) (u : Series) :
    residual sigma kappa c h u =
      pref sigma h*(derivative u-C (1/3)*derivative (u^3))+
      C h*(C (kappa+3)*B h-3*A*u-C (kappa+c*(kappa+3))*B h*u^2+
        C (3*c)*A*u^3+C (c*kappa)*B h*u^4) := by
  unfold residual
  simp only [derivative_pow]
  norm_num only [Nat.cast_ofNat,map_add,map_mul,map_ofNat]
  have hc : (C (1/3) : Series)*3=1 := by
    rw [← map_ofNat C 3,← map_mul]
    norm_num
  have h3 : ∀ v : Series, C (1/3)*(3*v)=v := by intro v; rw [← mul_assoc,hc,one_mul]
  simp only [mul_assoc,h3]
  ring

lemma coeff_B_mul (h : ℝ) (u : Series) (n : ℕ) :
    coeff (n+1) (B h*u)=coeff (n+1) u-(1+h)*coeff n u := by
  simp only [B,sub_mul,one_mul,mul_assoc,map_sub (coeff (n+1)),coeff_C_mul,coeff_succ_X_mul]

lemma coeff_A_mul (u : Series) (n : ℕ) :
    coeff (n+1) (A*u)=coeff (n+1) u-coeff n u := by
  simp [A,sub_mul,coeff_succ_X_mul]

lemma coeff_B_high (h : ℝ) (n : ℕ) : coeff (n+2) (B h)=0 := by
  simp [B]

lemma residual_coeff_direct (sigma kappa c h : ℝ) (u : Series) (n : ℕ) :
    coeff (n+2) (residual sigma kappa c h u)=
    p0 sigma h*(n+3)*(coeff (n+3) u-coeff (n+3) (u^3)/3)+
    p1 sigma h*(n+2)*(coeff (n+2) u-coeff (n+2) (u^3)/3)+
    p2 sigma h*(n+1)*(coeff (n+1) u-coeff (n+1) (u^3)/3)+
    p3 sigma h*n*(coeff n u-coeff n (u^3)/3)+
    h*(-3*coeff (n+2) u+3*coeff (n+1) u-
      (kappa+c*(kappa+3))*coeff (n+2) (u^2)+
      (kappa+c*(kappa+3))*(1+h)*coeff (n+1) (u^2)+
      3*c*coeff (n+2) (u^3)-3*c*coeff (n+1) (u^3)+
      c*kappa*coeff (n+2) (u^4)-c*kappa*(1+h)*coeff (n+1) (u^4)) := by
  rw [residual_direct]
  have hx : pref sigma h*(derivative u-C (1/3)*derivative (u^3))=
    pref sigma h*derivative u-C (1/3)*(pref sigma h*derivative (u^3)) := by ring
  rw [hx]
  have h2 : 3*A*u=(C 3)*(A*u) := by rw [map_ofNat]; ring
  rw [h2]
  simp only [mul_assoc,coeff_C_mul,map_add (coeff (n+2)),map_sub (coeff (n+2)),coeff_pref_derivative,
    coeff_B_mul,coeff_A_mul,coeff_B_high,mul_zero]
  ring

/-- Tangency of the sonic vector-field divisor prevents loss of one order in
its residual. This is the reason finite jets suffice for the barrier. -/
lemma residual_congr_X_pow (sigma kappa c h : ℝ) (u v : Series) (m : ℕ)
    (hm : 1  ≤  m) (hu0 : coeff 0 u=1) (hdiv : X^m  ∣  u-v) :
    X^m  ∣  residual sigma kappa c h u-residual sigma kappa c h v := by
  obtain ⟨w,hw⟩ := hdiv
  have hu : u=v+X^m*w := by linear_combination hw
  have hu2 : X^m  ∣  u^2-v^2 := by
    refine ⟨w*(u+v),?_⟩
    linear_combination (u+v)*hw
  have hx : X  ∣  1-u^2 := by
    rw [X_dvd_iff]
    have hu0' : constantCoeff u=1 := by simpa using hu0
    simp only [map_sub,map_one,map_pow,hu0',one_pow,sub_self]
  obtain ⟨z,hz⟩ := hx
  have hd : derivative u-derivative v=
      (m : ℝ) • (X^(m-1)*w)+X^m*derivative w := by
    rw [hu,map_add,add_sub_cancel_left,Derivation.leibniz,derivative_pow,derivative_X]
    simp only [mul_one]
    simp only [Algebra.smul_def,Algebra.algebraMap_self_apply]
    push_cast
    ring
  have hd1 : X^m  ∣  (1-u^2)*(derivative u-derivative v) := by
    refine ⟨(m : ℝ) • (z*w)+X*z*derivative w,?_⟩
    rw [hd,hz]
    simp only [Algebra.smul_def]
    have hp : X*X^(m-1)=(X : Series)^m := by rw [← pow_succ']; congr 1; omega
    calc
      _ = (m : ℝ) • ((X*X^(m-1))*(z*w))+X^m*(X*z*derivative w) := by
        simp only [Algebra.smul_def]; ring
      _ = _ := by rw [hp]; simp only [Algebra.smul_def]; ring
  have hu2' : X^m  ∣  (1-u^2)-(1-v^2) := by
    (convert hu2.neg_right using 1; ring)
  have hres1 : X^m  ∣  (1-u^2)*derivative u-(1-v^2)*derivative v := by
    have := hd1.add (hu2'.mul_right (derivative v))
    (convert this using 1; ring)
  have hbr : X^m  ∣  (C kappa*B h*(1-u^2)+3*(B h-A*u))-
      (C kappa*B h*(1-v^2)+3*(B h-A*v)) := by
    have h12 := hu2'.mul_left (C kappa*B h)
    have h13 : X^m  ∣  -3*A*(u-v) := (show X^m  ∣  u-v from ⟨w,hw⟩).mul_left (-3*A)
    (convert h12.add h13 using 1; ring)
  have hup : X^m  ∣  (1-C c*u^2)-(1-C c*v^2) := by
    (convert hu2.mul_left (-C c) using 1; ring)
  have hres2 := (hbr.mul_left (1-C c*u^2)).add
    (hup.mul_right (C kappa*B h*(1-v^2)+3*(B h-A*v)))
  have hh := (hres1.mul_left (pref sigma h)).add (hres2.mul_left (C h))
  (convert hh using 1; unfold residual; ring)

end SepticProfile.EulerFormal

namespace SepticProfile.FixedInterval
open PowerSeries Finset

lemma coeff_mul_support (f g : PowerSeries ℝ) (A B n : ℕ)
    (hf : ∀ i, A ≤ i → coeff i f=0) (hg : ∀ i, B ≤ i → coeff i g=0) :
    coeff n (f*g)=∑ i ∈ Ico (n+1-B) (min A (n+1)), coeff i f*coeff (n-i) g := by
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  symm
  apply Finset.sum_subset
  · intro i hi
    simp only [mem_Ico,mem_range] at hi ⊢
    omega
  · intro i hi hnot
    have hi' := mem_range.mp hi
    by_cases ha : A ≤ i
    · rw [hf i ha,zero_mul]
    · have hb : B ≤ n-i := by
        simp only [mem_Ico,not_and] at hnot
        omega
      rw [hg (n-i) hb,mul_zero]

lemma coeff_mul_support_zero (f g : PowerSeries ℝ) (A B n : ℕ)
    (hf : ∀ i, A ≤ i → coeff i f=0) (hg : ∀ i, B ≤ i → coeff i g=0)
    (hn : A+B-1 ≤ n) : coeff n (f*g)=0 := by
  rw [coeff_mul_support f g A B n hf hg]
  have : Ico (n+1-B) (min A (n+1))=∅ := by apply Ico_eq_empty_of_le; omega
  rw [this,sum_empty]

lemma holds_poly_conv {Q : ℤ} (hQ : 0<Q) (D A B n : ℕ) (hA : A ≤ 2^D)
    (f g : PowerSeries ℝ) (a b : ℕ → Box)
    (hf : ∀ i, A ≤ i → coeff i f=0) (hg : ∀ i, B ≤ i → coeff i g=0)
    (ha : ∀ i, Holds Q (a i) (coeff i f)) (hb : ∀ i, Holds Q (b i) (coeff i g)) :
    Holds Q (convBox Q D (n+1-B) (min A (n+1)) a b n) (coeff n (f*g)) := by
  rw [coeff_mul_support f g A B n hf hg]
  apply holds_convBox hQ D (n+1-B) (min A (n+1)) a b (fun i => coeff i f) (fun i => coeff i g) n
  · exact le_trans (min_le_left _ _) hA
  · intro i _ _; exact ha i
  · intro i _ _; exact hb _

end SepticProfile.FixedInterval

namespace SepticProfile.BarrierTrace
open FixedInterval Finset

structure Parameters where
  (p0 p1 p2 p3 b20 b21 b30 b31 b40 b41 h : ℚ)

def sourceParams (sigma kappa c h : ℚ) : Parameters where
  p0 := 1-sigma
  p1 := -2-(1+h)+3*sigma*(1+h)
  p2 := 1+2*(1+h)-3*sigma*(1+h)^2
  p3 := -(1+h)+sigma*(1+h)^3
  b20 := -(kappa+c*(kappa+3))
  b21 := (kappa+c*(kappa+3))*(1+h)
  b30 := 3*c
  b31 := -3*c
  b40 := c*kappa
  b41 := -c*kappa*(1+h)
  h := h

structure Trace where
  (u b c d r : ℕ → Box)

def residualBox (p : Parameters) (t : Trace) (k : ℕ) : Box :=
  add (add (add (add
    (rscale (p.p0*(k+1)) (sub (t.u (k+1)) (rscale (1/3) (t.c (k+1)))))
    (rscale (p.p1*k) (sub (t.u k) (rscale (1/3) (t.c k)))))
    (rscale (p.p2*(k-1)) (sub (t.u (k-1)) (rscale (1/3) (t.c (k-1))))))
    (rscale (p.p3*(k-2)) (sub (t.u (k-2)) (rscale (1/3) (t.c (k-2))))))
    (rscale p.h (add (add (add (add (add (add (add
      (rscale (-3) (t.u k)) (rscale 3 (t.u (k-1))))
      (rscale p.b20 (t.b k))) (rscale p.b21 (t.b (k-1))))
      (rscale p.b30 (t.c k))) (rscale p.b31 (t.c (k-1))))
      (rscale p.b40 (t.d k))) (rscale p.b41 (t.d (k-1)))))

lemma residual_enclosed {Q : ℤ} (sigma kappa c h : ℚ) (t : Trace)
    (u : EulerFormal.Series) (k : ℕ) (hk : 2 ≤ k)
    (hu : ∀ i, Holds Q (t.u i) (PowerSeries.coeff i u))
    (hb : ∀ i, Holds Q (t.b i) (PowerSeries.coeff i (u^2)))
    (hc : ∀ i, Holds Q (t.c i) (PowerSeries.coeff i (u^3)))
    (hd : ∀ i, Holds Q (t.d i) (PowerSeries.coeff i (u^4))) :
    Holds Q (residualBox (sourceParams sigma kappa c h) t k)
      (PowerSeries.coeff k (EulerFormal.residual sigma kappa c h u)) := by
  obtain ⟨n,rfl⟩ : ∃ n, k=n+2 := ⟨k-2,by omega⟩
  rw [EulerFormal.residual_coeff_direct]
  unfold residualBox sourceParams
  simp only [show n+2-1=n+1 by omega,Nat.add_sub_cancel_right]
  have hs : ∀ b : Box, ∀ x : ℝ, ∀ r : ℚ, Holds Q b x → Holds Q (rscale r b) ((r : ℝ)*x) :=
    fun _ _ _ hx => holds_rscale _ hx
  have hbound := holds_add (holds_add (holds_add (holds_add
    (hs _ _ ((1-sigma)*(n+2+1)) (holds_sub (hu (n+2+1)) (hs _ _ (1/3) (hc (n+2+1)))))
    (hs _ _ ((-2-(1+h)+3*sigma*(1+h))*(n+2)) (holds_sub (hu (n+2)) (hs _ _ (1/3) (hc (n+2))))))
    (hs _ _ ((1+2*(1+h)-3*sigma*(1+h)^2)*(n+1)) (holds_sub (hu (n+1)) (hs _ _ (1/3) (hc (n+1))))))
    (hs _ _ ((-(1+h)+sigma*(1+h)^3)*n) (holds_sub (hu n) (hs _ _ (1/3) (hc n)))) )
    (hs _ _ h (holds_add (holds_add (holds_add (holds_add (holds_add (holds_add (holds_add
      (hs _ _ (-3) (hu (n+2))) (hs _ _ 3 (hu (n+1))))
      (hs _ _ (-(kappa+c*(kappa+3))) (hb (n+2))))
      (hs _ _ ((kappa+c*(kappa+3))*(1+h)) (hb (n+1))))
      (hs _ _ (3*c) (hc (n+2)))) (hs _ _ (-3*c) (hc (n+1))))
      (hs _ _ (c*kappa) (hd (n+2)))) (hs _ _ (-c*kappa*(1+h)) (hd (n+1)))))
  convert hbound using 1
  · push_cast
    (congr 1; congr 1; congr 1)
    all_goals (congr 1; ring)
  · unfold EulerFormal.p0 EulerFormal.p1 EulerFormal.p2 EulerFormal.p3
    push_cast
    ring

end SepticProfile.BarrierTrace

namespace SepticProfile.FixedInterval

lemma holds_change_scale {Q S : ℤ} (hS : 0<S) {b : Box} {x : ℝ}
    (hx : Holds (Q*S) b x) : Holds Q (scale 1 S b) x := by
  have hs' : (S : ℝ)≠0 := by exact_mod_cast ne_of_gt hS
  have hh := holds_scale (a := 1) hS hx
  unfold Holds at hh ⊢
  push_cast at hh
  convert hh using 1
  field_simp

lemma bounds {Q : ℤ} {b : Box} {x : ℝ} (hx : Holds Q b x) :
    (b.center : ℝ)-b.radius ≤ (Q : ℝ)*x ∧
      (Q : ℝ)*x ≤ (b.center : ℝ)+b.radius := by
  have := abs_le.mp hx
  constructor <;> linarith

lemma abs_bound {Q : ℤ} {b : Box} {x : ℝ} (hx : Holds Q b x) :
    |(Q : ℝ)*x| ≤ (|b.center|+b.radius : ℤ) := by
  calc
    _ = |((Q : ℝ)*x-b.center)+(b.center : ℝ)| := by congr 1; ring
    _ ≤ |(Q : ℝ)*x-b.center|+|(b.center : ℝ)| := abs_add_le _ _
    _ ≤ _ := by norm_cast; simpa [add_comm] using add_le_add_right hx |(b.center : ℝ)|

end SepticProfile.FixedInterval

namespace SepticProfile.BarrierTrace
open FixedInterval PowerSeries

structure ValidPowers (Q : ℤ) (D N : ℕ) (t : Trace) : Prop where
  square : ∀ n, n≤2*N → t.b n=convBox Q D (n-N) (min (N+1) (n+1)) t.u t.u n
  cube : ∀ n, n≤3*N → t.c n=convBox Q D (n-2*N) (min (N+1) (n+1)) t.u t.b n
  fourth : ∀ n, n≤4*N → t.d n=convBox Q D (n-2*N) (min (2*N+1) (n+1)) t.b t.b n
  bZero : ∀ n, 2*N<n → t.b n=zero
  cZero : ∀ n, 3*N<n → t.c n=zero
  dZero : ∀ n, 4*N<n → t.d n=zero

lemma powers_enclosed {Q : ℤ} (hQ : 0<Q) (D N : ℕ) (hD : 2*N+1≤2^D)
    (t : Trace) (ht : ValidPowers Q D N t) (u : EulerFormal.Series)
    (hu : ∀ n, Holds Q (t.u n) (coeff n u))
    (hu0 : ∀ n, N<n → coeff n u=0) :
    (∀ n, Holds Q (t.b n) (coeff n (u^2))) ∧
    (∀ n, Holds Q (t.c n) (coeff n (u^3))) ∧
    (∀ n, Holds Q (t.d n) (coeff n (u^4))) := by
  have hs1 : ∀ n, N+1≤n → coeff n u=0 := by intro n hn; exact hu0 n (by omega)
  have hs2 : ∀ n, 2*N<n → coeff n (u^2)=0 := by
    intro n hn
    rw [pow_two]
    exact coeff_mul_support_zero u u (N+1) (N+1) n hs1 hs1 (by omega)
  have hb : ∀ n, Holds Q (t.b n) (coeff n (u^2)) := by
    intro n
    by_cases hn : n≤2*N
    · rw [ht.square n hn,pow_two]
      simpa only [Nat.add_sub_add_right] using holds_poly_conv hQ D (N+1) (N+1) n (by omega) u u t.u t.u hs1 hs1 hu hu
    · rw [ht.bZero n (by omega),hs2 n (by omega)]
      exact holds_zero _
  have hs2' : ∀ n, 2*N+1≤n → coeff n (u^2)=0 := by intro n hn; exact hs2 n (by omega)
  have hc : ∀ n, Holds Q (t.c n) (coeff n (u^3)) := by
    intro n
    rw [show u^3=u*u^2 by ring]
    by_cases hn : n≤3*N
    · rw [ht.cube n hn]
      simpa only [Nat.add_sub_add_right] using holds_poly_conv hQ D (N+1) (2*N+1) n (by omega) u (u^2) t.u t.b hs1 hs2' hu hb
    · rw [ht.cZero n (by omega),coeff_mul_support_zero u (u^2) (N+1) (2*N+1) n hs1 hs2' (by omega)]
      exact holds_zero _
  have hd : ∀ n, Holds Q (t.d n) (coeff n (u^4)) := by
    intro n
    rw [show u^4=u^2*u^2 by ring]
    by_cases hn : n≤4*N
    · rw [ht.fourth n hn]
      simpa only [Nat.add_sub_add_right] using holds_poly_conv hQ D (2*N+1) (2*N+1) n hD (u^2) (u^2) t.b t.b hs2' hs2' hb hb
    · rw [ht.dZero n (by omega),coeff_mul_support_zero (u^2) (u^2) (2*N+1) (2*N+1) n hs2' hs2' (by omega)]
      exact holds_zero _
  exact ⟨hb,hc,hd⟩

end SepticProfile.BarrierTrace

namespace SepticProfile.EulerPolynomial
open Polynomial
noncomputable def residual (sigma kappa c h : ℝ) (p : ℝ[X]) : ℝ[X] :=
  (1-C (1+h)*X)*((1-X)^2-C sigma*(1-C (1+h)*X)^2)*(1-p^2)*derivative p+
    C h*(1-C c*p^2)*(C kappa*(1-C (1+h)*X)*(1-p^2)+3*((1-C (1+h)*X)-(1-X)*p))

lemma coe_residual (sigma kappa c h : ℝ) (p : ℝ[X]) :
    ((residual sigma kappa c h p : ℝ[X]) : PowerSeries ℝ)=
      EulerFormal.residual sigma kappa c h p := by
  have h3 : ((3 : ℝ[X]) : PowerSeries ℝ)=3 := by
    rw [← coeToPowerSeries.ringHom_apply,map_ofNat]
  simp only [residual,EulerFormal.residual,EulerFormal.pref,EulerFormal.A,EulerFormal.B,
    coe_add,coe_mul,coe_sub,coe_pow,coe_one,coe_C,coe_X,h3,PowerSeries.derivative_coe]

lemma eval_residual (sigma kappa c h : ℝ) (p : ℝ[X]) (x : ℝ) :
    (residual sigma kappa c h p).eval x=
      EulerFormal.profileResidual sigma kappa c h (fun t => p.eval t) x := by
  simp [residual,EulerFormal.profileResidual,Polynomial.deriv]

lemma degree_residual (sigma kappa c h : ℝ) (p : ℝ[X]) (hp : p.natDegree≤220) :
    (residual sigma kappa c h p).natDegree≤881 := by
  have hd := natDegree_derivative_le p
  unfold residual
  compute_degree!
  omega

noncomputable def barrier (f : PowerSeries ℝ) (δ : ℝ) : ℝ[X] :=
  PowerSeries.trunc 221 f+C δ*X^140

lemma coeff_barrier (f : PowerSeries ℝ) (δ : ℝ) (n : ℕ) :
    (barrier f δ).coeff n=(if n<221 then PowerSeries.coeff n f else 0)+
      (if n=140 then δ else 0) := by
  unfold barrier
  rw [coeff_add,PowerSeries.coeff_trunc,coeff_C_mul,coeff_X_pow]
  simp only [mul_ite,mul_one,mul_zero]

lemma degree_barrier (f : PowerSeries ℝ) (δ : ℝ) : (barrier f δ).natDegree≤220 := by
  have hp := PowerSeries.natDegree_trunc_lt f 220
  unfold barrier
  apply natDegree_add_le_of_degree_le
  · exact Nat.le_of_lt_succ hp
  · exact (natDegree_C_mul_X_pow_le δ 140).trans (by norm_num)

lemma barrier_congr (f : PowerSeries ℝ) (δ : ℝ) :
    (PowerSeries.X : PowerSeries ℝ)^140 ∣ f-(barrier f δ : PowerSeries ℝ) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro n hn
  rw [map_sub,Polynomial.coeff_coe,coeff_barrier]
  simp [show n<221 by omega,show n≠140 by omega]

lemma residual_lowzero (sigma kappa c h : ℝ) (f : PowerSeries ℝ) (δ : ℝ)
    (hf0 : PowerSeries.coeff 0 f=1) (hf : EulerFormal.residual sigma kappa c h f=0)
    (n : ℕ) (hn : n<140) : (residual sigma kappa c h (barrier f δ)).coeff n=0 := by
  have hh := EulerFormal.residual_congr_X_pow sigma kappa c h f (barrier f δ) 140
    (by norm_num) hf0 (barrier_congr f δ)
  rw [hf,zero_sub,← coe_residual] at hh
  have hh' := PowerSeries.X_pow_dvd_iff.mp hh n hn
  simpa using hh'

lemma eval_factor (p : ℝ[X]) (hp : p.natDegree≤881)
    (hz : ∀ n<140, p.coeff n=0) (x : ℝ) :
    p.eval x=x^140*∑ i ∈ Finset.range 742, p.coeff (i+140)*x^i := by
  rw [eval_eq_sum_range' (show p.natDegree<882 by omega),
    show 882=140+742 by norm_num,Finset.sum_range_add]
  have hzero : ∑ i ∈ Finset.range 140, p.coeff i*x^i=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hz i (Finset.mem_range.mp hi),zero_mul]
  rw [hzero,zero_add,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_add,Nat.add_comm 140 i]
  ring

end SepticProfile.EulerPolynomial


namespace SepticProfile.FixedInterval
open Finset

def treeInt : ℕ → (ℕ → ℤ) → ℕ → ℤ
  | 0,f,a => f a
  | D+1,f,a => treeInt D f a+treeInt D f (a+2^D)

lemma treeInt_eq (D : ℕ) (f : ℕ → ℤ) (a : ℕ) :
    treeInt D f a=∑ i  ∈  range (2^D), f (a+i) := by
  induction D generalizing a with
  | zero => simp [treeInt]
  | succ D ih =>
    rw [treeInt,pow_succ,Nat.mul_two,Finset.sum_range_add,ih,ih]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    omega

def sumInt (D lo hi : ℕ) (f : ℕ → ℤ) : ℤ :=
  treeInt D (fun i => if lo ≤ i ∧ i<hi then f i else 0) 0

lemma sumInt_eq (D lo hi : ℕ) (f : ℕ → ℤ) (hhi : hi ≤ 2^D) :
    sumInt D lo hi f=∑ i  ∈  Ico lo hi, f i := by
  unfold sumInt
  rw [treeInt_eq]
  simp only [zero_add]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [mem_filter,mem_range,mem_Ico]
  omega

def absTail (D lo hi : ℕ) (b : ℕ → Box) : ℤ :=
  sumInt D lo hi (fun i => (|(b i).center|+(b i).radius)*5^i*6^(hi-1-i))

lemma scaled_tail_bound {Q : ℤ} (hQ : 0<Q) (D lo hi : ℕ) (hhi : hi ≤ 2^D)
    (b : ℕ → Box) (a : ℕ → ℝ) (ha : ∀ i ∈ Ico lo hi, Holds Q (b i) (a i))
    {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 5/6) :
    |(Q : ℝ)*6^(hi-1)*(∑ i ∈ Ico lo hi, a i*x^i)|  ≤  (absTail D lo hi b : ℝ) := by
  have hQ' : 0<(Q : ℝ) := by exact_mod_cast hQ
  rw [absTail,sumInt_eq D lo hi _ hhi]
  push_cast
  rw [Finset.mul_sum]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  apply Finset.sum_le_sum
  intro i hi'
  have hi'' := mem_Ico.mp hi'
  have hb := abs_bound (ha i hi')
  have hr : 0 ≤ (|(b i).center|+(b i).radius : ℤ) := by
    exact_mod_cast le_trans (abs_nonneg _) hb
  have hr' : (0:ℝ) ≤ (|(b i).center|+(b i).radius : ℤ) := by exact_mod_cast hr
  have hp : x^i ≤ (5/6:ℝ)^i := pow_le_pow_left₀ hx hx' i
  calc
    _ = |(Q : ℝ)*a i| *6^(hi-1)*x^i := by
      rw [show (Q : ℝ)*6^(hi-1)*(a i*x^i)=((Q : ℝ)*a i)*(6^(hi-1)*x^i) by ring,
        abs_mul,abs_of_nonneg (show (0:ℝ) ≤ 6^(hi-1)*x^i by positivity)]
      ring
    _  ≤  ((|(b i).center|+(b i).radius : ℤ) : ℝ)*6^(hi-1)*(5/6)^i := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hb (by positivity)) hp (by positivity)
        (mul_nonneg hr' (by positivity))
    _ = _ := by
      have he : hi-1=i+(hi-1-i) := by omega
      have hp6 : (6:ℝ)^(hi-1)=6^i*6^(hi-1-i) := by rw [← pow_add,← he]
      rw [hp6,div_pow]
      push_cast
      field_simp

lemma quad_lower {a b c r x : ℝ} (hc : 0 ≤ c) (hder : b+2*r*c ≤ 0)
    (_hx : 0 ≤ x) (hxr : x ≤ r) : a+b*r+c*r^2 ≤ a+b*x+c*x^2 := by
  have h1 : 0 ≤ -b-c*(r+x) := by nlinarith
  have h2 := mul_nonneg (sub_nonneg.mpr hxr) h1
  nlinarith

/-- Finite, exact positivity criterion used by the sonic residual certificate.
The tail is bounded absolutely, not numerically sampled. -/
lemma finite_positive {Q : ℤ} (hQ : 0<Q) (D M : ℕ) (hM : 10 ≤ M) (hD : M ≤ 2^D)
    (b : ℕ → Box) (a : ℕ → ℝ)
    (ha : ∀ i<M, Holds Q (b i) (a i))
    (L0 L1 L2 : ℝ) (h0 : L0 ≤ a 0) (h1 : L1 ≤ a 1) (h2 : L2 ≤ a 2)
    (hmid : ∀ i, 3 ≤ i → i<10 → (b i).radius ≤ (b i).center)
    (hL2 : 0 ≤ L2) (hder : L1+2*(5/6)*L2 ≤ 0)
    (hh : 4/100000000 ≤ L0+L1*(5/6)+L2*(5/6)^2)
    (htail : 100000000*absTail D 10 M b<Q*6^(M-1))
    {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 5/6) : 0<∑ i ∈ range M, a i*x^i := by
  have hQ' : 0<(Q : ℝ) := by exact_mod_cast hQ
  have hd : 0<(Q : ℝ)*6^(M-1) := by positivity
  have htail' : (100000000 : ℝ)*(absTail D 10 M b : ℝ)<(Q : ℝ)*6^(M-1) := by exact_mod_cast htail
  have hab := scaled_tail_bound hQ D 10 M hD b a (by intro i hi; exact ha i (mem_Ico.mp hi).2) hx hx'
  have hlo : -(1/100000000 : ℝ)<∑ i ∈ Ico 10 M, a i*x^i := by
    have hab' := (neg_le_abs ((Q : ℝ)*6^(M-1)*∑ i ∈ Ico 10 M, a i*x^i)).trans hab
    by_contra hn
    have hn' : (∑ i ∈ Ico 10 M, a i*x^i) ≤  -(1/100000000 : ℝ) := le_of_not_gt hn
    have hh' := mul_le_mul_of_nonneg_left hn' (le_of_lt hd)
    nlinarith
  have hmid' : 0 ≤ ∑ i ∈ Ico 3 10, a i*x^i := by
    apply Finset.sum_nonneg
    intro i hi
    have hi' := mem_Ico.mp hi
    have hbi := (bounds (ha i (by omega))).1
    have hmi : ((b i).radius : ℝ) ≤ (b i).center := by exact_mod_cast hmid i hi'.1 hi'.2
    have hai : 0 ≤ a i := by nlinarith
    positivity
  have hhead : 4/100000000 ≤ ∑ i ∈ Ico 0 3, a i*x^i := by
    have hq := quad_lower (a := L0) hL2 hder hx hx'
    have hh1 := mul_le_mul_of_nonneg_right h1 hx
    have hh2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg x)
    norm_num [Nat.Ico_zero_eq_range,Finset.sum_range_succ] at hq hh ⊢
    linarith
  have hs := Finset.sum_Ico_consecutive (fun i => a i*x^i) (by norm_num : 0 ≤ 3) (by norm_num : 3 ≤ 10)
  have hs' := Finset.sum_Ico_consecutive (fun i => a i*x^i) (by norm_num : 0 ≤ 10) hM
  calc
    0 < (∑ i ∈ Ico 0 3, a i*x^i)+(∑ i ∈ Ico 3 10, a i*x^i)+(∑ i ∈ Ico 10 M, a i*x^i) := by linarith
    _ = _ := by rw [hs,hs',Nat.Ico_zero_eq_range]

end SepticProfile.FixedInterval


namespace SepticProfile.EulerPolynomial
open Filter Set Polynomial
open scoped Topology ContDiff

lemma eval_add_monomial (p : ℝ[X]) (δ x : ℝ) :
    (p+C δ*X^140).eval x=p.eval x+δ*x^140 := by
  rw [eval_add]
  congr 1
  rw [eval_mul,eval_C,eval_pow,eval_X]

lemma eval_barrier (f : PowerSeries ℝ) (δ x : ℝ) :
    (barrier f δ).eval x=(PowerSeries.trunc 221 f).eval x+δ*x^140 := by
  unfold barrier
  exact eval_add_monomial (PowerSeries.trunc 221 f) δ x

lemma taylor_jet_littleO (f : ℝ → ℝ) (hf : ContDiffAt ℝ 220 f 0) :
    (fun x => f x-(PowerSeries.trunc 221 (SonicJet.jet f)).eval x)
      =o[𝓝 (0 : ℝ)] (fun x => x^220) := by
  obtain ⟨s,hs,hfs⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hs
  have hfb : ContDiffOn ℝ 220 f (Metric.ball 0 r) := hfs.mono hrs
  have h0 : (0 : ℝ) ∈ Metric.ball 0 r := Metric.mem_ball_self hr
  have ht := taylor_isLittleO (convex_ball (0 : ℝ) r) h0 hfb
  rw [nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds _ hr)] at ht
  have heval (x : ℝ) : taylorWithinEval f 220 (Metric.ball 0 r) 0 x=
      (PowerSeries.trunc 221 (SonicJet.jet f)).eval x := by
    rw [taylor_within_apply]
    change (∑ k ∈ Finset.range 221, ((k.factorial : ℝ)⁻¹*(x-0)^k) •
      iteratedDerivWithin k f (Metric.ball 0 r) 0)=
        (PowerSeries.trunc 221 (SonicJet.jet f)).eval₂ (RingHom.id ℝ) x
    rw [PowerSeries.eval₂_trunc_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    rw [iteratedDerivWithin_of_isOpen Metric.isOpen_ball h0,SonicJet.coeff_jet]
    simp only [RingHom.id_apply,sub_zero,smul_eq_mul,div_eq_mul_inv]
    ring
  simpa only [heval,sub_zero] using ht

/-- The barriers enter on the correct sides of the actual analytic sonic
solution. No numerical assumption about the omitted Taylor tail is needed. -/
lemma exists_barrier_entry (f : ℝ → ℝ) (hf : ContDiffAt ℝ 220 f 0)
    (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ x in 𝓝 (0 : ℝ), 0<x →
      (barrier (SonicJet.jet f) (-δ)).eval x<f x ∧
        f x<(barrier (SonicJet.jet f) δ).eval x := by
  have ht := (taylor_jet_littleO f hf).bound (show (0 : ℝ)<δ/2 by positivity)
  have hx1 : ∀ᶠ x : ℝ in 𝓝 0, x≤1 := eventually_le_nhds (by norm_num)
  filter_upwards [ht,hx1] with x ht hx1
  intro hx
  have hp : x^220≤x^140 := pow_le_pow_of_le_one hx.le hx1 (by norm_num)
  have hxpow : 0<x^140 := pow_pos hx _
  have hbound : |f x-(PowerSeries.trunc 221 (SonicJet.jet f)).eval x|≤δ/2*x^220 := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hx.le 220)] using ht
  have hbound' := abs_le.mp hbound
  have hmul := mul_le_mul_of_nonneg_left hp (show 0≤δ/2 by positivity)
  have hpos := mul_pos hδ hxpow
  rw [eval_barrier,eval_barrier]
  simp only [neg_mul]
  constructor <;> linarith only [hbound'.1,hbound'.2,hmul,hpos]

end SepticProfile.EulerPolynomial




namespace SepticProfile.FixedInterval
open Finset

lemma tail_unscaled_bound {Q : ℤ} (hQ : 0<Q) (D lo hi : ℕ) (hD : hi≤2^D)
    (b : ℕ → Box) (a : ℕ → ℝ) (ha : ∀ i ∈ Ico lo hi, Holds Q (b i) (a i))
    (p d : ℤ) (hd : 0<d)
    (hb : d*absTail D lo hi b≤p*Q*6^(hi-1))
    {x : ℝ} (hx : 0≤x) (hx' : x≤5/6) :
    |∑ i ∈ Ico lo hi, a i*x^i|≤(p : ℝ)/d := by
  have hh := scaled_tail_bound hQ D lo hi hD b a ha hx hx'
  have hq : 0<(Q : ℝ) := by exact_mod_cast hQ
  have hd' : 0<(d : ℝ) := by exact_mod_cast hd
  have hh' : (d : ℝ)*(absTail D lo hi b : ℝ)≤(p : ℝ)*Q*6^(hi-1) := by
    exact_mod_cast hb
  rw [abs_mul,abs_of_pos (mul_pos hq (by positivity))] at hh
  apply (le_div_iff₀ hd').mpr
  apply (mul_le_mul_iff_right₀ (show 0<(Q : ℝ)*6^(hi-1) by positivity)).mp
  calc
    _ = (d : ℝ)*((Q : ℝ)*6^(hi-1)*|∑ i ∈ Ico lo hi, a i*x^i|) := by ring
    _ ≤ (d : ℝ)*(absTail D lo hi b : ℝ) := mul_le_mul_of_nonneg_left hh hd'.le
    _ ≤ _ := by nlinarith only [hh']

lemma finite_velocity_range {Q : ℤ} (hQ : 0<Q) (b : ℕ → Box) (a : ℕ → ℝ)
    (ha : ∀ i<220, Holds Q (b i) (a i))
    (hfirst : a 0≤ -(201/100000:ℝ))
    (hmid : ∀ i : ℕ, 1 ≤ i → i < 63 → (b i).center+(b i).radius≤0)
    (hall : 50*absTail 8 0 220 b≤Q*6^219)
    (htail : 100000*absTail 8 63 220 b≤Q*6^219)
    {x : ℝ} (hx : 0≤x) (hx' : x≤5/6) :
    -(1/50:ℝ)≤∑ i ∈ range 220, a i*x^i ∧
      (∑ i ∈ range 220, a i*x^i)≤ -(1/500:ℝ) := by
  have hAll := tail_unscaled_bound hQ 8 0 220 (by norm_num) b a
    (fun i hi => ha i (mem_Ico.mp hi).2) 1 50 (by norm_num) (by simpa using hall) hx hx'
  rw [Nat.Ico_zero_eq_range] at hAll
  constructor
  · have hh := (abs_le.mp hAll).1
    norm_num at hh ⊢
    exact hh
  have hTail := tail_unscaled_bound hQ 8 63 220 (by norm_num) b a
    (fun i hi => ha i (mem_Ico.mp hi).2) 1 100000 (by norm_num) (by simpa using htail) hx hx'
  have hMid : (∑ i ∈ Ico 1 63, a i*x^i)≤0 := by
    apply sum_nonpos
    intro i hi
    have hm := hmid i (mem_Ico.mp hi).1 (mem_Ico.mp hi).2
    have hmi : ((b i).center : ℝ)+(b i).radius≤0 := by exact_mod_cast hm
    have hb := (bounds (ha i (by have := (mem_Ico.mp hi).2; omega))).2
    have hq : 0<(Q : ℝ) := by exact_mod_cast hQ
    have hai : a i≤0 := by nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg hai (pow_nonneg hx _)
  have hsum := Finset.sum_Ico_consecutive (fun i => a i*x^i) (by norm_num : 0≤1) (by norm_num : 1≤63)
  have hsum' := Finset.sum_Ico_consecutive (fun i => a i*x^i) (by norm_num : 0≤63) (by norm_num : 63≤220)
  simp only [Nat.Ico_zero_eq_range] at hsum hsum'
  norm_num at hsum
  have ht := (abs_le.mp hTail).2
  norm_num at ht
  linarith

end SepticProfile.FixedInterval

namespace SepticProfile.EulerPolynomial
open Polynomial
lemma eval_shift_one (p : ℝ[X]) (hp : p.natDegree≤220) (h0 : p.coeff 0=1) (x : ℝ) :
    p.eval x=1+x*∑ i ∈ Finset.range 220, p.coeff (i+1)*x^i := by
  rw [eval_eq_sum_range' (show p.natDegree<221 by omega),
    show 221=1+220 by norm_num,Finset.sum_range_add]
  simp only [Finset.sum_range_one,h0,pow_zero,mul_one,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.add_comm 1 i,pow_succ]
  ring

lemma polynomial_velocity_range {Q : ℤ} (hQ : 0<Q) (b : ℕ → FixedInterval.Box)
    (p : ℝ[X]) (hp : p.natDegree≤220) (h0 : p.coeff 0=1)
    (ha : ∀ i<220, FixedInterval.Holds Q (b i) (p.coeff (i+1)))
    (hfirst : p.coeff 1≤ -(201/100000:ℝ))
    (hmid : ∀ i : ℕ, 1 ≤ i → i < 63 → (b i).center+(b i).radius≤0)
    (hall : 50*FixedInterval.absTail 8 0 220 b≤Q*6^219)
    (htail : 100000*FixedInterval.absTail 8 63 220 b≤Q*6^219)
    {x : ℝ} (hx : 0≤x) (hx' : x≤5/6) :
    1-x/50≤p.eval x ∧ p.eval x≤1-x/500 := by
  have hh := FixedInterval.finite_velocity_range hQ b (fun i => p.coeff (i+1)) ha
    (by simpa only [zero_add] using hfirst) hmid hall htail hx hx'
  rw [eval_shift_one p hp h0 x]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hh.1 hx]
  · nlinarith [mul_le_mul_of_nonneg_left hh.2 hx]
end SepticProfile.EulerPolynomial



namespace SepticProfile.RegularContinuation
open Set
open scoped NNReal

/-- Projection to a closed scalar interval. It is used only away from the
source singularities, and is proved inactive by exact comparison barriers. -/
def clamp (c d x : ℝ) : ℝ := max (min x d) c

lemma clamp_mem {c d : ℝ} (hcd : c≤d) (x : ℝ) : clamp c d x ∈ Icc c d := by
  exact ⟨le_max_right _ _,max_le (min_le_right _ _) hcd⟩

lemma clamp_eq {c d x : ℝ} (hx : x ∈ Icc c d) : clamp c d x=x := by
  simp [clamp,min_eq_left hx.2,max_eq_left hx.1]

lemma clamp_lipschitz (c d : ℝ) : LipschitzWith 1 (clamp c d) :=
  (LipschitzWith.id.min_const d).max_const c

/-- An ordinary (nonsingular) ODE on a compact rectangle has a clamped solution
on the entire time interval. No singular-point continuation is imported here. -/
theorem exists_clamped_solution {a b c d : ℝ} (hab : a≤b) (hcd : c≤d)
    {f : ℝ×ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Icc a b ×ˢ Icc c d)) (u0 : ℝ) :
    ∃ u : ℝ → ℝ, u a=u0 ∧ ContinuousOn u (Icc a b) ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt u (f (t,clamp c d (u t))) (Icc a b) t := by
  let S := Icc a b ×ˢ Icc c d
  have hcomp : IsCompact S := isCompact_Icc.prod isCompact_Icc
  obtain ⟨K,hK⟩ := hf.exists_lipschitzOnWith (by norm_num) ((convex_Icc a b).prod (convex_Icc c d)) hcomp
  obtain ⟨B,hB⟩ := hcomp.exists_bound_of_continuousOn hf.continuousOn
  let L : ℝ≥0 := ⟨max B 0,le_max_right _ _⟩
  let A : ℝ≥0 := ⟨(L:ℝ)*(b-a)+1,by have := L.coe_nonneg; nlinarith⟩
  let F : ℝ → ℝ → ℝ := fun t u => f (t,clamp c d u)
  let t0 : Icc a b := ⟨a,le_rfl,hab⟩
  have hLip (t : ℝ) (ht : t ∈ Icc a b) : LipschitzWith K (F t) := by
    rw [lipschitzWith_iff_norm_sub_le]
    intro x y
    have hb1 := hK.norm_sub_le (show (t,clamp c d x) ∈ S from ⟨ht,clamp_mem hcd x⟩)
      (show (t,clamp c d y) ∈ S from ⟨ht,clamp_mem hcd y⟩)
    have hb2 := (clamp_lipschitz c d).norm_sub_le x y
    simp only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero,
      max_eq_right (norm_nonneg _),NNReal.coe_one,one_mul] at hb1 hb2
    exact hb1.trans (mul_le_mul_of_nonneg_left hb2 K.coe_nonneg)
  have hPic : IsPicardLindelof F t0 u0 A 0 L K := by
    refine ⟨fun t ht => (hLip t ht).lipschitzOnWith,?_,?_,?_⟩
    · intro u _
      exact hf.continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
        (fun t ht => ⟨ht,clamp_mem hcd u⟩)
    · intro t ht u _
      exact (hB (t,clamp c d u) ⟨ht,clamp_mem hcd u⟩).trans (le_max_left _ _)
    · have hA : (A : ℝ)=(L : ℝ)*(b-a)+1 := rfl
      change (L : ℝ)*max (b-a) (a-a) ≤ (A : ℝ)-(0 : ℝ)
      rw [hA,sub_self,max_eq_left (sub_nonneg.mpr hab),sub_zero]
      linarith
  obtain ⟨u,hu0,hud⟩ := hPic.exists_eq_forall_mem_Icc_hasDerivWithinAt (x := u0) (by simp)
  exact ⟨u,hu0,fun t ht => (hud t ht).continuousWithinAt,hud⟩

end SepticProfile.RegularContinuation


namespace SepticProfile.RegularContinuation
open Set

/-- A compact nonsingular scalar ODE is continued between verified strict
barriers. The integrator is constructed, rather than assumed. -/
theorem exists_between_strict_barriers {a b c d u0 : ℝ} (hab : a≤b) (hcd : c≤d)
    {f : ℝ×ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Icc a b ×ˢ Icc c d))
    (lo hi dlo dhi : ℝ → ℝ)
    (hloder : ∀ t ∈ Icc a b, HasDerivAt lo (dlo t) t)
    (hhider : ∀ t ∈ Icc a b, HasDerivAt hi (dhi t) t)
    (hlorange : ∀ t ∈ Icc a b, lo t ∈ Icc c d)
    (hhirange : ∀ t ∈ Icc a b, hi t ∈ Icc c d)
    (hlostrict : ∀ t ∈ Icc a b, dlo t<f (t,lo t))
    (hhistrict : ∀ t ∈ Icc a b, f (t,hi t)<dhi t)
    (hu0 : u0 ∈ Icc (lo a) (hi a)) :
    ∃ u : ℝ → ℝ, u a=u0 ∧ ContinuousOn u (Icc a b) ∧
      (∀ t ∈ Icc a b, u t ∈ Icc (lo t) (hi t)) ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt u (f (t,u t)) (Icc a b) t := by
  obtain ⟨u,hu,huc,hud⟩ := exists_clamped_solution hab hcd hf u0
  have hright (t : ℝ) (ht : t ∈ Ico a b) : HasDerivWithinAt u
      (f (t,clamp c d (u t))) (Ici t) t := by
    apply (hud t ⟨ht.1,le_of_lt ht.2⟩).mono_of_mem_nhdsWithin
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)
  have hupper : ∀ t ∈ Icc a b, u t≤hi t := by
    apply image_le_of_deriv_right_lt_deriv_boundary' huc hright
      (B' := dhi) (by simpa [hu] using hu0.2)
      (fun t ht => (hhider t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hhider t ⟨ht.1,ht.2.le⟩).hasDerivWithinAt)
    intro t ht he
    rw [he,clamp_eq (hhirange t ⟨ht.1,ht.2.le⟩)]
    exact hhistrict t ⟨ht.1,ht.2.le⟩
  have hlower : ∀ t ∈ Icc a b, lo t≤u t := by
    have hh := image_le_of_deriv_right_lt_deriv_boundary' huc.neg
      (fun t ht => (hright t ht).neg) (B := fun t => -lo t) (B' := fun t => -dlo t)
      (by change -u a ≤ -lo a; rw [hu]; linarith [hu0.1])
      (fun t ht => (hloder t ht).neg.continuousAt.continuousWithinAt)
      (fun t ht => (hloder t ⟨ht.1,ht.2.le⟩).neg.hasDerivWithinAt)
    have hh' : ∀ t ∈ Icc a b, -u t≤ -lo t := by
      apply hh
      intro t ht he
      have he' : u t=lo t := neg_inj.mp he
      rw [he',clamp_eq (hlorange t ⟨ht.1,ht.2.le⟩)]
      exact neg_lt_neg (hlostrict t ⟨ht.1,ht.2.le⟩)
    intro t ht
    linarith [hh' t ht]
  refine ⟨u,hu,huc,fun t ht => ⟨hlower t ht,hupper t ht⟩,?_⟩
  intro t ht
  have htu : u t ∈ Icc c d :=
    ⟨le_trans (hlorange t ht).1 (hlower t ht),le_trans (hupper t ht) (hhirange t ht).2⟩
  simpa only [clamp_eq htu] using hud t ht

end SepticProfile.RegularContinuation


namespace SepticProfile.EulerContinuation
open Set Polynomial RegularContinuation

def D (sigma t u : ℝ) : ℝ :=
  (1-(1+1/500)*t)*((1-t)^2-sigma*(1-(1+1/500)*t)^2)*(1-u^2)
def N (kappa t u : ℝ) : ℝ :=
  -(1/500)*(1-(3/5)*u^2)*(kappa*(1-(1+1/500)*t)*(1-u^2)+
    3*((1-(1+1/500)*t)-(1-t)*u))

lemma D_pos {sigma t u : ℝ} (hs : sigma<1)
    (ht : t ∈ Icc 0 (5/6)) (hu : u ∈ Ico 0 1) : 0<D sigma t u := by
  have hb : 0<1-(1+1/500:ℝ)*t := by linarith [ht.2]
  have hba : 1-(1+1/500:ℝ)*t≤1-t := by linarith [ht.1]
  have hsq : (1-(1+1/500:ℝ)*t)^2≤(1-t)^2 := by nlinarith
  have hs' := mul_lt_mul_of_pos_right hs (sq_pos_of_pos hb)
  have hu' : 0<1-u^2 := by nlinarith [sq_nonneg u,mul_pos (sub_pos.mpr hu.2) (by linarith [hu.1] : 0<1+u)]
  exact mul_pos (mul_pos hb (by nlinarith)) hu'

lemma field_contDiffOn {sigma kappa a b d : ℝ} (hs : sigma<1)
    (ha : 0≤a) (hb : b≤5/6) (hd : d<1) :
    ContDiffOn ℝ 1 (fun p : ℝ×ℝ => N kappa p.1 p.2 / D sigma p.1 p.2)
      (Icc a b ×ˢ Icc 0 d) := by
  have hN : ContDiff ℝ 1 (fun p : ℝ×ℝ => N kappa p.1 p.2) := by unfold N; fun_prop
  have hD : ContDiff ℝ 1 (fun p : ℝ×ℝ => D sigma p.1 p.2) := by unfold D; fun_prop
  exact hN.contDiffOn.div hD.contDiffOn (fun p hp => ne_of_gt (D_pos hs
    ⟨ha.trans hp.1.1,hp.1.2.trans hb⟩ ⟨hp.2.1,hp.2.2.trans_lt hd⟩))

lemma residual_eq (sigma kappa : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    EulerFormal.profileResidual sigma kappa (3/5) (1/500) f x=
      D sigma x (f x)*deriv f x-N kappa x (f x) := by
  unfold EulerFormal.profileResidual D N
  ring

/-- Genuine regular continuation of the sonic Euler equation from a>0 to
5/6, provided the two polynomial residual certificates are supplied. -/
theorem exists_between_polynomials {sigma kappa a u0 : ℝ} (hs : sigma<1)
    (ha : 0<a) (ha' : a≤5/6) (p q : ℝ[X])
    (hrangep : ∀ t ∈ Icc 0 (5/6), 1-t/50≤p.eval t ∧ p.eval t≤1-t/500)
    (hrangeq : ∀ t ∈ Icc 0 (5/6), 1-t/50≤q.eval t ∧ q.eval t≤1-t/500)
    (hresp : ∀ t ∈ Ioc 0 (5/6),
      EulerFormal.profileResidual sigma kappa (3/5) (1/500) (fun x => p.eval x) t<0)
    (hresq : ∀ t ∈ Ioc 0 (5/6),
      0<EulerFormal.profileResidual sigma kappa (3/5) (1/500) (fun x => q.eval x) t)
    (hu0 : u0 ∈ Icc (p.eval a) (q.eval a)) :
    ∃ u : ℝ → ℝ, u a=u0 ∧ ContinuousOn u (Icc a (5/6)) ∧
      (∀ t ∈ Icc a (5/6), p.eval t≤u t ∧ u t≤q.eval t) ∧
      ∀ t ∈ Icc a (5/6), HasDerivWithinAt u
        (N kappa t (u t)/D sigma t (u t)) (Icc a (5/6)) t := by
  have hd : (0:ℝ)≤1-a/1000 := by linarith
  have hd' : 1-a/1000<1 := by linarith
  have ht0 {t : ℝ} (ht : t ∈ Icc a (5/6)) : t ∈ Icc 0 (5/6) :=
    ⟨ha.le.trans ht.1,ht.2⟩
  have htp {t : ℝ} (ht : t ∈ Icc a (5/6)) : t ∈ Ioc 0 (5/6) :=
    ⟨ha.trans_le ht.1,ht.2⟩
  have hpr (t : ℝ) (ht : t ∈ Icc a (5/6)) : p.eval t ∈ Icc 0 (1-a/1000) := by
    have hh := hrangep t (ht0 ht)
    constructor <;> linarith [ht.1,ht.2]
  have hqr (t : ℝ) (ht : t ∈ Icc a (5/6)) : q.eval t ∈ Icc 0 (1-a/1000) := by
    have hh := hrangeq t (ht0 ht)
    constructor <;> linarith [ht.1,ht.2]
  apply exists_between_strict_barriers ha' hd
    (field_contDiffOn hs ha.le (le_refl (5/6)) hd')
    (fun t => p.eval t) (fun t => q.eval t)
    (fun t => deriv (fun x => p.eval x) t) (fun t => deriv (fun x => q.eval x) t)
    (fun t _ => p.differentiableAt.hasDerivAt) (fun t _ => q.differentiableAt.hasDerivAt)
    hpr hqr ?_ ?_ hu0
  · intro t ht
    apply (lt_div_iff₀ (D_pos hs (ht0 ht) ⟨(hpr t ht).1,(hpr t ht).2.trans_lt hd'⟩)).mpr
    have hh := hresp t (htp ht)
    rw [residual_eq] at hh
    nlinarith only [hh]
  · intro t ht
    apply (div_lt_iff₀ (D_pos hs (ht0 ht) ⟨(hqr t ht).1,(hqr t ht).2.trans_lt hd'⟩)).mpr
    have hh := hresq t (htp ht)
    rw [residual_eq] at hh
    nlinarith only [hh]

end SepticProfile.EulerContinuation

end
end

end OAI
