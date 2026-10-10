import Mathlib
import OAI.Probability.ParisiFinite.ContinuousTiltedMeanJoint
import OAI.Probability.ParisiFinite.Nnwidth
import OAI.Probability.ParisiFinite.TimeCubicTest

namespace OAI

/-! Splice. -/

noncomputable section

open MeasureTheory Filter Function Set
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
open ContinuousLinearMap
open scoped Convolution
open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiPath
namespace TimeQuadraticTest

def splice (c : ℝ) (f g : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ := if t<c then f t x else g t x

lemma integrable_dt (f : TimeQuadraticTest) (u v x : ℝ) :
    IntervalIntegrable (fun t => f.dt t x) volume u v := by
  apply (intervalIntegrable_const (c := (f.ct:ℝ))).mono_fun'
    ((f.measT.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  exact ae_of_all _ fun t => f.boundT t x

lemma measurable_splice {f g : ℝ → ℝ → ℝ} (c : ℝ)
    (hf : Measurable (uncurry f)) (hg : Measurable (uncurry g)) :
    Measurable (uncurry (splice c f g)) :=
  Measurable.ite (measurableSet_lt measurable_fst measurable_const) hf hg

lemma bound_splice {f g : ℝ → ℝ → ℝ} {C D : ℝ≥0} (c : ℝ)
    (hf : ∀ t x,‖f t x‖≤C) (hg : ∀ t x,‖g t x‖≤D) (t x : ℝ) :
    ‖splice c f g t x‖≤ max C D := by
  unfold splice
  split_ifs
  · exact (hf t x).trans (by exact_mod_cast le_max_left C D)
  · exact (hg t x).trans (by exact_mod_cast le_max_right C D)

lemma integrable_splice_dt (f g : TimeQuadraticTest) (c u v x : ℝ) :
    IntervalIntegrable (fun t => splice c f.dt g.dt t x) volume u v := by
  apply (intervalIntegrable_const (c := (max f.ct g.ct:ℝ))).mono_fun'
    (((measurable_splice c f.measT g.measT).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  exact ae_of_all _ fun t => bound_splice c f.boundT g.boundT t x

lemma continuousAt_splice {f g : ℝ → ℝ → ℝ} {c t x : ℝ} (ht : t≠c)
    (hf : ContinuousAt (uncurry f) (t,x)) (hg : ContinuousAt (uncurry g) (t,x)) :
    ContinuousAt (uncurry (splice c f g)) (t,x) := by
  rcases lt_or_gt_of_ne ht with ht|ht
  · apply hf.congr_of_eventuallyEq
    filter_upwards [continuousAt_fst.preimage_mem_nhds (Iio_mem_nhds ht)] with p hp
    exact ite_eq_left hp
  · apply hg.congr_of_eventuallyEq
    filter_upwards [continuousAt_fst.preimage_mem_nhds (Ioi_mem_nhds ht)] with p hp
    exact ite_eq_right (not_lt.mpr hp.le)

lemma splice_integralT (f g : TimeQuadraticTest) {c : ℝ} (hc : c∈Icc (0:ℝ) 1)
    (hfg : ∀ x,f.val c x=g.val c x) {u v : ℝ}
    (hu : u∈Icc (0:ℝ) 1) (hv : v∈Icc (0:ℝ) 1) (x : ℝ) :
    splice c f.val g.val v x-splice c f.val g.val u x=
      ∫ t in u..v,splice c f.dt g.dt t x := by
  have hleft (t : ℝ) (ht : t≤c) : splice c f.val g.val t x=f.val t x := by
    rcases lt_or_eq_of_le ht with ht|rfl
    · exact ite_eq_left ht
    · simpa [splice] using (hfg x).symm
  have hright (t : ℝ) (ht : c≤t) : splice c f.val g.val t x=g.val t x :=
    ite_eq_right (not_lt.mpr ht)
  have hbefore {a b : ℝ} (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1)
      (hab : a≤b) (hbc : b≤c) :
      splice c f.val g.val b x-splice c f.val g.val a x=
        ∫ t in a..b,splice c f.dt g.dt t x := by
    rw [hleft b hbc,hleft a (hab.trans hbc),f.integralT a ha b hb]
    apply intervalIntegral.integral_congr_Ioo_of_le hab
    intro t ht
    exact (ite_eq_left (ht.2.trans_le hbc)).symm
  have hafter {a b : ℝ} (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1)
      (hab : a≤b) (hca : c≤a) :
      splice c f.val g.val b x-splice c f.val g.val a x=
        ∫ t in a..b,splice c f.dt g.dt t x := by
    rw [hright b (hca.trans hab),hright a hca,g.integralT a ha b hb]
    apply intervalIntegral.integral_congr_Ioo_of_le hab
    intro t ht
    exact (ite_eq_right (not_lt.mpr (hca.trans ht.1.le))).symm
  have hle {a b : ℝ} (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) (hab : a≤b) :
      splice c f.val g.val b x-splice c f.val g.val a x=
        ∫ t in a..b,splice c f.dt g.dt t x := by
    by_cases hbc : b≤c
    · exact hbefore ha hb hab hbc
    by_cases hca : c≤a
    · exact hafter ha hb hab hca
    rw [←intervalIntegral.integral_add_adjacent_intervals
      (integrable_splice_dt f g c a c x) (integrable_splice_dt f g c c b x),
      ←hbefore ha hc (le_of_not_ge hca) le_rfl,
      ←hafter hc hb (le_of_not_ge hbc) le_rfl]
    ring
  rcases le_total u v with huv|hvu
  · exact hle hu hv huv
  · rw [intervalIntegral.integral_symm,←hle hv hu hvu]
    ring

 

def glue (f g : TimeQuadraticTest) (c : ℝ) (hc : c∈Icc (0:ℝ) 1)
    (hfg : ∀ x,f.val c x=g.val c x) : TimeQuadraticTest where
  val := splice c f.val g.val
  d1 := splice c f.d1 g.d1
  d2 := splice c f.d2 g.d2
  dt := splice c f.dt g.dt
  hasD1 := by intro t x; unfold splice; split_ifs; exact f.hasD1 t x; exact g.hasD1 t x
  hasD2 := by intro t x; unfold splice; split_ifs; exact f.hasD2 t x; exact g.hasD2 t x
  continuousD2 := by intro t; unfold splice; split_ifs; exact f.continuousD2 t; exact g.continuousD2 t
  c1 := max f.c1 g.c1
  c2 := max f.c2 g.c2
  ct := max f.ct g.ct
  bound1 := bound_splice c f.bound1 g.bound1
  bound2 := bound_splice c f.bound2 g.bound2
  boundT := bound_splice c f.boundT g.boundT
  measT := measurable_splice c f.measT g.measT
  continuousT := by intro t; unfold splice; split_ifs; exact f.continuousT t; exact g.continuousT t
  jointD1 := by
    filter_upwards [f.jointD1,g.jointD1,volume.ae_ne c] with t hf hg ht hmem x
    exact continuousAt_splice ht (hf hmem x) (hg hmem x)
  jointD2 := by
    filter_upwards [f.jointD2,g.jointD2,volume.ae_ne c] with t hf hg ht hmem x
    exact continuousAt_splice ht (hf hmem x) (hg hmem x)
  integralT := fun _ hu _ hv x => splice_integralT f g hc hfg hu hv x

end TimeQuadraticTest
end ParisiPath

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite
open ParisiPath

 
def SmoothField.staticTimeTest (f : SmoothField) : TimeQuadraticTest where
  val := fun _ => f.val
  d1 := fun _ => f.d1
  d2 := fun _ => f.d2
  dt := fun _ _ => 0
  hasD1 := fun _ => f.hasD1
  hasD2 := fun _ => f.hasD2
  continuousD2 := fun _ => f.continuousD2
  c1 := f.bound1
  c2 := f.bound2
  ct := 0
  bound1 := fun _ x => by simpa only [Real.norm_eq_abs] using f.normD1 x
  bound2 := fun _ x => by simpa only [Real.norm_eq_abs] using f.normD2 x
  boundT := by intros; simp
  measT := measurable_const
  continuousT := fun _ => continuous_const
  jointD1 := ae_of_all _ fun _ _ _ => (f.continuousD1.comp continuous_snd).continuousAt
  jointD2 := ae_of_all _ fun _ _ _ => (f.continuousD2.comp continuous_snd).continuousAt
  integralT := by intros; simp

 
def SmoothField.slabTimeTest (f : SmoothField) (a b : ℝ) : TimeQuadraticTest where
  val := fun t => (fieldOnInterval f a b t).val
  d1 := fun t => (fieldOnInterval f a b t).d1
  d2 := fun t => (fieldOnInterval f a b t).d2
  dt := fieldOnInterval_dt f a b
  hasD1 := fun t => (fieldOnInterval f a b t).hasD1
  hasD2 := fun t => (fieldOnInterval f a b t).hasD2
  continuousD2 := fun t => (fieldOnInterval f a b t).continuousD2
  c1 := f.bound1
  c2 := f.bound2+2*Real.nnabs a*f.bound1^2
  ct := fieldOnInterval_timeBound f a
  bound1 := fun t x => by simpa only [Real.norm_eq_abs,fieldOnInterval,SmoothField.transform] using (fieldOnInterval f a b t).normD1 x
  bound2 := fun t x => by simpa only [Real.norm_eq_abs,fieldOnInterval,SmoothField.transform] using (fieldOnInterval f a b t).normD2 x
  boundT := fieldOnInterval_dt_bound f a b
  measT := measurable_fieldOnInterval_dt f a b
  continuousT := continuous_fieldOnInterval_dt f a b
  jointD1 := ae_of_all _ fun _ _ _ => (continuous_fieldOnInterval_d1 f a b).continuousAt
  jointD2 := ae_of_all _ fun _ _ _ => (continuous_fieldOnInterval_d2 f a b).continuousAt
  integralT := fun u _ v _ x => (fieldOnInterval_integral_time f a b u v x).symm

 

def finiteTimeField (β : ℝ≥0) (hβ : 0<β) : Schedule → ℝ → ℝ → SmoothField
  | [],_,_ => terminalField β hβ
  | (a,d)::ls,s,t => if t<s+d then
      fieldOnInterval (smoothRecursion β hβ ls) a (s+d) t
    else finiteTimeField β hβ ls (s+d) t

def finiteTimeDerivative (β : ℝ≥0) (hβ : 0<β) : Schedule → ℝ → ℝ → ℝ → ℝ
  | [],_,_,_ => 0
  | (a,d)::ls,s,t,x => if t<s+d then
      fieldOnInterval_dt (smoothRecursion β hβ ls) a (s+d) t x
    else finiteTimeDerivative β hβ ls (s+d) t x

def finiteTimeCoefficient : Schedule → ℝ → ℝ → ℝ
  | [],_,_ => 0
  | (a,d)::ls,s,t => if t<s+d then a else finiteTimeCoefficient ls (s+d) t

lemma finiteTimeField_start (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (s x : ℝ) :
    (finiteTimeField β hβ ls s s).val x=recursion β ls x := by
  induction ls generalizing s with
  | nil => rfl
  | cons l ls ih =>
    rcases l with ⟨a,d⟩
    by_cases hd : d=0
    · simp only [hd,NNReal.coe_zero,add_zero,finiteTimeField,lt_self_iff_false,ite_false,
        ih,recursion,Real.sqrt_zero,step_zero_width]
    · have hp : (0:ℝ)<d := by exact_mod_cast pos_of_ne_zero hd
      rw [finiteTimeField,ite_eq_left (by linarith : s<s+(d:ℝ))]
      change step a (Real.sqrt (s+d-s)) (smoothRecursion β hβ ls).val x=recursion β ((a,d)::ls) x
      rw [add_sub_cancel_left,smoothRecursion_val]
      rfl

lemma finiteTimeField_after (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (s t x : ℝ)
    (ht : s+width ls≤t) : (finiteTimeField β hβ ls s t).val x=terminal β x := by
  induction ls generalizing s with
  | nil => rfl
  | cons l ls ih =>
    rcases l with ⟨a,d⟩
    rw [width_cons] at ht
    rw [finiteTimeField,ite_eq_right (by linarith [schedule_width_nonneg ls] : ¬ t<s+(d:ℝ))]
    apply ih
    linarith

lemma finiteTimeField_curvature (β : ℝ≥0) (hβ : 0<β) (ls : Schedule)
    (ha : ∀ l∈ls,l.1≤β) (s t : ℝ) : HasParisiCurvature β (finiteTimeField β hβ ls s t) := by
  induction ls generalizing s with
  | nil => exact terminal_hasParisiCurvature β hβ
  | cons l ls ih =>
    have htail : ∀ k∈ls,k.1≤β := fun k hk => ha k (List.mem_cons_of_mem _ hk)
    simp only [finiteTimeField]
    split_ifs
    · exact transform_hasParisiCurvature (smoothRecursion_hasParisiCurvature β hβ ls htail)
        l.1.coe_nonneg (by exact_mod_cast ha l List.mem_cons_self) _
    · exact ih htail _

lemma finiteTimeField_PDE (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (s t x : ℝ)
    (hs : s≤t) (ht : t<s+width ls) :
    finiteTimeDerivative β hβ ls s t x=-(1/2:ℝ)*((finiteTimeField β hβ ls s t).d2 x+
      finiteTimeCoefficient ls s t*((finiteTimeField β hβ ls s t).d1 x)^2) := by
  induction ls generalizing s with
  | nil =>
    simp only [width,List.map_nil,List.sum_nil,add_zero] at ht
    exact False.elim (not_lt_of_ge hs ht)
  | cons l ls ih =>
    rcases l with ⟨a,d⟩
    simp only [finiteTimeDerivative,finiteTimeField,finiteTimeCoefficient]
    split_ifs with hcut
    · exact ite_eq_left hcut
    · apply ih (s+d) (le_of_not_gt hcut)
      rw [width_cons] at ht
      linarith

 

structure ScheduleTimeRealization (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (s : ℝ) where
  test : TimeQuadraticTest
  val_eq : ∀ t x,test.val t x=(finiteTimeField β hβ ls s t).val x
  d1_eq : ∀ t x,test.d1 t x=(finiteTimeField β hβ ls s t).d1 x
  d2_eq : ∀ t x,test.d2 t x=(finiteTimeField β hβ ls s t).d2 x
  dt_eq : ∀ t x,test.dt t x=finiteTimeDerivative β hβ ls s t x

 

def scheduleTimeRealization (β : ℝ≥0) (hβ : 0<β) (ls : Schedule)
    (s : ℝ) (hs : 0 ≤ s) (he : s + width ls ≤ 1) : ScheduleTimeRealization β hβ ls s := by
  induction ls generalizing s with
  | nil =>
    exact ⟨(terminalField β hβ).staticTimeTest,fun _ _ => rfl,
      fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl⟩
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
    let slab := (smoothRecursion β hβ ls).slabTimeTest a c
    have hmatch (x : ℝ) : slab.val c x=tail.test.val c x := by
      change (fieldOnInterval (smoothRecursion β hβ ls) a c c).val x=tail.test.val c x
      rw [fieldOnInterval_right,tail.val_eq,finiteTimeField_start,smoothRecursion_val]
    refine ⟨slab.glue tail.test c ⟨hc0,hc1⟩ hmatch,?_,?_,?_,?_⟩
    · intro t x
      simp only [TimeQuadraticTest.glue,TimeQuadraticTest.splice,finiteTimeField,
        SmoothField.slabTimeTest,slab,c]
      split_ifs
      · rfl
      · exact tail.val_eq t x
    · intro t x
      simp only [TimeQuadraticTest.glue,TimeQuadraticTest.splice,finiteTimeField,
        SmoothField.slabTimeTest,slab,c]
      split_ifs
      · rfl
      · exact tail.d1_eq t x
    · intro t x
      simp only [TimeQuadraticTest.glue,TimeQuadraticTest.splice,finiteTimeField,
        SmoothField.slabTimeTest,slab,c]
      split_ifs
      · rfl
      · exact tail.d2_eq t x
    · intro t x
      simp only [TimeQuadraticTest.glue,TimeQuadraticTest.splice,finiteTimeDerivative,
        SmoothField.slabTimeTest,slab,c]
      split_ifs
      · rfl
      · exact tail.dt_eq t x

lemma finiteTimeCoefficient_measurable (ls : Schedule) (s : ℝ) :
    Measurable (finiteTimeCoefficient ls s) := by
  induction ls generalizing s with
  | nil => exact measurable_const
  | cons l ls ih =>
    exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
      measurable_const (ih _)

lemma finiteTimeCoefficient_bound (β : ℝ≥0) (ls : Schedule)
    (ha : ∀ l∈ls,l.1≤β) (s t : ℝ) : |finiteTimeCoefficient ls s t|≤β := by
  induction ls generalizing s with
  | nil => simpa only [finiteTimeCoefficient,abs_zero] using β.coe_nonneg
  | cons l ls ih =>
    simp only [finiteTimeCoefficient]
    split_ifs
    · rw [abs_of_nonneg l.1.coe_nonneg]
      exact_mod_cast ha l List.mem_cons_self
    · exact ih (fun k hk => ha k (List.mem_cons_of_mem _ hk)) _

lemma finiteTimeField_measurable_d1 (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (s : ℝ) :
    Measurable (fun p : ℝ×ℝ => (finiteTimeField β hβ ls s p.1).d1 p.2) := by
  classical
  induction ls generalizing s with
  | nil => exact (terminalField β hβ).continuousD1.measurable.comp measurable_snd
  | cons l ls ih =>
    have hh : Measurable (fun p : ℝ × ℝ => if p.1 < s + l.2 then
        (fieldOnInterval (smoothRecursion β hβ ls) l.1 (s+l.2) p.1).d1 p.2
        else (finiteTimeField β hβ ls (s+l.2) p.1).d1 p.2) :=
      Measurable.ite (measurableSet_lt measurable_fst measurable_const)
        (continuous_fieldOnInterval_d1 (smoothRecursion β hβ ls) l.1 (s+l.2)).measurable (ih _)
    convert! hh using 1
    funext p
    simp only [finiteTimeField]
    split_ifs <;> rfl

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite

def scheduleSuffix : Schedule → ℝ≥0 → Schedule
  | [],_ => []
  | (a,d)::ls,r => if r<d then (a,d-r)::ls else scheduleSuffix ls (r-d)

lemma scheduleSuffix_coeff_bound {β : ℝ≥0} (ls : Schedule)
    (ha : ∀ l∈ls,l.1 ≤ β) (r : ℝ≥0) : ∀ l∈scheduleSuffix ls r,l.1 ≤ β := by
  induction ls generalizing r with
  | nil => simp [scheduleSuffix]
  | cons l ls ih =>
    simp only [scheduleSuffix]
    split_ifs
    · intro k hk
      rcases List.mem_cons.mp hk with rfl|hk
      · exact ha l List.mem_cons_self
      · exact ha k (List.mem_cons_of_mem _ hk)
    · exact ih (fun k hk => ha k (List.mem_cons_of_mem _ hk)) _

lemma nnwidth_scheduleSuffix (ls : Schedule) (r : ℝ≥0) :
    nnwidth (scheduleSuffix ls r) = nnwidth ls-r := by
  induction ls generalizing r with
  | nil => simp [scheduleSuffix,nnwidth]
  | cons l ls ih =>
    rcases l with ⟨a,d⟩
    simp only [scheduleSuffix,nnwidth]
    split_ifs with hrd
    · simp only [nnwidth]
      exact tsub_add_eq_add_tsub hrd.le
    · rw [ih]
      have hdr : d ≤ r := le_of_not_gt hrd
      symm
      calc d+nnwidth ls-r = d+nnwidth ls-(d+(r-d)) := by rw [add_tsub_cancel_of_le hdr]
           _ = nnwidth ls-(r-d) := add_tsub_add_eq_tsub_left _ _ _

lemma scheduleValue_suffix (ls : Schedule) (r u : ℝ≥0) :
    scheduleValue (scheduleSuffix ls r) u = scheduleValue ls (r+u) := by
  induction ls generalizing r with
  | nil => rfl
  | cons l ls ih =>
    rcases l with ⟨a,d⟩
    rw [scheduleSuffix]
    split_ifs with hrd
    · exact (scheduleValue_split_shift a r d hrd.le ls u).symm
    · have hru : ¬ r+u<d := not_lt.mpr ((le_of_not_gt hrd).trans le_self_add)
      rw [scheduleValue,ite_eq_right hru,ih,tsub_add_eq_add_tsub (le_of_not_gt hrd)]

lemma scheduleSuffix_add (ls : Schedule) (r u : ℝ≥0) :
    scheduleSuffix (scheduleSuffix ls r) u = scheduleSuffix ls (r+u) := by
  induction ls generalizing r with
  | nil => rfl
  | cons l ls ih =>
    rcases l with ⟨a,d⟩
    rw [scheduleSuffix]
    split_ifs with hrd
    · have he : r+(d-r)=d := add_tsub_cancel_of_le hrd.le
      have hc : r+u<d ↔ u<d-r := lt_tsub_iff_left.symm
      simp only [scheduleSuffix,hc]
      split_ifs with hu
      · rw [tsub_tsub]
      · congr 1
        symm
        calc r+u-d = r+u-(r+(d-r)) := by rw [he]
             _ = u-(d-r) := add_tsub_add_eq_tsub_left _ _ _
    · have hru : ¬ r+u<d := not_lt.mpr ((le_of_not_gt hrd).trans le_self_add)
      rw [scheduleSuffix,ite_eq_right hru,ih,tsub_add_eq_add_tsub (le_of_not_gt hrd)]

lemma evolve_scheduleSuffix_zero (ls : Schedule) (f : ℝ → ℝ) :
    evolve (scheduleSuffix ls 0) f = evolve ls f := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    rcases l with ⟨a,d⟩
    by_cases hd : d=0
    · simp [scheduleSuffix,hd,ih]
    · simp only [scheduleSuffix,pos_iff_ne_zero.mpr hd,ite_eq_left,tsub_zero]

lemma scheduleSuffix_append (ls rs : Schedule) (r : ℝ≥0) (hr : r<nnwidth ls) :
    scheduleSuffix (ls++rs) r = scheduleSuffix ls r++rs := by
  induction ls generalizing r with
  | nil => simp [nnwidth] at hr
  | cons l ls ih =>
    simp only [List.cons_append,scheduleSuffix]
    split_ifs with hrd
    · rfl
    · apply ih
      exact (tsub_lt_iff_left (le_of_not_gt hrd)).mpr hr

lemma finiteTimeField_suffix_val (β : ℝ≥0) (hβ : 0<β) (ls : Schedule)
    (s : ℝ) (r : ℝ≥0) (x : ℝ) :
    (finiteTimeField β hβ ls s (s+r)).val x = recursion β (scheduleSuffix ls r) x := by
  induction ls generalizing s r with
  | nil => rfl
  | cons l ls ih =>
    rcases l with ⟨a,d⟩
    have hc : s+(r:ℝ)<s+(d:ℝ) ↔ r<d := by exact_mod_cast add_lt_add_iff_left s
    simp only [finiteTimeField,scheduleSuffix,hc]
    split_ifs with hrd
    · change step a (Real.sqrt (s+d-(s+r))) (smoothRecursion β hβ ls).val x =
        step a (Real.sqrt ((d-r:ℝ≥0):ℝ)) (recursion β ls) x
      rw [smoothRecursion_val,NNReal.coe_sub hrd.le]
      congr 2
      ring
    · have he : s+(r:ℝ)=(s+d)+(r-d:ℝ≥0) := by
        rw [NNReal.coe_sub (le_of_not_gt hrd)]
        ring
      rw [he,ih]

 

lemma recursion_suffix_time_bound (β : ℝ≥0) (hβ : 0<β) (ls : Schedule)
    (ha : ∀ l∈ls,l.1 ≤ β) (r : ℝ≥0) (x : ℝ) :
    0 ≤ recursion β ls x-recursion β (scheduleSuffix ls r) x ∧
      recursion β ls x-recursion β (scheduleSuffix ls r) x ≤ (β:ℝ)*r/2 := by
  induction ls generalizing r with
  | nil => simp only [scheduleSuffix,sub_self]; exact ⟨le_rfl,by positivity⟩
  | cons l ls ih =>
    rcases l with ⟨a,d⟩
    have ha0 : (a:ℝ) ≤ β := by exact_mod_cast ha (a,d) List.mem_cons_self
    have ht : ∀ l∈ls,l.1 ≤ β := fun l hl => ha l (List.mem_cons_of_mem _ hl)
    have hh := smoothRecursion_hasParisiCurvature β hβ ls ht
    rw [scheduleSuffix]
    split_ifs with hrd
    · let f := (smoothRecursion β hβ ls).transform a (Real.sqrt (d-r:ℝ≥0))
      have hf := transform_hasParisiCurvature hh a.coe_nonneg ha0 (Real.sqrt (d-r:ℝ≥0))
      have hb := step_curvature_time_bound hf a.coe_nonneg ha0 (Real.sqrt r) (Real.sqrt_nonneg _) x
      rw [Real.sq_sqrt r.coe_nonneg] at hb
      have he : step a (Real.sqrt r) f.val x=recursion β ((a,d)::ls) x := by
        change step a (Real.sqrt r) (step a (Real.sqrt (d-r:ℝ≥0)) (smoothRecursion β hβ ls).val) x=_
        rw [step_semigroup (smoothRecursion β hβ ls).lipschitz,
          Real.sq_sqrt r.coe_nonneg,Real.sq_sqrt (d-r).coe_nonneg,
          ←NNReal.coe_add,add_tsub_cancel_of_le hrd.le,smoothRecursion_val]
        rfl
      rw [he] at hb
      simpa only [SmoothField.transform,smoothRecursion_val,recursion] using hb
    · have hb := step_curvature_time_bound hh a.coe_nonneg ha0 (Real.sqrt d) (Real.sqrt_nonneg _) x
      rw [Real.sq_sqrt d.coe_nonneg,smoothRecursion_val] at hb
      have hi := ih ht (r-d)
      rw [NNReal.coe_sub (le_of_not_gt hrd)] at hi
      simp only [recursion]
      constructor <;> nlinarith [hb.1,hb.2,hi.1,hi.2]

lemma shifted_schedule_suffix_error (β : ℝ≥0) (hβ : 0<β) (a b d : ℝ≥0)
    (ha : a ≤ β) (hb : b ≤ β) (mid : Schedule) (hm : ∀ l∈mid,l.1 ≤ β)
    (r : ℝ≥0) (hr : r<nnwidth ((a,d)::mid)) (x : ℝ) :
    |recursion β (scheduleSuffix ((a,d)::mid) r) x-
      recursion β (scheduleSuffix (mid++[(b,d)]) r) x| ≤ (β:ℝ)*d := by
  let low : Schedule := (a,d)::mid
  let high : Schedule := mid++[(b,d)]
  let full : Schedule := low++[(b,d)]
  have hhi : ∀ l∈high,l.1 ≤ β := by
    intro l hl
    rcases List.mem_append.mp hl with hl|hl
    · exact hm l hl
    · simp only [List.mem_singleton] at hl
      subst l
      exact hb
  have hfull : full=(a,d)::high := rfl
  have hterm := step_curvature_time_bound (terminal_hasParisiCurvature β hβ)
    b.coe_nonneg (by exact_mod_cast hb) (Real.sqrt d) (Real.sqrt_nonneg _) x
  have hleft : |recursion β (scheduleSuffix full r) x-recursion β (scheduleSuffix low r) x| ≤
      (β:ℝ)*d/2 := by
    rw [scheduleSuffix_append low _ r hr,recursion_eq_evolve,evolve_append,recursion_eq_evolve]
    apply evolve_stable (step_lipschitz (terminal_lipschitz hβ) b.coe_nonneg _)
      (terminal_lipschitz hβ) _ _ (fun y => ?_)
    have ht := step_curvature_time_bound (terminal_hasParisiCurvature β hβ)
      b.coe_nonneg (by exact_mod_cast hb) (Real.sqrt d) (Real.sqrt_nonneg _) y
    rw [Real.sq_sqrt d.coe_nonneg] at ht
    change 0 ≤ step b (Real.sqrt d) (terminal (β:ℝ)) y-terminal (β:ℝ) y ∧
      step b (Real.sqrt d) (terminal (β:ℝ)) y-terminal (β:ℝ) y ≤ (β:ℝ)*d/2 at ht
    exact abs_le.mpr ⟨(neg_nonpos.mpr (by positivity)).trans ht.1,ht.2⟩
  have hright : 0 ≤ recursion β (scheduleSuffix full r) x-recursion β (scheduleSuffix high r) x ∧
      recursion β (scheduleSuffix full r) x-recursion β (scheduleSuffix high r) x ≤ (β:ℝ)*d/2 := by
    rw [hfull,scheduleSuffix]
    split_ifs with hrd
    · have ht := step_curvature_time_bound (smoothRecursion_hasParisiCurvature β hβ high hhi)
        a.coe_nonneg (by exact_mod_cast ha) (Real.sqrt (d-r:ℝ≥0)) (Real.sqrt_nonneg _) x
      rw [Real.sq_sqrt (d-r).coe_nonneg,NNReal.coe_sub hrd.le,smoothRecursion_val] at ht
      have hh := recursion_suffix_time_bound β hβ high hhi r x
      simp only [recursion,NNReal.coe_sub hrd.le]
      constructor <;> nlinarith [ht.1,ht.2,hh.1,hh.2]
    · have hh := recursion_suffix_time_bound β hβ (scheduleSuffix high (r-d))
        (scheduleSuffix_coeff_bound high hhi (r-d)) d x
      rw [scheduleSuffix_add,tsub_add_cancel_of_le (le_of_not_gt hrd)] at hh
      exact hh
  calc
    _ ≤ |recursion β (scheduleSuffix low r) x-recursion β (scheduleSuffix full r) x|+
        |recursion β (scheduleSuffix full r) x-recursion β (scheduleSuffix high r) x| :=
      abs_sub_le _ _ _
    _ ≤ (β:ℝ)*d/2+(β:ℝ)*d/2 := add_le_add
      (by simpa only [abs_sub_comm] using hleft)
      (abs_le.mpr ⟨by linarith [hright.1],hright.2⟩)
    _ = _ := by ring

lemma dyadic_suffix_grid_error (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0}
    (hb : ∀ t,γ t ≤ β) (t d : ℝ≥0) (n : ℕ) (r : ℝ≥0) (hr : r<d) (x : ℝ) :
    |recursion β (scheduleSuffix (dyadicSchedule γ false t d n) r) x-
      recursion β (scheduleSuffix (dyadicSchedule γ true t d n) r) x| ≤
      (β:ℝ)*dyadicMesh d n := by
  have hs := dyadicSchedule_shift γ t d n
  have hn := dyadicSchedule_nonempty γ false t d n
  have hw := dyadicSchedule_nnwidth γ false t d n
  have hc := dyadicSchedule_coeff_bound hb false t d n
  generalize he : dyadicSchedule γ false t d n=ls at hs hn hw hc ⊢
  cases ls with
  | nil => exact (hn rfl).elim
  | cons c mid =>
    simp only [List.cons_append,List.cons.injEq] at hs
    rw [hs.1] at hw hc ⊢
    rw [←hs.2]
    apply shifted_schedule_suffix_error β hβ _ _ _ (hb t) (hb (t+d)) mid
      (fun l hl => hc l (List.mem_cons_of_mem _ hl)) r (by rwa [hw])

lemma dyadic_suffix_value_bounds {f : ℝ → ℝ} (hf : LipschitzWith 1 f)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) {β : ℝ} (hb : ∀ t,(γ t:ℝ) ≤ β)
    (t d : ℝ≥0) (n : ℕ) (r : ℝ≥0) (hr : r<d) (x : ℝ) :
    evolve (scheduleSuffix (dyadicSchedule γ false t d n) r) f x ≤
      dyadicEvolution γ (t+r) (d-r) f x ∧
    dyadicEvolution γ (t+r) (d-r) f x ≤
      evolve (scheduleSuffix (dyadicSchedule γ true t d n) r) f x := by
  have hw (u : Bool) : nnwidth (scheduleSuffix (dyadicSchedule γ u t d n) r)=d-r := by
    rw [nnwidth_scheduleSuffix,dyadicSchedule_nnwidth]
  constructor
  · apply ge_of_tendsto (dyadic_high_tendsto hf hγ hb (t+r) (d-r) x)
    exact Eventually.of_forall fun k => evolve_le_of_scheduleValue_le hf _ _
      (by rw [hw,dyadicSchedule_nnwidth]) (fun u hu => by
        rw [scheduleValue_suffix]
        have hur : r+u<d := by
          have hu' : u < d-r := by simpa [hw] using hu
          simpa only [add_comm] using (add_lt_add_left hu' r).trans_eq
            (tsub_add_cancel_of_le hr.le)
        exact (dyadicSchedule_value_bounds hγ t d n hur).1.trans
          (by simpa only [add_assoc] using (dyadicSchedule_value_bounds hγ (t+r) (d-r) k
            (by simpa [hw] using hu)).2)) x
  · apply le_of_tendsto (dyadic_low_tendsto hf hγ (t+r) (d-r) x)
    exact Eventually.of_forall fun k => evolve_le_of_scheduleValue_le hf _ _
      (by rw [hw,dyadicSchedule_nnwidth]) (fun u hu => by
        rw [scheduleValue_suffix]
        have hu' : u<d-r := by simpa [dyadicSchedule_nnwidth] using hu
        have hur : r+u<d := by
          simpa only [add_comm] using (add_lt_add_left hu' r).trans_eq (tsub_add_cancel_of_le hr.le)
        exact (dyadicSchedule_value_bounds hγ (t+r) (d-r) k hu').1.trans
          (by simpa only [add_assoc] using (dyadicSchedule_value_bounds hγ t d n hur).2)) x

lemma dyadic_suffix_value_error (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0}
    (hγ : Monotone γ) (hb : ∀ t,γ t ≤ β) (t d : ℝ≥0) (n : ℕ)
    (r : ℝ≥0) (hr : r<d) (x : ℝ) :
    |recursion β (scheduleSuffix (dyadicSchedule γ false t d n) r) x-
      dyadicEvolution γ (t+r) (d-r) (terminal β) x| ≤ (β:ℝ)*dyadicMesh d n := by
  have hb' := dyadic_suffix_value_bounds (terminal_lipschitz hβ) hγ
    (fun t => by exact_mod_cast hb t) t d n r hr x
  rw [←recursion_eq_evolve,←recursion_eq_evolve] at hb'
  have he := abs_le.mp (dyadic_suffix_grid_error β hβ hb t d n r hr x)
  apply abs_le.mpr
  constructor
  · exact he.1.trans (sub_le_sub_left hb'.2 _)
  · exact (sub_nonpos.mpr hb'.1).trans (mul_nonneg β.coe_nonneg (dyadicMesh d n).coe_nonneg)

end ParisiFinite

end

end OAI
