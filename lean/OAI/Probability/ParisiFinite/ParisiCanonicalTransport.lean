import Mathlib
import OAI.Probability.ParisiFinite.ParisiConjugateTransport

namespace OAI

/-! Parisi Canonical Transport. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite
open ParisiPath

lemma smoothEvolve_curvature {β : ℝ≥0} {f : SmoothField} (hf : HasParisiCurvature β f)
    (ls : Schedule) (ha : ∀ l∈ls,l.1≤β) : HasParisiCurvature β (smoothEvolve f ls) := by
  induction ls with
  | nil => exact hf
  | cons l ls ih =>
    exact transform_hasParisiCurvature
      (ih (fun k hk => ha k (List.mem_cons_of_mem _ hk))) l.1.coe_nonneg
      (by exact_mod_cast ha l List.mem_cons_self) _

lemma scheduleField_curvature {β : ℝ≥0} {f : SmoothField} (hf : HasParisiCurvature β f)
    (ls : Schedule) (ha : ∀ l∈ls,l.1≤β) (s t : ℝ) :
    HasParisiCurvature β (scheduleField f ls s t) := by
  induction ls generalizing s with
  | nil => exact hf
  | cons l ls ih =>
    have htail : ∀ k∈ls,k.1≤β := fun k hk => ha k (List.mem_cons_of_mem _ hk)
    simp only [scheduleField]
    split_ifs
    · exact transform_hasParisiCurvature (smoothEvolve_curvature hf ls htail)
        l.1.coe_nonneg (by exact_mod_cast ha l List.mem_cons_self) _
    · exact ih htail _

abbrev genericRecursion (f : SmoothField) (ls : Schedule) : ℝ → ℝ := evolve ls f.val

lemma scheduleField_suffix_val (β : ℝ≥0) (f : SmoothField) (_hfc : HasParisiCurvature β f) (ls : Schedule)
    (s : ℝ) (r : ℝ≥0) (x : ℝ) :
    (scheduleField f ls s (s+r)).val x = genericRecursion f (scheduleSuffix ls r) x := by
  induction ls generalizing s r with
  | nil => rfl
  | cons l ls ih =>
    rcases l with ⟨a,d⟩
    have hc : s+(r:ℝ)<s+(d:ℝ) ↔ r<d := by exact_mod_cast add_lt_add_iff_left s
    simp only [scheduleField,scheduleSuffix,hc]
    split_ifs with hrd
    · change step a (Real.sqrt (s+d-(s+r))) (smoothEvolve f ls).val x =
        step a (Real.sqrt ((d-r:ℝ≥0):ℝ)) (genericRecursion f ls) x
      rw [smoothEvolve_val,NNReal.coe_sub hrd.le]
      congr 2
      ring
    · have he : s+(r:ℝ)=(s+d)+(r-d:ℝ≥0) := by
        rw [NNReal.coe_sub (le_of_not_gt hrd)]
        ring
      rw [he,ih]

 

lemma evolve_suffix_time_bound (β : ℝ≥0) (f : SmoothField) (hfc : HasParisiCurvature β f) (ls : Schedule)
    (ha : ∀ l∈ls,l.1 ≤ β) (r : ℝ≥0) (x : ℝ) :
    0 ≤ genericRecursion f ls x-genericRecursion f (scheduleSuffix ls r) x ∧
      genericRecursion f ls x-genericRecursion f (scheduleSuffix ls r) x ≤ (β:ℝ)*r/2 := by
  induction ls generalizing r with
  | nil => simp only [scheduleSuffix,sub_self]; exact ⟨le_rfl,by positivity⟩
  | cons l ls ih =>
    rcases l with ⟨a,d⟩
    have ha0 : (a:ℝ) ≤ β := by exact_mod_cast ha (a,d) List.mem_cons_self
    have ht : ∀ l∈ls,l.1 ≤ β := fun l hl => ha l (List.mem_cons_of_mem _ hl)
    have hh := smoothEvolve_curvature hfc ls ht
    rw [scheduleSuffix]
    split_ifs with hrd
    · let fmid := (smoothEvolve f ls).transform a (Real.sqrt (d-r:ℝ≥0))
      have hf := transform_hasParisiCurvature hh a.coe_nonneg ha0 (Real.sqrt (d-r:ℝ≥0))
      have hb := step_curvature_time_bound hf a.coe_nonneg ha0 (Real.sqrt r) (Real.sqrt_nonneg _) x
      rw [Real.sq_sqrt r.coe_nonneg] at hb
      have he : step a (Real.sqrt r) fmid.val x=genericRecursion f ((a,d)::ls) x := by
        change step a (Real.sqrt r) (step a (Real.sqrt (d-r:ℝ≥0)) (smoothEvolve f ls).val) x=_
        rw [step_semigroup (smoothEvolve f ls).lipschitz,
          Real.sq_sqrt r.coe_nonneg,Real.sq_sqrt (d-r).coe_nonneg,
          ←NNReal.coe_add,add_tsub_cancel_of_le hrd.le,smoothEvolve_val]
        rfl
      rw [he] at hb
      simpa only [SmoothField.transform,smoothEvolve_val,genericRecursion,evolve] using hb
    · have hb := step_curvature_time_bound hh a.coe_nonneg ha0 (Real.sqrt d) (Real.sqrt_nonneg _) x
      rw [Real.sq_sqrt d.coe_nonneg,smoothEvolve_val] at hb
      have hi := ih ht (r-d)
      rw [NNReal.coe_sub (le_of_not_gt hrd)] at hi
      simp only [genericRecursion,evolve]
      constructor <;> nlinarith [hb.1,hb.2,hi.1,hi.2]

lemma general_shifted_schedule_suffix_error (β : ℝ≥0) (f : SmoothField) (hfc : HasParisiCurvature β f) (a b d : ℝ≥0)
    (ha : a ≤ β) (hb : b ≤ β) (mid : Schedule) (hm : ∀ l∈mid,l.1 ≤ β)
    (r : ℝ≥0) (hr : r<nnwidth ((a,d)::mid)) (x : ℝ) :
    |genericRecursion f (scheduleSuffix ((a,d)::mid) r) x-
      genericRecursion f (scheduleSuffix (mid++[(b,d)]) r) x| ≤ (β:ℝ)*d := by
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
  have hterm := step_curvature_time_bound (hfc)
    b.coe_nonneg (by exact_mod_cast hb) (Real.sqrt d) (Real.sqrt_nonneg _) x
  have hleft : |genericRecursion f (scheduleSuffix full r) x-genericRecursion f (scheduleSuffix low r) x| ≤
      (β:ℝ)*d/2 := by
    rw [scheduleSuffix_append low _ r hr,genericRecursion,evolve_append,genericRecursion]
    apply evolve_stable (step_lipschitz ((show LipschitzWith 1 f.val from by simpa only [←hfc.1] using f.lipschitz)) b.coe_nonneg _)
      ((show LipschitzWith 1 f.val from by simpa only [←hfc.1] using f.lipschitz)) _ _ (fun y => ?_)
    have ht := step_curvature_time_bound (hfc)
      b.coe_nonneg (by exact_mod_cast hb) (Real.sqrt d) (Real.sqrt_nonneg _) y
    rw [Real.sq_sqrt d.coe_nonneg] at ht
    change 0 ≤ step b (Real.sqrt d) f.val y-f.val y ∧
      step b (Real.sqrt d) f.val y-f.val y ≤ (β:ℝ)*d/2 at ht
    exact abs_le.mpr ⟨(neg_nonpos.mpr (by positivity)).trans ht.1,ht.2⟩
  have hright : 0 ≤ genericRecursion f (scheduleSuffix full r) x-genericRecursion f (scheduleSuffix high r) x ∧
      genericRecursion f (scheduleSuffix full r) x-genericRecursion f (scheduleSuffix high r) x ≤ (β:ℝ)*d/2 := by
    rw [hfull,scheduleSuffix]
    split_ifs with hrd
    · have ht := step_curvature_time_bound (smoothEvolve_curvature hfc high hhi)
        a.coe_nonneg (by exact_mod_cast ha) (Real.sqrt (d-r:ℝ≥0)) (Real.sqrt_nonneg _) x
      rw [Real.sq_sqrt (d-r).coe_nonneg,NNReal.coe_sub hrd.le,smoothEvolve_val] at ht
      have hh := evolve_suffix_time_bound β f hfc high hhi r x
      simp only [genericRecursion,evolve,NNReal.coe_sub hrd.le]
      constructor <;> nlinarith [ht.1,ht.2,hh.1,hh.2]
    · have hh := evolve_suffix_time_bound β f hfc (scheduleSuffix high (r-d))
        (scheduleSuffix_coeff_bound high hhi (r-d)) d x
      rw [scheduleSuffix_add,tsub_add_cancel_of_le (le_of_not_gt hrd)] at hh
      exact hh
  calc
    _ ≤ |genericRecursion f (scheduleSuffix low r) x-genericRecursion f (scheduleSuffix full r) x|+
        |genericRecursion f (scheduleSuffix full r) x-genericRecursion f (scheduleSuffix high r) x| :=
      abs_sub_le _ _ _
    _ ≤ (β:ℝ)*d/2+(β:ℝ)*d/2 := add_le_add
      (by simpa only [abs_sub_comm] using hleft)
      (abs_le.mpr ⟨by linarith [hright.1],hright.2⟩)
    _ = _ := by ring

lemma general_dyadic_suffix_grid_error (β : ℝ≥0) (f : SmoothField) (hfc : HasParisiCurvature β f) {γ : ℝ≥0 → ℝ≥0}
    (hb : ∀ t,γ t ≤ β) (t d : ℝ≥0) (n : ℕ) (r : ℝ≥0) (hr : r<d) (x : ℝ) :
    |genericRecursion f (scheduleSuffix (dyadicSchedule γ false t d n) r) x-
      genericRecursion f (scheduleSuffix (dyadicSchedule γ true t d n) r) x| ≤
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
    apply general_shifted_schedule_suffix_error β f hfc _ _ _ (hb t) (hb (t+d)) mid
      (fun l hl => hc l (List.mem_cons_of_mem _ hl)) r (by rwa [hw])

lemma general_dyadic_suffix_value_error {β : ℝ≥0} {f : SmoothField}
    (hf : HasParisiCurvature β f) {γ : ℝ≥0 → ℝ≥0}
    (hγ : Monotone γ) (hb : ∀ t,γ t ≤ β) (t d : ℝ≥0) (n : ℕ)
    (r : ℝ≥0) (hr : r<d) (x : ℝ) :
    |evolve (scheduleSuffix (dyadicSchedule γ false t d n) r) f.val x-
      dyadicEvolution γ (t+r) (d-r) f.val x| ≤ (β:ℝ)*dyadicMesh d n := by
  have hfl : LipschitzWith 1 f.val := by simpa only [←hf.1] using f.lipschitz
  have hb' := dyadic_suffix_value_bounds hfl hγ
    (fun t => by exact_mod_cast hb t) t d n r hr x
  have he := abs_le.mp (general_dyadic_suffix_grid_error β f hf hb t d n r hr x)
  apply abs_le.mpr
  constructor
  · exact he.1.trans (sub_le_sub_left hb'.2 _)
  · exact (sub_nonpos.mpr hb'.1).trans (mul_nonneg β.coe_nonneg (dyadicMesh d n).coe_nonneg)

lemma general_dyadic_field_tendstoUniformly {β : ℝ≥0} {f : SmoothField}
    (hf : HasParisiCurvature β f) {γ : ℝ≥0 → ℝ≥0}
    (hγ : Monotone γ) (hb : ∀ t,γ t≤β) (d r : ℝ≥0) (hr : r<d) :
    TendstoUniformly (fun n => (scheduleField f (dyadicSchedule γ false 0 d n) 0 r).val)
      (dyadicEvolution γ r (d-r) f.val) atTop := by
  have he : Tendsto (fun n => (β:ℝ)*(dyadicMesh d n:ℝ)) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero] using (dyadicMesh_tendsto d).const_mul (β:ℝ)
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [he.eventually (gt_mem_nhds hε)] with n hn x
  rw [Real.dist_eq,abs_sub_comm]
  have hh := general_dyadic_suffix_value_error hf hγ hb 0 d n r hr x
  rw [←zero_add (r:ℝ),scheduleField_suffix_val β f hf]
  simpa only [genericRecursion,zero_add] using hh.trans_lt hn

lemma general_dyadic_gradient_tendstoUniformly {β : ℝ≥0} {f : SmoothField}
    (hf : HasParisiCurvature β f) {γ : ℝ≥0 → ℝ≥0}
    (hγ : Monotone γ) (hb : ∀ t,γ t≤β) (d r : ℝ≥0) (hr : r<d) :
    TendstoUniformly (fun n => (scheduleField f (dyadicSchedule γ false 0 d n) 0 r).d1)
      (deriv (dyadicEvolution γ r (d-r) f.val)) atTop := by
  obtain ⟨m,hu,hd,_,_⟩ := exists_uniform_derivative_limit
    (fun n => scheduleField_curvature hf _ (dyadicSchedule_coeff_bound hb false 0 d n) 0 r)
    (general_dyadic_field_tendstoUniformly hf hγ hb d r hr)
  have he : m=deriv (dyadicEvolution γ r (d-r) f.val) := funext fun x => (hd x).deriv.symm
  rwa [he] at hu

lemma canonicalSmoothField_curvature (β : ℝ≥0) (hβ : 0<β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t≤β) (t : ℝ≥0) :
    HasParisiCurvature β (canonicalSmoothField β hβ hγ hb t) := by
  refine ⟨rfl,fun x => ?_⟩
  exact ⟨(fieldCurvature_bounds β hβ hγ hb t x).1.le,
    (fieldCurvature_bounds β hβ hγ hb t x).2⟩

lemma prefix_dyadic_gradient_tendstoUniformly (β : ℝ≥0) (hβ : 0<β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t≤β)
    (d r : ℝ≥0) (hd : d≤1) (hr : r<d) :
    TendstoUniformly (fun n =>
      (scheduleField (canonicalSmoothField β hβ hγ hb d) (dyadicSchedule γ false 0 d n) 0 r).d1)
      (fieldGradient β γ r) atTop := by
  have he : dyadicEvolution γ r (d-r) (canonicalSmoothField β hβ hγ hb d).val=field β γ r :=
    funext fun x => (field_DPP β hβ hγ hb hr.le hd x).symm
  simpa only [he,fieldGradient] using
    general_dyadic_gradient_tendstoUniformly (canonicalSmoothField_curvature β hβ hγ hb d)
      hγ hb d r hr

end ParisiFinite

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite
open ParisiPath

lemma scheduleField_measurable_d1 (f : SmoothField) (ls : Schedule) (s : ℝ) :
    Measurable (fun p : ℝ×ℝ => (scheduleField f ls s p.1).d1 p.2) := by
  induction ls generalizing s with
  | nil => exact f.continuousD1.measurable.comp measurable_snd
  | cons l ls ih =>
    have hh : Measurable (fun p : ℝ×ℝ => if p.1<s+l.2 then
        (fieldOnInterval (smoothEvolve f ls) l.1 (s+l.2) p.1).d1 p.2
        else (scheduleField f ls (s+l.2) p.1).d1 p.2) :=
      Measurable.ite (measurableSet_lt measurable_fst measurable_const)
        (continuous_fieldOnInterval_d1 (smoothEvolve f ls) l.1 (s+l.2)).measurable (ih _)
    convert! hh using 1
    funext p
    simp only [scheduleField]
    split_ifs <;> rfl

lemma finiteTimeCoefficient_continuous_ae (ls : Schedule) (s : ℝ) :
    ∀ᵐ t ∂volume,ContinuousAt (finiteTimeCoefficient ls s) t := by
  induction ls generalizing s with
  | nil => exact ae_of_all _ fun t => continuousAt_const
  | cons l ls ih =>
    filter_upwards [ih (s+l.2),volume.ae_ne (s+(l.2:ℝ))] with t ht hne
    change t≠s+(l.2:ℝ) at hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · apply (continuousAt_const (y := (l.1:ℝ))).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hlt] with u hu
      exact ite_eq_left hu
    · apply ht.congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hgt] with u hu
      exact ite_eq_right (not_lt_of_ge hu.le)

def scheduleDrift {β : ℝ≥0} {f : SmoothField} (hf : HasParisiCurvature β f)
    (ls : Schedule) (ha : ∀ l∈ls,l.1≤β) : Drift (β*β) β where
  val := fun t x => finiteTimeCoefficient ls 0 t*(scheduleField f ls 0 t).d1 x
  measurable := (finiteTimeCoefficient_measurable ls 0 |>.comp measurable_fst).mul
    (scheduleField_measurable_d1 f ls 0)
  bound := by
    intro t x
    have hc := scheduleField_curvature hf ls ha 0 t
    have hg : |(scheduleField f ls 0 t).d1 x|≤(1:ℝ) := by
      simpa only [hc.1,NNReal.coe_one] using (scheduleField f ls 0 t).normD1 x
    rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hg (abs_nonneg _)).trans
      (by simpa only [mul_one] using finiteTimeCoefficient_bound β ls ha 0 t)
  lipschitz := by
    intro t
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq,←mul_sub,abs_mul,NNReal.coe_mul]
    have hh := (curvature_gradient_lipschitz (scheduleField_curvature hf ls ha 0 t)).dist_le_mul x y
    rw [Real.dist_eq,Real.dist_eq] at hh
    have hp := finiteTimeCoefficient_bound β ls ha 0 t
    calc
      _ ≤ |finiteTimeCoefficient ls 0 t| * ((β:ℝ)*|x-y|) := mul_le_mul_of_nonneg_left hh (abs_nonneg _)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hp (mul_nonneg β.coe_nonneg (abs_nonneg (x-y)))]

lemma scheduleDrift_joint_ae_continuous {β : ℝ≥0} {f : SmoothField}
    (hf : HasParisiCurvature β f) (ls : Schedule) (ha : ∀ l∈ls,l.1≤β)
    (hw : width ls≤1) :
    ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry (scheduleDrift hf ls ha).val) (t,x) := by
  let r := generalScheduleTimeRealization f ls 0 le_rfl (by simpa only [zero_add] using hw)
  filter_upwards [r.test.jointD1,finiteTimeCoefficient_continuous_ae ls 0] with t ht hc hmem x
  have he : r.test.d1=fun t x => (scheduleField f ls 0 t).d1 x := funext fun t => funext fun x => r.d1_eq t x
  have hh := ht hmem x
  rw [he] at hh
  exact (hc.comp continuousAt_fst).mul hh

end ParisiFinite

namespace ParisiPath
variable {K M : ℝ≥0}

def patchDrift (u v : Drift K M) (a b : ℝ) : Drift K M where
  val := fun t x => if t∈Ioo a b then u.val t x else v.val t x
  measurable := Measurable.ite (measurableSet_Ioo.preimage measurable_fst) u.measurable v.measurable
  bound := fun t x => by split_ifs; exact u.bound t x; exact v.bound t x
  lipschitz := fun t => by split_ifs; exact u.lipschitz t; exact v.lipschitz t

lemma continuousAt_patch_Ioo {u v : ℝ×ℝ → ℝ} {a b t x : ℝ}
    (ht0 : t≠a) (ht1 : t≠b) (hu : ContinuousAt u (t,x)) (hv : ContinuousAt v (t,x)) :
    ContinuousAt (fun p : ℝ×ℝ => if p.1∈Ioo a b then u p else v p) (t,x) := by
  by_cases hmem : t∈Ioo a b
  · apply hu.congr_of_eventuallyEq
    filter_upwards [continuousAt_fst.preimage_mem_nhds (Ioo_mem_nhds hmem.1 hmem.2)] with p hp
    exact ite_eq_left hp
  · have hn : ∀ᶠ p : ℝ×ℝ in 𝓝 (t,x),p.1∉Ioo a b := by
      rcases le_total t a with hta | hat
      · have hta : t<a := lt_of_le_of_ne hta ht0
        filter_upwards [continuousAt_fst.preimage_mem_nhds (Iio_mem_nhds hta)] with p hp
        exact fun hh => (not_lt_of_ge hp.le) hh.1
      · have hbt : b<t := lt_of_le_of_ne (by by_contra! h;exact hmem ⟨lt_of_le_of_ne hat ht0.symm,h⟩) ht1.symm
        filter_upwards [continuousAt_fst.preimage_mem_nhds (Ioi_mem_nhds hbt)] with p hp
        exact fun hh => (not_lt_of_ge hp.le) hh.2
    apply hv.congr_of_eventuallyEq
    filter_upwards [hn] with p hp
    exact ite_eq_right hp

lemma patchDrift_joint_ae_continuous (u v : Drift K M) (a b : ℝ)
    (hu : ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry u.val) (t,x))
    (hv : ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry v.val) (t,x)) :
    ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry (patchDrift u v a b).val) (t,x) := by
  filter_upwards [hu,hv,volume.ae_ne a,volume.ae_ne b] with t ht hu ha hb hmem x
  exact continuousAt_patch_Ioo ha hb (ht hmem x) (hu hmem x)

end ParisiPath

namespace ParisiFinite
lemma prefix_dyadic_coefficient_tendsto_ae {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (d : ℝ≥0) :
    ∀ᵐ t ∂volume,t ∈ Ioo (0:ℝ) d →
      Tendsto (fun n => finiteTimeCoefficient (dyadicSchedule γ false 0 d n) 0 t)
        atTop (𝓝 (γ (Real.toNNReal t):ℝ)) := by
  let c (s : ℝ) : ℝ := γ (Real.toNNReal s)
  have hm : Monotone c := fun s t h =>
    NNReal.coe_le_coe.mpr (hγ (Real.toNNReal_le_toNNReal h))
  have hc : ∀ᵐ t ∂volume,ContinuousAt c t := by
    rw [ae_iff]
    exact hm.countable_not_continuousAt.measure_zero volume
  filter_upwards [hc] with t ht hmem
  have hr : Real.toNNReal t < d := by
    exact_mod_cast (show (Real.toNNReal t:ℝ)<d by rw [Real.coe_toNNReal _ hmem.1.le];exact hmem.2)
  have hh := dyadicSchedule_low_value_coe_tendsto γ 0 d (Real.toNNReal t) hr
    (by simpa only [zero_add,Real.coe_toNNReal _ hmem.1.le,c] using ht)
  simpa only [zero_add,←finiteTimeCoefficient_scheduleValue _ (0:ℝ),
    Real.coe_toNNReal _ hmem.1.le] using hh

namespace BoundedCoefficient
open ParisiPath
variable {β : ℝ≥0}

def prefixDrift (c : BoundedCoefficient β) (hβ : 0<β) (d : ℝ≥0) (n : ℕ) : Drift (β*β) β :=
  patchDrift (scheduleDrift (canonicalSmoothField_curvature β hβ c.mono c.bound d)
    (dyadicSchedule c.val false 0 d n) (dyadicSchedule_coeff_bound c.bound false 0 d n))
    (c.driftData hβ) 0 d

lemma prefixDrift_joint_ae_continuous (c : BoundedCoefficient β) (hβ : 0<β)
    (d : ℝ≥0) (hd : d≤1) (n : ℕ) :
    ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry (c.prefixDrift hβ d n).val) (t,x) :=
  patchDrift_joint_ae_continuous _ _ _ _
    (scheduleDrift_joint_ae_continuous _ _ _ (by rw [dyadicSchedule_width];exact_mod_cast hd))
    (c.drift_joint_ae_continuous hβ)

lemma prefixDrift_tendsto_ae (c : BoundedCoefficient β) (hβ : 0<β)
    (d : ℝ≥0) (hd : d≤1) :
    ∀ᵐ t ∂volume,∀ x,Tendsto (fun n => (c.prefixDrift hβ d n).val t x) atTop
      (𝓝 ((c.driftData hβ).val t x)) := by
  filter_upwards [prefix_dyadic_coefficient_tendsto_ae c.mono d] with t ht x
  by_cases hm : t∈Ioo (0:ℝ) d
  · have hr : Real.toNNReal t<d := by
      exact_mod_cast (show (Real.toNNReal t:ℝ)<d by rw [Real.coe_toNNReal _ hm.1.le];exact hm.2)
    have hh := (prefix_dyadic_gradient_tendstoUniformly β hβ c.mono c.bound d _ hd hr).tendsto_at x
    rw [Real.coe_toNNReal _ hm.1.le] at hh
    simpa only [prefixDrift,patchDrift,ite_eq_left hm,scheduleDrift,driftData,drift,real] using (ht hm).mul hh
  · simpa only [prefixDrift,patchDrift,ite_eq_right hm] using
      (tendsto_const_nhds (x := (c.driftData hβ).val t x))

lemma prefix_solution_tendsto (c : BoundedCoefficient β) (hβ : 0<β)
    (d : ℝ≥0) (hd : d≤1) (W : Path) :
    Tendsto (fun n => solution (c.prefixDrift hβ d n) W) atTop (𝓝 (solution (c.driftData hβ) W)) :=
  solution_tendsto_drift_ae (c.prefixDrift_tendsto_ae hβ d hd) W

end BoundedCoefficient
end ParisiFinite

namespace ParisiFinite.BoundedCoefficient
open ParisiPath ParisiSpectral
variable {β : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

 

lemma actual_conjugate_positive_continuous (c : BoundedCoefficient β) (hβ : 0<β)
    (hW : IsBrownianReal W P) (d : ℝ≥0) (hd0 : d≠0) (hd1 : d≤1)
    (ha : 0<c.val d) {g : ℝ → ℝ} (hg : Continuous g) (R : ℝ≥0) (hR : ∀ x,|g x|≤R)
    (hψ : PositiveDefinite (fun x => Real.exp ((c.val d:ℝ)*field β c.val d x)*g x)) :
    0≤∫ ω,g (solution (c.driftData hβ) (brownianPath W ω)
      ⟨d,d.coe_nonneg,by exact_mod_cast hd1⟩) ∂P := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  let f := canonicalSmoothField β hβ c.mono c.bound d
  let ψ : ℝ → ℝ := fun x => Real.exp ((c.val d:ℝ)*f.val x)*g x
  have hcψ : Continuous ψ := ((continuous_const.mul f.continuousVal).rexp).mul hg
  let ls (n : ℕ) := dyadicSchedule c.val false 0 d n
  let X (n : ℕ) (ω : Ω) := solution (c.prefixDrift hβ d n) (brownianPath W ω)
    ⟨d,d.coe_nonneg,by exact_mod_cast hd1⟩
  let Y (ω : Ω) := solution (c.driftData hβ) (brownianPath W ω)
    ⟨d,d.coe_nonneg,by exact_mod_cast hd1⟩
  have ht (ω : Ω) : Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)) :=
    (show Continuous (fun Z : Path => Z ⟨d,d.coe_nonneg,by exact_mod_cast hd1⟩) from by fun_prop).continuousAt.tendsto.comp
      (c.prefix_solution_tendsto hβ d hd1 (brownianPath W ω))
  have hj : Tendsto (fun n => ∫ ω,g (X n ω) ∂P) atTop (𝓝 (∫ ω,g (Y ω) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (R:ℝ))
    · intro n
      exact (hg.measurable.comp_aemeasurable
        (aemeasurable_solution_eval _ _ (brownianPath_aemeasurable_eval hW) _)).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hR (X n ω)
    · exact ae_of_all _ fun ω => hg.continuousAt.tendsto.comp (ht ω)
  apply ge_of_tendsto hj
  filter_upwards [] with n
  have ho : ParisiGuerra.OrderedFrom (c.val d) 0 (ls n) := by
    simpa only [zero_add] using ordered_lower (c.val 0).coe_nonneg
      (dyadicSchedule_ordered c.mono false 0 d n)
  have hh := conjugate_linearEvolve_positiveDefinite f.lipschitz hψ hcψ
    (by exact_mod_cast ha) (field_coshCone β hβ c.mono c.bound d (by exact_mod_cast ha) le_rfl)
    (a := (0:ℝ)) le_rfl (ls n) ho
  have he : (fun y => Real.exp (-(c.val d:ℝ)*f.val y)*ψ y)=g := by
    funext x
    dsimp only [ψ]
    rw [←mul_assoc,←Real.exp_add]
    ring_nf
    rw [Real.exp_zero,one_mul]
  change PositiveDefinite (fun x => Real.exp (0*evolve (ls n) f.val x)*
    linearEvolve f.val (fun y => Real.exp (-(c.val d:ℝ)*f.val y)*ψ y) (ls n) x) at hh
  rw [he] at hh
  have hp := hh.at_zero
  simp only [zero_mul,Real.exp_zero,one_mul] at hp
  have heq := generalSchedule_actual_transport_continuous hW (c.prefixDrift hβ d n)
    (c.prefixDrift_joint_ae_continuous hβ d hd1 n) f hg R hR (ls n) d hd0 hd1
    (dyadicSchedule_width c.val false 0 d n) (fun t ht x => by
      simp only [prefixDrift,patchDrift,ite_eq_left ht,scheduleDrift,ls,f])
  exact heq.symm ▸ hp

lemma conjugate_expectation_nonneg (c : BoundedCoefficient β) (hβ : 0<β)
    (hW : IsBrownianReal W P) (d : ℝ≥0) (hd0 : d≠0) (hd1 : d≤1)
    (ha : 0<c.val d) {ψ : ℝ → ℝ} (hψ : PositiveDefinite ψ) (hcψ : Continuous ψ) :
    0≤∫ ω,Real.exp (-(c.val d:ℝ)*field β c.val d
      (solution (c.driftData hβ) (brownianPath W ω) ⟨d,d.coe_nonneg,by exact_mod_cast hd1⟩))*
      ψ (solution (c.driftData hβ) (brownianPath W ω) ⟨d,d.coe_nonneg,by exact_mod_cast hd1⟩) ∂P := by
  let g : ℝ → ℝ := fun x => Real.exp (-(c.val d:ℝ)*field β c.val d x)*ψ x
  have hcg : Continuous g := ((continuous_const.mul
    (field_lipschitz β hβ c.mono c.bound d).continuous).rexp).mul hcψ
  have hp : PositiveDefinite g :=
    ((field_coshCone β hβ c.mono c.bound d (by exact_mod_cast ha) le_rfl).neg_exp_positiveDefinite
      (by exact_mod_cast ha) (c.val d).coe_nonneg).mul hψ
  apply c.actual_conjugate_positive_continuous hβ hW d hd0 hd1 ha hcg
    (Real.toNNReal (g 0)) (fun x => by
      simpa only [Real.norm_eq_abs,Real.coe_toNNReal _ hp.at_zero] using hp.norm_le x)
  convert! hψ using 1
  funext x
  dsimp only [g]
  rw [←mul_assoc,←Real.exp_add]
  have he : (c.val d:ℝ)*field β c.val d x+(-(c.val d:ℝ))*field β c.val d x=0 := by ring
  rw [he,Real.exp_zero,one_mul]

end ParisiFinite.BoundedCoefficient

 

 

open MeasureTheory ProbabilityTheory Filter Function Set Real
open scoped Topology NNReal
namespace ParisiSpectral
open ParisiFinite

def stepWeight (a s : ℝ) (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  exp (a*f (p.1+s*p.2))/exp (a*step a s f p.1)

def stepJoint (μ : Measure ℝ) (a s : ℝ) (f : ℝ → ℝ) : Measure (ℝ × ℝ) :=
  (μ.prod (gaussianReal 0 1)).withDensity (fun p => ENNReal.ofReal (stepWeight a s f p))

def stepLaw (μ : Measure ℝ) (a s : ℝ) (f : ℝ → ℝ) : Measure ℝ :=
  (stepJoint μ a s f).map (fun p => p.1+s*p.2)

lemma stepWeight_pos (a s : ℝ) (f : ℝ → ℝ) (p : ℝ × ℝ) :
    0<stepWeight a s f p := div_pos (exp_pos _) (exp_pos _)

lemma continuous_stepWeight {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    {a : ℝ} (ha : 0≤a) (s : ℝ) : Continuous (stepWeight a s f) := by
  have hs := (step_lipschitz hf ha s).continuous
  unfold stepWeight
  exact ((continuous_const.mul (hf.continuous.comp (continuous_fst.add
    (continuous_const.mul continuous_snd)))).rexp).div
    ((continuous_const.mul (hs.comp continuous_fst)).rexp) (fun p => (exp_pos _).ne')

lemma integral_stepWeight {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (a s x : ℝ) : (∫ z,stepWeight a s f (x,z) ∂gaussianReal 0 1)=1 := by
  simp only [stepWeight,integral_div]
  change expMass a s f x / exp (a*step a s f x)=1
  rw [←exp_step_all hf,div_self (exp_pos _).ne']

lemma stepJoint_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f) {a : ℝ} (ha : 0≤a) (s : ℝ) :
    IsProbabilityMeasure (stepJoint μ a s f) := by
  constructor
  rw [stepJoint,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [lintegral_prod _ ((continuous_stepWeight hf ha s).measurable.ennreal_ofReal.aemeasurable)]
  have he (x : ℝ) : (∫⁻ z, ENNReal.ofReal (stepWeight a s f (x,z)) ∂gaussianReal 0 1)=1 := by
    rw [←ofReal_integral_eq_lintegral_ofReal]
    · rw [integral_stepWeight hf,ENNReal.ofReal_one]
    · exact (integrable_exp_shift hf a x s).div_const (exp (a*step a s f x))
    · exact ae_of_all _ fun z => (stepWeight_pos a s f (x,z)).le
  simp only [he,lintegral_const,measure_univ,mul_one]

lemma integral_stepJoint {μ : Measure ℝ} [SFinite μ] {L : ℝ≥0} {f g : ℝ → ℝ}
    (hf : LipschitzWith L f) {a : ℝ} (ha : 0≤a) (s : ℝ)
    (hi : Integrable (fun p : ℝ × ℝ => g (p.1+s*p.2)) (stepJoint μ a s f)) :
    (∫ p,g (p.1+s*p.2) ∂stepJoint μ a s f)=∫ x,tiltedMean a s f g x ∂μ := by
  have hm := (continuous_stepWeight hf ha s).measurable.ennreal_ofReal
  have hb : ∀ᵐ p ∂μ.prod (gaussianReal 0 1), ENNReal.ofReal (stepWeight a s f p)<⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have hi' := (integrable_withDensity_iff_integrable_smul' hm hb).mp hi
  simp only [ENNReal.toReal_ofReal (stepWeight_pos a s f _).le,smul_eq_mul] at hi'
  rw [stepJoint,integral_withDensity_eq_integral_toReal_smul hm hb]
  simp only [ENNReal.toReal_ofReal (stepWeight_pos a s f _).le,smul_eq_mul]
  rw [integral_prod _ hi']
  congr 1
  funext x
  simp only [stepWeight,div_mul_eq_mul_div,integral_div,tiltedMean,expMoment,exp_step_all hf]

lemma integral_stepLaw {μ : Measure ℝ} [SFinite μ] {L : ℝ≥0} {f g : ℝ → ℝ}
    (hf : LipschitzWith L f) {a : ℝ} (ha : 0≤a) (s : ℝ) (hg : StronglyMeasurable g)
    (hi : Integrable g (stepLaw μ a s f)) :
    (∫ y,g y ∂stepLaw μ a s f)=∫ x,tiltedMean a s f g x ∂μ := by
  rw [stepLaw,integral_map_of_stronglyMeasurable (by fun_prop) hg]
  exact integral_stepJoint hf ha s (hi.comp_aemeasurable (by fun_prop))

lemma measure_eq_stepLaw {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f) {a : ℝ} (ha : 0≤a) (s : ℝ)
    (h : ∀ (g : ℝ → ℝ), Continuous g → ∀ R : ℝ≥0, (∀x,|g x|≤R) →
      (∫ y,g y ∂ν)=∫ x,tiltedMean a s f g x ∂μ) : ν=stepLaw μ a s f := by
  have := stepJoint_probability μ hf ha s
  have : IsProbabilityMeasure (stepLaw μ a s f) := by
    unfold stepLaw
    infer_instance
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  rw [h g g.continuous ‖g‖₊ (fun x => by simpa only [Real.norm_eq_abs, coe_nnnorm] using g.norm_coe_le_norm x)]
  symm
  exact integral_stepLaw hf ha s g.continuous.stronglyMeasurable (g.integrable (μ := stepLaw μ a s f))

end ParisiSpectral

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite.BoundedCoefficient
open ParisiPath ParisiSpectral
variable {β : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

lemma actual_plateau_transport (c : BoundedCoefficient β) (hβ : 0<β)
    (hW : IsBrownianReal W P) {a d α : ℝ≥0} (ha0 : a≠0) (had : a<d) (hd1 : d≤1)
    (hg : ∀ t∈Ico a d,c.val t=α) {g : ℝ → ℝ} (hgc : Continuous g)
    (R : ℝ≥0) (hR : ∀ x,|g x|≤R) :
    (∫ ω,g (solution (c.driftData hβ) (brownianPath W ω) ⟨d,d.coe_nonneg,by exact_mod_cast hd1⟩) ∂P)=
      ∫ ω,tiltedMean α (Real.sqrt (d-a)) (field β c.val d) g
        (solution (c.driftData hβ) (brownianPath W ω) ⟨a,a.coe_nonneg,by exact_mod_cast had.le.trans hd1⟩) ∂P := by
  let f := canonicalSmoothField β hβ c.mono c.bound d
  have hsum : (a:ℝ)+((d-a:ℝ≥0):ℝ)=d := by
    rw [NNReal.coe_sub had.le];ring
  have hb (t : ℝ) (ht : t∈Ioo (a:ℝ) d) (x : ℝ) :
      (c.driftData hβ).val t x=finiteTimeCoefficient [(α,d-a)] a t*(scheduleField f [(α,d-a)] a t).d1 x := by
    have ht0 : 0≤t := a.coe_nonneg.trans ht.1.le
    have hr : Real.toNNReal t ∈ Ico a d := by
      constructor
      · exact_mod_cast (show (a:ℝ)≤(Real.toNNReal t:ℝ) by rw [Real.coe_toNNReal _ ht0];exact ht.1.le)
      · exact_mod_cast (show (Real.toNNReal t:ℝ)<d by rw [Real.coe_toNNReal _ ht0];exact ht.2)
    simp only [driftData,drift,real,finiteTimeCoefficient,scheduleField,hsum,ite_eq_left ht.2,smoothEvolve]
    rw [hg _ hr,fieldGradient_on_plateau β hβ c.mono c.bound hd1 hg hr]
    simp only [fieldOnInterval,SmoothField.transform,f,canonicalSmoothField,Real.coe_toNNReal _ ht0]
  have hh := generalSchedule_actual_transport_between_continuous hW (c.driftData hβ)
    (c.drift_joint_ae_continuous hβ) f hgc R hR [(α,d-a)] a d ha0 had hd1
    (by simpa only [width,List.sum_cons,List.sum_nil,List.map_cons,List.map_nil,add_zero] using hsum) hb
  simpa only [linearEvolve,evolve,NNReal.coe_sub had.le,f,canonicalSmoothField] using hh

lemma actual_plateau_law (c : BoundedCoefficient β) (hβ : 0<β)
    (hW : IsBrownianReal W P) {a d α : ℝ≥0} (ha0 : a≠0) (had : a<d) (hd1 : d≤1)
    (hg : ∀ t∈Ico a d,c.val t=α) :
    P.map (fun ω => solution (c.driftData hβ) (brownianPath W ω)
      ⟨d,d.coe_nonneg,by exact_mod_cast hd1⟩)=
    stepLaw (P.map (fun ω => solution (c.driftData hβ) (brownianPath W ω)
      ⟨a,a.coe_nonneg,by exact_mod_cast had.le.trans hd1⟩)) α (Real.sqrt (d-a)) (field β c.val d) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  let X (t : Time) (ω : Ω) := solution (c.driftData hβ) (brownianPath W ω) t
  have hm (t : Time) : AEMeasurable (X t) P :=
    aemeasurable_solution_eval _ _ (brownianPath_aemeasurable_eval hW) t
  let ta : Time := ⟨a,a.coe_nonneg,by exact_mod_cast had.le.trans hd1⟩
  let td : Time := ⟨d,d.coe_nonneg,by exact_mod_cast hd1⟩
  change P.map (X td)=stepLaw (P.map (X ta)) α (Real.sqrt (d-a)) (field β c.val d)
  have : IsProbabilityMeasure (P.map (X ta)) := inferInstance
  have : IsProbabilityMeasure (P.map (X td)) := inferInstance
  apply measure_eq_stepLaw (field_lipschitz β hβ c.mono c.bound d) α.coe_nonneg
  intro g hgc R hR
  rw [integral_map (hm td) hgc.aestronglyMeasurable,
    integral_map (hm ta) (continuous_tiltedMean (field_lipschitz β hβ c.mono c.bound d)
      hgc hR _ _).aestronglyMeasurable]
  exact c.actual_plateau_transport hβ hW ha0 had hd1 hg hgc R hR

lemma actual_plateau_transport_integrable (c : BoundedCoefficient β) (hβ : 0<β)
    (hW : IsBrownianReal W P) {a d α : ℝ≥0} (ha0 : a≠0) (had : a<d) (hd1 : d≤1)
    (hg : ∀ t∈Ico a d,c.val t=α) {g : ℝ → ℝ} (hgc : Continuous g)
    (hi : Integrable (fun ω => g (solution (c.driftData hβ) (brownianPath W ω)
      ⟨d,d.coe_nonneg,by exact_mod_cast hd1⟩)) P) :
    (∫ ω,g (solution (c.driftData hβ) (brownianPath W ω) ⟨d,d.coe_nonneg,by exact_mod_cast hd1⟩) ∂P)=
      ∫ ω,tiltedMean α (Real.sqrt (d-a)) (field β c.val d) g
        (solution (c.driftData hβ) (brownianPath W ω) ⟨a,a.coe_nonneg,by exact_mod_cast had.le.trans hd1⟩) ∂P := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  let X (t : Time) (ω : Ω) := solution (c.driftData hβ) (brownianPath W ω) t
  have hm (t : Time) : AEMeasurable (X t) P :=
    aemeasurable_solution_eval _ _ (brownianPath_aemeasurable_eval hW) t
  let ta : Time := ⟨a,a.coe_nonneg,by exact_mod_cast had.le.trans hd1⟩
  let td : Time := ⟨d,d.coe_nonneg,by exact_mod_cast hd1⟩
  have : IsProbabilityMeasure (P.map (X ta)) := inferInstance
  have he : P.map (X td)=stepLaw (P.map (X ta)) α (Real.sqrt (d-a)) (field β c.val d) :=
    c.actual_plateau_law hβ hW ha0 had hd1 hg
  have hi' : Integrable g (P.map (X td)) :=
    (integrable_map_measure hgc.aestronglyMeasurable (hm td)).mpr hi
  change (∫ ω,g (X td ω) ∂P)=∫ ω,tiltedMean α (Real.sqrt (d-a)) (field β c.val d) g (X ta ω) ∂P
  rw [←integral_map (hm td) hgc.aestronglyMeasurable,he]
  rw [integral_stepLaw (field_lipschitz β hβ c.mono c.bound d) α.coe_nonneg _
    hgc.stronglyMeasurable (he ▸ hi')]
  have htc : StronglyMeasurable (tiltedMean α (Real.sqrt (d-a)) (field β c.val d) g) := by
    have hnum : Continuous (fun p : ℝ × ℝ => Real.exp ((α:ℝ)*field β c.val d (p.1+Real.sqrt (d-a)*p.2))*
        g (p.1+Real.sqrt (d-a)*p.2)) := by
      have hf := (field_lipschitz β hβ c.mono c.bound d).continuous
      exact ((continuous_const.mul (hf.comp (by fun_prop))).rexp).mul (hgc.comp (by fun_prop))
    have hden : Continuous (expMass α (Real.sqrt (d-a)) (field β c.val d)) := by
      have hf := (step_lipschitz (field_lipschitz β hβ c.mono c.bound d) α.coe_nonneg (Real.sqrt (d-a))).continuous
      have hh : Continuous (fun x => Real.exp ((α:ℝ)*step α (Real.sqrt (d-a)) (field β c.val d) x)) :=
        ((continuous_const (y := (α:ℝ))).mul hf).rexp
      simp_rw [exp_step_all (field_lipschitz β hβ c.mono c.bound d)] at hh
      exact hh
    exact hnum.stronglyMeasurable.integral_prod_right.div hden.stronglyMeasurable
  exact integral_map (hm ta) htc.aestronglyMeasurable

end ParisiFinite.BoundedCoefficient

end

end OAI
