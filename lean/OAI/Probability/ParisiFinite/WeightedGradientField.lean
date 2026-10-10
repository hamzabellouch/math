import Mathlib
import OAI.Probability.ParisiFinite.MeasurableStepParam

namespace OAI

/-! Weighted Gradient Field. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite
open ParisiPath
namespace ThirdJet
variable {f : SmoothField}

def weightedGradientField (j : ThirdJet f) (r : SmoothField) (R : ℝ≥0)
    (hr : ∀ x,|r.val x|≤R) : SmoothField where
  val := fun x => r.val x*f.d1 x
  d1 := fun x => r.d1 x*f.d1 x+r.val x*f.d2 x
  d2 := fun x => r.d2 x*f.d1 x+2*r.d1 x*f.d2 x+r.val x*j.d3 x
  hasD1 := fun x => (r.hasD1 x).mul (f.hasD2 x)
  hasD2 := fun x => by
    convert ((r.hasD2 x).mul (f.hasD2 x)).add ((r.hasD1 x).mul (j.hasD3 x)) using 1
    first | rfl | ring
  continuousD2 := ((r.continuousD2.mul f.continuousD1).add
    ((r.continuousD1.const_mul 2).mul f.continuousD2)).add (r.lipschitz.continuous.mul j.continuousD3)
  bound1 := r.bound1*f.bound1+R*f.bound2
  bound2 := r.bound2*f.bound1+2*r.bound1*f.bound2+R*j.bound3
  normD1 := fun x => by
    apply (abs_add_le _ _).trans
    simp only [abs_mul,NNReal.coe_add,NNReal.coe_mul]
    gcongr <;> first | exact r.normD1 x | exact f.normD1 x | exact hr x | exact f.normD2 x
  normD2 := fun x => by
    change _ ≤ (r.bound2:ℝ)*f.bound1+2*r.bound1*f.bound2+(R:ℝ)*j.bound3
    apply (abs_add_le _ _).trans
    apply add_le_add ((abs_add_le _ _).trans ?_) ?_
    · simp only [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
      gcongr <;> first | exact r.normD2 x | exact r.normD1 x | exact f.normD1 x | exact f.normD2 x
    · simp only [abs_mul]
      exact mul_le_mul (hr x) (j.normD3 x) (abs_nonneg _) R.coe_nonneg

def slabWeightedGradientTest (j : ThirdJet f) (r : SmoothField) (R : ℝ≥0)
    (hr : ∀ x,|r.val x|≤R) (a b : ℝ) : TimeQuadraticTest where
  val := fun t x => r.val x*(fieldOnInterval f a b t).d1 x
  d1 := fun t x => r.d1 x*(fieldOnInterval f a b t).d1 x+r.val x*(fieldOnInterval f a b t).d2 x
  d2 := fun t x => r.d2 x*(fieldOnInterval f a b t).d1 x+
    2*r.d1 x*(fieldOnInterval f a b t).d2 x+r.val x*j.slabD3 a b t x
  dt := fun t x => r.val x*j.gradientDt a b t x
  hasD1 := fun t => ((j.transform a (Real.sqrt (b-t))).weightedGradientField r R hr).hasD1
  hasD2 := fun t => ((j.transform a (Real.sqrt (b-t))).weightedGradientField r R hr).hasD2
  continuousD2 := fun t => ((j.transform a (Real.sqrt (b-t))).weightedGradientField r R hr).continuousD2
  c1 := ((j.transform a 0).weightedGradientField r R hr).bound1
  c2 := ((j.transform a 0).weightedGradientField r R hr).bound2
  ct := R*j.gradientTimeBound a
  bound1 := fun t x => by
    simpa only [Real.norm_eq_abs,fieldOnInterval,weightedGradientField,transform,SmoothField.transform]
      using ((j.transform a (Real.sqrt (b-t))).weightedGradientField r R hr).normD1 x
  bound2 := fun t x => by
    simpa only [Real.norm_eq_abs,fieldOnInterval,weightedGradientField,transform,SmoothField.transform,slabD3]
      using ((j.transform a (Real.sqrt (b-t))).weightedGradientField r R hr).normD2 x
  boundT := fun t x => by
    simp only [norm_mul,NNReal.coe_mul]
    exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hr x)
      (j.gradientDt_bound a b t x) (norm_nonneg _) R.coe_nonneg
  measT := (r.lipschitz.continuous.measurable.comp measurable_snd).mul (j.measurable_gradientDt a b)
  continuousT := fun t => r.lipschitz.continuous.mul (j.continuous_gradientDt a b t)
  jointD1 := ae_of_all _ fun _ _ _ =>
    (((r.continuousD1.comp continuous_snd).mul (continuous_fieldOnInterval_d1 f a b)).add
      ((r.lipschitz.continuous.comp continuous_snd).mul (continuous_fieldOnInterval_d2 f a b))).continuousAt
  jointD2 := ae_of_all _ fun _ _ _ =>
    ((((r.continuousD2.comp continuous_snd).mul (continuous_fieldOnInterval_d1 f a b)).add
      (((r.continuousD1.comp continuous_snd).const_mul 2).mul (continuous_fieldOnInterval_d2 f a b))).add
        ((r.lipschitz.continuous.comp continuous_snd).mul (j.continuous_slabD3 a b))).continuousAt
  integralT := fun u _ v _ x => by
    rw [intervalIntegral.integral_const_mul,j.gradient_integral_time]
    ring

end ThirdJet

structure ScheduleWeightedGradient (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (s : ℝ) (r : SmoothField) where
  test : TimeQuadraticTest
  val_eq : ∀ t x,test.val t x=r.val x*(finiteTimeField β hβ ls s t).d1 x
  cancel : ∀ t,s≤t → t<s+width ls → ∀ x z,
    test.dt t x+test.d1 t x*z+test.d2 t x/2=
      r.d2 x/2*(finiteTimeField β hβ ls s t).d1 x+
      r.d1 x*(finiteTimeField β hβ ls s t).d2 x+
      r.d1 x*(finiteTimeField β hβ ls s t).d1 x*z+
      r.val x*(finiteTimeField β hβ ls s t).d2 x*
        (z-finiteTimeCoefficient ls s t*(finiteTimeField β hβ ls s t).d1 x)

def scheduleWeightedGradient (β : ℝ≥0) (hβ : 0<β) (ls : Schedule)
    (s : ℝ) (hs : 0 ≤ s) (he : s+width ls≤1) (r : SmoothField) (R : ℝ≥0)
    (hr : ∀ x,|r.val x|≤R) : ScheduleWeightedGradient β hβ ls s r := by
  induction ls generalizing s with
  | nil =>
    refine ⟨((terminalThird β hβ).weightedGradientField r R hr).staticTimeTest,fun _ _ => rfl,?_⟩
    intro t ht ht' x z
    simp only [width,List.map_nil,List.sum_nil,add_zero] at ht'
    exact False.elim (not_lt_of_ge ht ht')
  | cons l ls ih =>
    rcases l with ⟨a,d⟩
    let c : ℝ := s+d
    have hc0 : 0≤c := add_nonneg hs d.coe_nonneg
    have hend : c+width ls≤1 := by dsimp only [c];rw [width_cons] at he;linarith
    have hc1 : c≤1 := by linarith [schedule_width_nonneg ls]
    let tail := ih c hc0 hend
    let slab := (recursionThird β hβ ls).slabWeightedGradientTest r R hr a c
    have hval : (fieldOnInterval (smoothRecursion β hβ ls) a c c).val=(finiteTimeField β hβ ls c c).val := by
      funext x
      rw [fieldOnInterval_right,finiteTimeField_start,smoothRecursion_val]
    have hmatch (x : ℝ) : slab.val c x=tail.test.val c x := by
      change r.val x*(fieldOnInterval (smoothRecursion β hβ ls) a c c).d1 x=tail.test.val c x
      rw [tail.val_eq,SmoothField.d1_eq_of_val_eq hval]
    refine ⟨slab.glue tail.test c ⟨hc0,hc1⟩ hmatch,?_,?_⟩
    · intro t x
      simp only [TimeQuadraticTest.glue,TimeQuadraticTest.splice,finiteTimeField,ThirdJet.slabWeightedGradientTest,slab,c]
      split_ifs
      · rfl
      · exact tail.val_eq t x
    · intro t ht ht' x z
      simp only [TimeQuadraticTest.glue,TimeQuadraticTest.splice,finiteTimeField,finiteTimeCoefficient,
        ThirdJet.slabWeightedGradientTest,slab,c]
      split_ifs with hcut
      · rw [ThirdJet.gradientDt,ite_eq_left hcut]
        ring
      · exact tail.cancel t (le_of_not_gt hcut) (by rw [width_cons] at ht';dsimp only [c];linarith) x z

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite
open ParisiPath
variable {K M : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

def finiteWeightedKernel (w : SmoothField) (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (b : Drift K M)
    (t x : ℝ) : ℝ :=
  w.d2 x/2*(finiteTimeField β hβ ls 0 t).d1 x+
    w.d1 x*(finiteTimeField β hβ ls 0 t).d2 x+
    w.d1 x*(finiteTimeField β hβ ls 0 t).d1 x*b.val t x+
    w.val x*(finiteTimeField β hβ ls 0 t).d2 x*
      (b.val t x-finiteTimeCoefficient ls 0 t*(finiteTimeField β hβ ls 0 t).d1 x)

lemma finiteWeightedKernel_bound (w : SmoothField) (R : ℝ≥0) (hR : ∀ x,|w.val x|≤R) (β : ℝ≥0) (hβ : 0<β) (ls : Schedule)
    (ha : ∀ l∈ls,l.1≤β) (b : Drift K M) (t x : ℝ) :
    ‖finiteWeightedKernel w β hβ ls b t x‖≤(w.bound2:ℝ)/2+w.bound1*(β:ℝ)+w.bound1*(M:ℝ)+(R:ℝ)*(β:ℝ)*((M:ℝ)+(β:ℝ)) := by
  have hm : |(finiteTimeField β hβ ls 0 t).d1 x|≤1 := by
    simpa only [(finiteTimeField_curvature β hβ ls ha 0 t).1,NNReal.coe_one] using
      (finiteTimeField β hβ ls 0 t).normD1 x
  have ha' := curvature_abs_d2 (finiteTimeField_curvature β hβ ls ha 0 t) x
  have hc := finiteTimeCoefficient_bound β ls ha 0 t
  have hbm : |b.val t x|≤(M:ℝ) := by simpa only [Real.norm_eq_abs] using b.bound t x
  have he : |b.val t x-finiteTimeCoefficient ls 0 t*(finiteTimeField β hβ ls 0 t).d1 x|≤(M:ℝ)+(β:ℝ) := by
    apply (abs_sub _ _).trans
    rw [abs_mul]
    exact add_le_add hbm ((mul_le_mul hc hm (abs_nonneg _) β.coe_nonneg).trans_eq (mul_one _))
  rw [finiteWeightedKernel,Real.norm_eq_abs]
  calc
    _ ≤ |w.d2 x/2*(finiteTimeField β hβ ls 0 t).d1 x|+
        |w.d1 x*(finiteTimeField β hβ ls 0 t).d2 x|+
        |w.d1 x*(finiteTimeField β hβ ls 0 t).d1 x*b.val t x|+
        |w.val x*(finiteTimeField β hβ ls 0 t).d2 x*
          (b.val t x-finiteTimeCoefficient ls 0 t*(finiteTimeField β hβ ls 0 t).d1 x)| := by
      exact (abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ (w.bound2:ℝ)/2*1+w.bound1*(β:ℝ)+w.bound1*1*(M:ℝ)+(R:ℝ)*(β:ℝ)*((M:ℝ)+(β:ℝ)) := by
      simp only [abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
      gcongr <;> first | exact w.normD2 x | exact w.normD1 x | exact hR x
    _ = _ := by ring

lemma finiteWeightedKernel_integrable (w : SmoothField) (R : ℝ≥0) (hR : ∀ x,|w.val x|≤R) (hW : IsBrownianReal W P)
    (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (ha : ∀ l∈ls,l.1≤β)
    (b : Drift K M) (t : ℝ) :
    Integrable (fun ω => finiteWeightedKernel w β hβ ls b t
      (extend (solution b (brownianPath W ω)) t)) P := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  refine Integrable.of_bound (C := (w.bound2:ℝ)/2+w.bound1*(β:ℝ)+w.bound1*(M:ℝ)+(R:ℝ)*(β:ℝ)*((M:ℝ)+(β:ℝ))) ?_ ?_
  · have hx := aemeasurable_solution_eval b (brownianPath W) (brownianPath_aemeasurable_eval hW)
      (projIcc 0 1 zero_le_one t)
    have h1 := (finiteTimeField β hβ ls 0 t).continuousD1
    have h2 := (finiteTimeField β hβ ls 0 t).continuousD2
    have hc : Continuous (finiteWeightedKernel w β hβ ls b t) := by
      unfold finiteWeightedKernel
      exact ((((w.continuousD2.div_const 2).mul h1).add
        (w.continuousD1.mul h2)).add ((w.continuousD1.mul h1).mul (b.lipschitz t).continuous)).add
          ((w.lipschitz.continuous.mul h2).mul ((b.lipschitz t).continuous.sub (continuous_const.mul h1)))
    exact hc.measurable.comp_aemeasurable hx |>.aestronglyMeasurable
  · exact ae_of_all _ fun ω => finiteWeightedKernel_bound w R hR β hβ ls ha b t _

lemma expected_finiteWeightedKernel_eq (w : SmoothField) (R : ℝ≥0) (hR : ∀ x,|w.val x|≤R) (hW : IsBrownianReal W P)
    (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (hw : width ls=1) (b : Drift K M)
    (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
    (∫ ω,finiteWeightedKernel w β hβ ls b t (extend (solution b (brownianPath W ω)) t) ∂P)=
      timeGeneratorC2 P W b (scheduleWeightedGradient β hβ ls 0 le_rfl (by rw [hw];norm_num) w R hR).test t+
      timeDerivativeC2 P W b (scheduleWeightedGradient β hβ ls 0 le_rfl (by rw [hw];norm_num) w R hR).test t := by
  let r := scheduleWeightedGradient β hβ ls 0 le_rfl (by rw [hw];norm_num) w R hR
  change _=(∫ ω,generatorC2 (r.test.slice t) b t (extend (solution b (brownianPath W ω)) t) ∂P)+
    (∫ ω,r.test.dt t (extend (solution b (brownianPath W ω)) t) ∂P)
  rw [←integral_add (generatorC2_integrable hW b _ t) (timeDerivativeC2_integrable_inner hW b r.test t)]
  apply integral_congr_ae
  filter_upwards [] with ω
  have hh := r.cancel t ht.1.le (by simpa only [hw,zero_add] using ht.2)
    (extend (solution b (brownianPath W ω)) t) (b.val t (extend (solution b (brownianPath W ω)) t))
  dsimp only [generatorC2,TimeQuadraticTest.slice,finiteWeightedKernel]
  linarith

lemma expected_finiteWeightedKernel_aestronglyMeasurable (w : SmoothField) (R : ℝ≥0) (hR : ∀ x,|w.val x|≤R) (hW : IsBrownianReal W P)
    (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (hw : width ls=1) (b : Drift K M)
    (hc : ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x)) :
    AEStronglyMeasurable (fun t => ∫ ω,finiteWeightedKernel w β hβ ls b t
      (extend (solution b (brownianPath W ω)) t) ∂P) (volume.restrict (Ioc (0:ℝ) 1)) := by
  let r := scheduleWeightedGradient β hβ ls 0 le_rfl (by rw [hw];norm_num) w R hR
  have hj := timeGeneratorC2_intervalIntegrable hW b r.test hc
  have ht := timeDerivativeC2_intervalIntegrable hW b r.test hc
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hj ht
  apply (hj.aestronglyMeasurable.add ht.aestronglyMeasurable).congr
  have hnot : ∀ᵐ t ∂volume,t≠(1:ℝ) := by simp [ae_iff,measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae hnot] with t hmem hn
  exact (expected_finiteWeightedKernel_eq w R hR hW β hβ ls hw b t ⟨hmem.1,hmem.2.lt_of_ne hn⟩).symm

lemma expected_finiteWeightedKernel_bound (w : SmoothField) (R : ℝ≥0) (hR : ∀ x,|w.val x|≤R) (hW : IsBrownianReal W P)
    (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (ha : ∀ l∈ls,l.1≤β) (b : Drift K M) (t : ℝ) :
    ‖∫ ω,finiteWeightedKernel w β hβ ls b t (extend (solution b (brownianPath W ω)) t) ∂P‖≤
      (w.bound2:ℝ)/2+w.bound1*(β:ℝ)+w.bound1*(M:ℝ)+(R:ℝ)*(β:ℝ)*((M:ℝ)+(β:ℝ)) := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact (norm_integral_le_of_norm_le_const (μ:=P) (ae_of_all P fun ω =>
    finiteWeightedKernel_bound w R hR β hβ ls ha b t _)).trans_eq (by simp)

 
theorem finite_schedule_weighted_verification (w : SmoothField) (R : ℝ≥0) (hR : ∀ x,|w.val x|≤R) (hW : IsBrownianReal W P)
    (b : Drift K M)
    (hc : ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x))
    (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (hw : width ls=1)
    (c : ℝ≥0) (hc0 : c≠0) (hc1 : c≤1) :
    (∫ ω,w.val (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc1⟩)*
      (finiteTimeField β hβ ls 0 c).d1
        (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc1⟩) ∂P)-
      w.val 0*(smoothRecursion β hβ ls).d1 0=
        ∫ t in (0:ℝ)..(c:ℝ),∫ ω,finiteWeightedKernel w β hβ ls b t
          (extend (solution b (brownianPath W ω)) t) ∂P := by
  let r := scheduleWeightedGradient β hβ ls 0 le_rfl (by rw [hw];norm_num) w R hR
  have hh := brownian_solution_time_generator_at hW b r.test c hc0 hc1 hc
  have hsub : uIcc (0:ℝ) c⊆uIcc (0:ℝ) 1 := by
    rw [uIcc_of_le c.coe_nonneg,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl (by exact_mod_cast hc1)
  have hj := (timeGeneratorC2_intervalIntegrable hW b r.test hc).mono_set hsub
  have ht := (timeDerivativeC2_intervalIntegrable hW b r.test hc).mono_set hsub
  simp_rw [r.val_eq,finiteTimeField_d1_start] at hh
  rw [hh,←intervalIntegral.integral_add hj ht]
  apply intervalIntegral.integral_congr_Ioo_of_le c.coe_nonneg
  intro t ht
  exact (expected_finiteWeightedKernel_eq w R hR hW β hβ ls hw b t
    ⟨ht.1,ht.2.trans_le (by exact_mod_cast hc1)⟩).symm

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite
open ParisiPath
variable {K M : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

def weightedKernel (w : SmoothField) (β : ℝ≥0) (γ : ℝ≥0 → ℝ≥0) (b : Drift K M) (t x : ℝ) : ℝ :=
  w.d2 x/2*fieldGradient β γ (Real.toNNReal t) x+
    w.d1 x*fieldCurvature β γ (Real.toNNReal t) x+
    w.d1 x*fieldGradient β γ (Real.toNNReal t) x*b.val t x+
    w.val x*fieldCurvature β γ (Real.toNNReal t) x*
      (b.val t x-(γ (Real.toNNReal t):ℝ)*fieldGradient β γ (Real.toNNReal t) x)

lemma global_dyadic_weightedKernel_tendsto (w : SmoothField) (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0}
    (hγ : Monotone γ) (hb : ∀ t,γ t≤β) (b : Drift K M) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1)
    (hc : Tendsto (fun n => finiteTimeCoefficient (dyadicSchedule γ false 0 1 n) 0 t)
      atTop (𝓝 (γ (Real.toNNReal t):ℝ))) (x : ℝ) :
    Tendsto (fun n => finiteWeightedKernel w β hβ (dyadicSchedule γ false 0 1 n) b t x)
      atTop (𝓝 (weightedKernel w β γ b t x)) := by
  have hr : Real.toNNReal t<1 := by
    exact_mod_cast (show (Real.toNNReal t:ℝ)<1 by rw [Real.coe_toNNReal _ ht.1.le];exact ht.2)
  have hg := (global_dyadic_gradient_tendstoUniformly β hβ hγ hb _ hr).tendsto_at x
  have ha := (global_dyadic_curvature_tendstoUniformly β hβ hγ hb _ hr).tendsto_at x
  rw [Real.coe_toNNReal _ ht.1.le] at hg ha
  exact (((hg.const_mul (w.d2 x/2)).add (ha.const_mul (w.d1 x))).add
    ((hg.const_mul (w.d1 x)).mul_const (b.val t x))).add
      ((ha.const_mul (w.val x)).mul (tendsto_const_nhds.sub (hc.mul hg)))

lemma expected_global_dyadic_weightedKernel_tendsto (w : SmoothField) (R : ℝ≥0) (hR : ∀ x,|w.val x|≤R) (hW : IsBrownianReal W P)
    (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t≤β)
    (b : Drift K M) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1)
    (hc : Tendsto (fun n => finiteTimeCoefficient (dyadicSchedule γ false 0 1 n) 0 t)
      atTop (𝓝 (γ (Real.toNNReal t):ℝ))) :
    Tendsto (fun n => ∫ ω,finiteWeightedKernel w β hβ (dyadicSchedule γ false 0 1 n) b t
      (extend (solution b (brownianPath W ω)) t) ∂P) atTop
      (𝓝 (∫ ω,weightedKernel w β γ b t (extend (solution b (brownianPath W ω)) t) ∂P)) := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  apply tendsto_integral_of_dominated_convergence
    (fun _ : Ω => (w.bound2:ℝ)/2+w.bound1*(β:ℝ)+w.bound1*(M:ℝ)+(R:ℝ)*(β:ℝ)*((M:ℝ)+(β:ℝ)))
    (fun n => (finiteWeightedKernel_integrable w R hR hW β hβ _ (dyadicSchedule_coeff_bound hb false 0 1 n) b t).aestronglyMeasurable)
    (integrable_const _) (fun n => ae_of_all _ fun ω =>
      finiteWeightedKernel_bound w R hR β hβ _ (dyadicSchedule_coeff_bound hb false 0 1 n) b t _)
  exact ae_of_all _ fun ω => global_dyadic_weightedKernel_tendsto w β hβ hγ hb b t ht hc _

lemma expected_global_dyadic_gradient_weighted_tendsto (w : SmoothField) (R : ℝ≥0) (hR : ∀ x,|w.val x|≤R) (hW : IsBrownianReal W P)
    (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t≤β)
    (b : Drift K M) (c : ℝ≥0) (hc : c<1) :
    Tendsto (fun n => ∫ ω,w.val (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc.le⟩)*
      (finiteTimeField β hβ (dyadicSchedule γ false 0 1 n) 0 c).d1
        (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc.le⟩) ∂P) atTop
      (𝓝 (∫ ω,w.val (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc.le⟩)*fieldGradient β γ c
        (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc.le⟩) ∂P)) := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hx := aemeasurable_solution_eval b (brownianPath W) (brownianPath_aemeasurable_eval hW)
    ⟨c,c.coe_nonneg,by exact_mod_cast hc.le⟩
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (R:ℝ))
  · intro n
    exact ((w.lipschitz.continuous.mul (finiteTimeField β hβ _ 0 c).continuousD1).measurable.comp_aemeasurable hx).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [] with ω
    rw [Real.norm_eq_abs,abs_mul]
    have hh := (finiteTimeField β hβ (dyadicSchedule γ false 0 1 n) 0 c).normD1
      (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc.le⟩)
    have hh' : |(finiteTimeField β hβ (dyadicSchedule γ false 0 1 n) 0 c).d1
        (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc.le⟩)|≤1 := by
      simpa only [(finiteTimeField_curvature β hβ _ (dyadicSchedule_coeff_bound hb false 0 1 n) 0 c).1,NNReal.coe_one] using hh
    exact (mul_le_mul (hR _) hh' (abs_nonneg _) R.coe_nonneg).trans_eq (mul_one _)
  · exact ae_of_all _ fun ω => ((global_dyadic_gradient_tendstoUniformly β hβ hγ hb c hc).tendsto_at _).const_mul _

 

theorem canonical_weighted_verification (w : SmoothField) (R : ℝ≥0) (hR : ∀ x,|w.val x|≤R) (hW : IsBrownianReal W P) (b : Drift K M)
    (hc : ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x))
    (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t≤β)
    (c : ℝ≥0) (hc0 : c≠0) (hc1 : c<1) :
    (∫ ω,w.val (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc1.le⟩)*
      fieldGradient β γ c (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc1.le⟩) ∂P)-
      w.val 0*fieldGradient β γ 0 0=
        ∫ t in (0:ℝ)..(c:ℝ),∫ ω,weightedKernel w β γ b t
          (extend (solution b (brownianPath W ω)) t) ∂P := by
  have hsub : Ioc (0:ℝ) c⊆Ioc (0:ℝ) 1 := Ioc_subset_Ioc le_rfl (by exact_mod_cast hc1.le)
  have hi : Tendsto (fun n => ∫ t in (0:ℝ)..(c:ℝ),∫ ω,
      finiteWeightedKernel w β hβ (dyadicSchedule γ false 0 1 n) b t
        (extend (solution b (brownianPath W ω)) t) ∂P) atTop
      (𝓝 (∫ t in (0:ℝ)..(c:ℝ),∫ ω,weightedKernel w β γ b t
        (extend (solution b (brownianPath W ω)) t) ∂P)) := by
    have hmeas (n : ℕ) : AEStronglyMeasurable
        (fun t => ∫ ω,finiteWeightedKernel w β hβ (dyadicSchedule γ false 0 1 n) b t
          (extend (solution b (brownianPath W ω)) t) ∂P) (volume.restrict (uIoc (0:ℝ) c)) := by
      rw [uIoc_of_le c.coe_nonneg]
      exact (expected_finiteWeightedKernel_aestronglyMeasurable w R hR hW β hβ _
        (by simpa only [NNReal.coe_one] using dyadicSchedule_width γ false 0 1 n) b hc).mono_measure
          (Measure.restrict_mono_set _ hsub)
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => (w.bound2:ℝ)/2+w.bound1*(β:ℝ)+w.bound1*(M:ℝ)+(R:ℝ)*(β:ℝ)*((M:ℝ)+(β:ℝ))) (Eventually.of_forall hmeas)
      (Eventually.of_forall fun n => ae_of_all _ fun t _ =>
        expected_finiteWeightedKernel_bound w R hR hW β hβ _ (dyadicSchedule_coeff_bound hb false 0 1 n) b t)
      intervalIntegrable_const
    filter_upwards [global_dyadic_coefficient_tendsto_ae hγ] with t ht hmem
    rw [uIoc_of_le c.coe_nonneg] at hmem
    have hti : t∈Ioo (0:ℝ) 1 := ⟨hmem.1,hmem.2.trans_lt (by exact_mod_cast hc1)⟩
    exact expected_global_dyadic_weightedKernel_tendsto w R hR hW β hβ hγ hb b t hti (ht hti)
  have h0 : Tendsto (fun n => w.val 0*(smoothRecursion β hβ (dyadicSchedule γ false 0 1 n)).d1 0)
      atTop (𝓝 (w.val 0*fieldGradient β γ 0 0)) := by
    have hh := ((global_dyadic_gradient_tendstoUniformly β hβ hγ hb 0 (by norm_num)).tendsto_at 0).const_mul (w.val 0)
    simpa only [NNReal.coe_zero,finiteTimeField_d1_start] using hh
  have he : (fun n => (∫ ω,w.val (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc1.le⟩)*
      (finiteTimeField β hβ (dyadicSchedule γ false 0 1 n) 0 c).d1
        (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc1.le⟩) ∂P)-
      w.val 0*(smoothRecursion β hβ (dyadicSchedule γ false 0 1 n)).d1 0)=
    (fun n => ∫ t in (0:ℝ)..(c:ℝ),∫ ω,finiteWeightedKernel w β hβ (dyadicSchedule γ false 0 1 n) b t
      (extend (solution b (brownianPath W ω)) t) ∂P) := by
    funext n
    exact finite_schedule_weighted_verification w R hR hW b hc β hβ _
      (by simpa only [NNReal.coe_one] using dyadicSchedule_width γ false 0 1 n) c hc0 hc1.le
  exact tendsto_nhds_unique
    ((expected_global_dyadic_gradient_weighted_tendsto w R hR hW β hβ hγ hb b c hc1).sub h0) (he ▸ hi)

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite

def sineWeight (L : ℝ≥0) (hL : 0<L) : SmoothField where
  val := fun x => (L:ℝ)*Real.sin (x/L)
  d1 := fun x => Real.cos (x/L)
  d2 := fun x => -Real.sin (x/L)/L
  hasD1 := fun x => by
    have hp : (L:ℝ)≠0 := by exact_mod_cast hL.ne'
    convert (((hasDerivAt_id x).div_const (L:ℝ)).sin).const_mul (L:ℝ) using 1 <;> first | rfl | simp [id_eq,div_eq_mul_inv,mul_comm,hp]
  hasD2 := fun x => by
    convert ((hasDerivAt_id x).div_const (L:ℝ)).cos using 1 <;> simp [div_eq_mul_inv]
  continuousD2 := by fun_prop
  bound1 := 1
  bound2 := 1/L
  normD1 := fun x => by simpa only [NNReal.coe_one] using Real.abs_cos_le_one (x/L)
  normD2 := fun x => by
    simp only [abs_div,abs_neg,abs_of_nonneg L.coe_nonneg,NNReal.coe_div,NNReal.coe_one]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) L.coe_nonneg

lemma sineWeight_bound (L : ℝ≥0) (hL : 0<L) (x : ℝ) :
    |(sineWeight L hL).val x|≤L := by
  change |(L:ℝ)*Real.sin (x/L)|≤L
  rw [abs_mul,abs_of_nonneg L.coe_nonneg]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) L.coe_nonneg

lemma sineWeight_zero (L : ℝ≥0) (hL : 0<L) : (sineWeight L hL).val 0=0 := by simp [sineWeight]
lemma sineWeight_bound_abs (L : ℝ≥0) (hL : 0<L) (x : ℝ) :
    |(sineWeight L hL).val x|≤|x| := by
  have hh := (sineWeight L hL).lipschitz.norm_sub_le x 0
  simpa only [sineWeight_zero,sub_zero,Real.norm_eq_abs,sineWeight,NNReal.coe_one,one_mul,zero_div,Real.sin_zero,mul_zero,sub_zero] using hh

lemma sineWeight_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => (sineWeight (n+1) (by positivity)).val x) atTop (𝓝 x) := by
  have h : Tendsto (fun n : ℕ => x/((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,one_div,one_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul x
  have hh := (Real.continuous_sinc.tendsto 0).comp h
  simp only [Real.sinc_zero] at hh
  have he (n : ℕ) : (sineWeight (n+1) (by positivity)).val x=x*Real.sinc (x/((n:ℝ)+1)) := by
    by_cases hx : x=0
    · simp [hx,sineWeight]
    · have hn : (n:ℝ)+1≠0 := by positivity
      simp only [sineWeight,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one,
        Real.sinc_of_ne_zero (div_ne_zero hx hn)]
      field_simp
  simp_rw [he]
  simpa only [mul_one,Function.comp_def] using hh.const_mul x

lemma sineWeight_d1_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => (sineWeight (n+1) (by positivity)).d1 x) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => x/((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,one_div,one_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul x
  simpa only [sineWeight,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one,Real.cos_zero,Function.comp_def]
    using (Real.continuous_cos.tendsto 0).comp h

lemma sineWeight_d2_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => (sineWeight (n+1) (by positivity)).d2 x) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => x/((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,one_div,one_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul x
  have hh := (((Real.continuous_sin.tendsto 0).comp h).neg).mul
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
  simpa only [sineWeight,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one,Real.sin_zero,neg_zero,mul_zero,
    one_div,div_eq_mul_inv,one_mul,Function.comp_def] using hh

lemma sineWeight_bound2_le (n : ℕ) : ((sineWeight (n+1) (by positivity)).bound2:ℝ)≤1 := by
  simp only [sineWeight,NNReal.coe_div,NNReal.coe_one,NNReal.coe_add,NNReal.coe_natCast]
  exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) n])

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite
open ParisiPath
variable {K M : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

lemma expected_weightedKernel_aestronglyMeasurable (w : SmoothField) (R : ℝ≥0) (hR : ∀ x,|w.val x|≤R)
    (hW : IsBrownianReal W P) (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0}
    (hγ : Monotone γ) (hb : ∀ t,γ t≤β) (b : Drift K M)
    (hc : ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x)) :
    AEStronglyMeasurable (fun t => ∫ ω,weightedKernel w β γ b t
      (extend (solution b (brownianPath W ω)) t) ∂P) (volume.restrict (Ioc (0:ℝ) 1)) := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => expected_finiteWeightedKernel_aestronglyMeasurable w R hR hW β hβ _
      (by simpa only [NNReal.coe_one] using dyadicSchedule_width γ false 0 1 n) b hc)
  have hn : ∀ᵐ t ∂volume,t≠(1:ℝ) := by simp [ae_iff,measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae hn,
    ae_restrict_of_ae (global_dyadic_coefficient_tendsto_ae hγ)] with t ht hn hc
  have hti : t∈Ioo (0:ℝ) 1 := ⟨ht.1,ht.2.lt_of_ne hn⟩
  exact expected_global_dyadic_weightedKernel_tendsto w R hR hW β hβ hγ hb b t hti (hc hti)

namespace BoundedCoefficient
variable {β : ℝ≥0}

def weightedFeedback (c : BoundedCoefficient β) (w : SmoothField) (t x : ℝ) : ℝ :=
  w.d2 x/2*fieldGradient β c.val (Real.toNNReal t) x+
    w.d1 x*fieldCurvature β c.val (Real.toNNReal t) x+
    c.real t*w.d1 x*(fieldGradient β c.val (Real.toNNReal t) x)^2

lemma weightedKernel_feedback (c : BoundedCoefficient β) (hβ : 0<β) (w : SmoothField) (t x : ℝ) :
    weightedKernel w β c.val (c.driftData hβ) t x=c.weightedFeedback w t x := by
  simp only [weightedKernel,weightedFeedback,driftData,drift,BoundedCoefficient.real]
  ring

lemma weightedFeedback_bound (c : BoundedCoefficient β) (hβ : 0<β) (w : SmoothField)
    (h1 : ∀ x,|w.d1 x|≤1) (h2 : ∀ x,|w.d2 x|≤1) (t x : ℝ) :
    ‖c.weightedFeedback w t x‖≤1/2+2*(β:ℝ) := by
  have hm := fieldGradient_bound β hβ c.mono c.bound (Real.toNNReal t) x
  have ha := fieldCurvature_abs β hβ c.mono c.bound (Real.toNNReal t) x
  have hc : |c.real t|≤β := by rw [abs_of_nonneg (c.real_nonneg t)];exact c.real_le t
  change |w.d2 x/2*fieldGradient β c.val (Real.toNNReal t) x+
    w.d1 x*fieldCurvature β c.val (Real.toNNReal t) x+
    c.real t*w.d1 x*(fieldGradient β c.val (Real.toNNReal t) x)^2|≤_
  have hA : |w.d2 x/2*fieldGradient β c.val (Real.toNNReal t) x|≤1/2 := by
    rw [abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    calc
      _ ≤ 1/2*1 := mul_le_mul (div_le_div_of_nonneg_right (h2 x) (by norm_num)) hm
        (abs_nonneg _) (by norm_num)
      _ = _ := mul_one _
  have hB : |w.d1 x*fieldCurvature β c.val (Real.toNNReal t) x|≤β := by
    rw [abs_mul]
    exact (mul_le_mul (h1 x) ha (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hC : |c.real t*w.d1 x*(fieldGradient β c.val (Real.toNNReal t) x)^2|≤β := by
    rw [abs_mul,abs_mul,abs_pow]
    exact (mul_le_mul (mul_le_mul hc (h1 x) (abs_nonneg _) β.coe_nonneg)
      (pow_le_pow_left₀ (abs_nonneg _) hm 2) (by positivity) (by positivity)).trans_eq (by ring)
  have hh := (abs_add_three (w.d2 x/2*fieldGradient β c.val (Real.toNNReal t) x)
    (w.d1 x*fieldCurvature β c.val (Real.toNNReal t) x)
    (c.real t*w.d1 x*(fieldGradient β c.val (Real.toNNReal t) x)^2)).trans
      (add_le_add (add_le_add hA hB) hC)
  linarith

lemma weightedFeedback_integrable (hW : IsBrownianReal W P) (c : BoundedCoefficient β) (hβ : 0<β)
    (w : SmoothField) (h1 : ∀ x,|w.d1 x|≤1) (h2 : ∀ x,|w.d2 x|≤1) (t : ℝ) :
    Integrable (fun ω => c.weightedFeedback w t
      (extend (solution (c.driftData hβ) (brownianPath W ω)) t)) P := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hx := aemeasurable_solution_eval (c.driftData hβ) (brownianPath W) (brownianPath_aemeasurable_eval hW)
    (projIcc 0 1 zero_le_one t)
  have hm := (fieldGradient_lipschitz β hβ c.mono c.bound (Real.toNNReal t)).continuous
  have ha := (fieldCurvature_lipschitz β hβ c.mono c.bound (Real.toNNReal t)).continuous
  have hh : Continuous (c.weightedFeedback w t) :=
    (((w.continuousD2.div_const 2).mul hm).add (w.continuousD1.mul ha)).add
      ((continuous_const.mul w.continuousD1).mul (hm.pow 2))
  exact Integrable.of_bound (hh.measurable.comp_aemeasurable hx).aestronglyMeasurable _
    (ae_of_all _ fun ω => c.weightedFeedback_bound hβ w h1 h2 t _)

lemma expected_feedback_sine_tendsto (hW : IsBrownianReal W P) (c : BoundedCoefficient β) (hβ : 0<β) (t : ℝ) :
    Tendsto (fun n : ℕ => ∫ ω,c.weightedFeedback (sineWeight (n+1) (by positivity)) t
      (extend (solution (c.driftData hβ) (brownianPath W ω)) t) ∂P) atTop
    (𝓝 (∫ ω,fieldCurvature β c.val (Real.toNNReal t)
      (extend (solution (c.driftData hβ) (brownianPath W ω)) t)+c.real t*
        (fieldGradient β c.val (Real.toNNReal t) (extend (solution (c.driftData hβ) (brownianPath W ω)) t))^2 ∂P)) := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hb1 (n : ℕ) (x : ℝ) : |(sineWeight (n+1) (by positivity)).d1 x|≤1 :=
    Real.abs_cos_le_one _
  have hb2 (n : ℕ) (x : ℝ) : |(sineWeight (n+1) (by positivity)).d2 x|≤1 :=
    ((sineWeight (n+1) (by positivity)).normD2 x).trans (sineWeight_bound2_le n)
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => 1/2+2*(β:ℝ))
    (fun n => (c.weightedFeedback_integrable hW hβ _ (hb1 n) (hb2 n) t).aestronglyMeasurable)
    (integrable_const _) (fun n => ae_of_all _ fun ω => c.weightedFeedback_bound hβ _ (hb1 n) (hb2 n) t _)
  filter_upwards [] with ω
  let x := extend (solution (c.driftData hβ) (brownianPath W ω)) t
  have hh := (((sineWeight_d2_tendsto x).div_const 2).mul_const (fieldGradient β c.val (Real.toNNReal t) x)).add
    ((sineWeight_d1_tendsto x).mul_const (fieldCurvature β c.val (Real.toNNReal t) x))
  have hh' := hh.add (((sineWeight_d1_tendsto x).const_mul (c.real t)).mul_const
    ((fieldGradient β c.val (Real.toNNReal t) x)^2))
  simpa only [weightedFeedback,x,zero_div,zero_mul,one_mul,mul_one,zero_add] using hh'

theorem position_spin_raw (hW : IsBrownianReal W P) (c : BoundedCoefficient β) (hβ : 0<β)
    (q : ℝ≥0) (hq0 : q≠0) (hq1 : q<1) :
    (∫ ω,(solution (c.driftData hβ) (brownianPath W ω) ⟨q,q.coe_nonneg,by exact_mod_cast hq1.le⟩)*
      fieldGradient β c.val q (solution (c.driftData hβ) (brownianPath W ω) ⟨q,q.coe_nonneg,by exact_mod_cast hq1.le⟩) ∂P)=
      ∫ t in (0:ℝ)..(q:ℝ),∫ ω,fieldCurvature β c.val (Real.toNNReal t)
        (extend (solution (c.driftData hβ) (brownianPath W ω)) t)+c.real t*
          (fieldGradient β c.val (Real.toNNReal t) (extend (solution (c.driftData hβ) (brownianPath W ω)) t))^2 ∂P := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  let X (ω : Ω) := solution (c.driftData hβ) (brownianPath W ω)
  let Q : Icc (0:ℝ) 1 := ⟨q,q.coe_nonneg,by exact_mod_cast hq1.le⟩
  let wn (n : ℕ) := sineWeight (n+1) (by positivity)
  have hb1 (n : ℕ) (x : ℝ) : |(wn n).d1 x|≤1 := Real.abs_cos_le_one _
  have hb2 (n : ℕ) (x : ℝ) : |(wn n).d2 x|≤1 :=
    ((wn n).normD2 x).trans (sineWeight_bound2_le n)
  have hx : Integrable (fun ω => X ω Q) P := brownian_solution_integrable hW _ Q
  have hleft : Tendsto (fun n => ∫ ω,(wn n).val (X ω Q)*fieldGradient β c.val q (X ω Q) ∂P) atTop
      (𝓝 (∫ ω,(X ω Q)*fieldGradient β c.val q (X ω Q) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun ω => ‖X ω Q‖)
      (fun n => (((wn n).lipschitz.continuous.mul (fieldGradient_lipschitz β hβ c.mono c.bound q).continuous).measurable.comp_aemeasurable hx.aemeasurable).aestronglyMeasurable)
      hx.norm
    · intro n
      filter_upwards [] with ω
      change ‖(wn n).val (X ω Q)*fieldGradient β c.val q (X ω Q)‖≤‖X ω Q‖
      rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,Real.norm_eq_abs]
      exact (mul_le_mul (sineWeight_bound_abs _ _ _) (fieldGradient_bound β hβ c.mono c.bound q _)
        (abs_nonneg _) (abs_nonneg _)).trans_eq (mul_one _)
    · exact ae_of_all _ fun ω => (sineWeight_tendsto (X ω Q)).mul_const _
  have hsub : Ioc (0:ℝ) q⊆Ioc (0:ℝ) 1 := Ioc_subset_Ioc le_rfl (by exact_mod_cast hq1.le)
  have hright : Tendsto (fun n => ∫ t in (0:ℝ)..(q:ℝ),∫ ω,c.weightedFeedback (wn n) t (extend (X ω) t) ∂P) atTop
      (𝓝 (∫ t in (0:ℝ)..(q:ℝ),∫ ω,fieldCurvature β c.val (Real.toNNReal t) (extend (X ω) t)+
        c.real t*(fieldGradient β c.val (Real.toNNReal t) (extend (X ω) t))^2 ∂P)) := by
    have hmeas (n : ℕ) : AEStronglyMeasurable (fun t => ∫ ω,c.weightedFeedback (wn n) t (extend (X ω) t) ∂P)
        (volume.restrict (uIoc (0:ℝ) q)) := by
      have hh := expected_weightedKernel_aestronglyMeasurable (wn n) (n+1) (sineWeight_bound _ _)
        hW β hβ c.mono c.bound (c.driftData hβ) (c.drift_joint_ae_continuous hβ)
      simp_rw [c.weightedKernel_feedback hβ] at hh
      rw [uIoc_of_le q.coe_nonneg]
      exact hh.mono_measure (Measure.restrict_mono_set _ hsub)
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => 1/2+2*(β:ℝ)) (Eventually.of_forall hmeas)
      (Eventually.of_forall fun n => ae_of_all _ fun t _ => ?_) intervalIntegrable_const
      (ae_of_all _ fun t _ => c.expected_feedback_sine_tendsto hW hβ t)
    exact (norm_integral_le_of_norm_le_const (μ:=P) (ae_of_all P fun ω =>
      c.weightedFeedback_bound hβ (wn n) (hb1 n) (hb2 n) t _)).trans_eq (by simp)
  have he : (fun n => ∫ ω,(wn n).val (X ω Q)*fieldGradient β c.val q (X ω Q) ∂P)=
      (fun n => ∫ t in (0:ℝ)..(q:ℝ),∫ ω,c.weightedFeedback (wn n) t (extend (X ω) t) ∂P) := by
    funext n
    have hh := canonical_weighted_verification (wn n) (n+1) (sineWeight_bound _ _) hW (c.driftData hβ)
      (c.drift_joint_ae_continuous hβ) β hβ c.mono c.bound q hq0 hq1
    simp_rw [c.weightedKernel_feedback hβ] at hh
    simpa only [wn,sineWeight_zero,zero_mul,sub_zero] using hh
  exact tendsto_nhds_unique hleft (he ▸ hright)

end BoundedCoefficient
end ParisiFinite

end

end OAI
