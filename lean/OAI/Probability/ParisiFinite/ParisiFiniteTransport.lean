import Mathlib
import OAI.Probability.ParisiFinite.MeasureCoefficientOnSupportGap

namespace OAI

/-! Parisi Finite Transport. -/

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

 

def smoothEvolve (f : SmoothField) : Schedule → SmoothField
  | [] => f
  | (a,d)::ls => (smoothEvolve f ls).transform a (Real.sqrt d)

lemma smoothEvolve_val (f : SmoothField) (ls : Schedule) :
    (smoothEvolve f ls).val = evolve ls f.val := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp only [smoothEvolve, SmoothField.transform, evolve, ih]

def scheduleField (f : SmoothField) : Schedule → ℝ → ℝ → SmoothField
  | [],_,_ => f
  | (a,d)::ls,s,t => if t<s+d then
      fieldOnInterval (smoothEvolve f ls) a (s+d) t
    else scheduleField f ls (s+d) t

def scheduleDerivative (f : SmoothField) : Schedule → ℝ → ℝ → ℝ → ℝ
  | [],_,_,_ => 0
  | (a,d)::ls,s,t,x => if t<s+d then
      fieldOnInterval_dt (smoothEvolve f ls) a (s+d) t x
    else scheduleDerivative f ls (s+d) t x

lemma scheduleField_start (f : SmoothField) (ls : Schedule) (s x : ℝ) :
    (scheduleField f ls s s).val x=(smoothEvolve f ls).val x := by
  induction ls generalizing s with
  | nil => rfl
  | cons l ls ih =>
    rcases l with ⟨a,d⟩
    by_cases hd : d=0
    · simp only [hd,NNReal.coe_zero,add_zero,scheduleField,lt_self_iff_false,ite_false,
        ih,smoothEvolve,Real.sqrt_zero,SmoothField.transform,step_zero_width]
    · have hp : (0:ℝ)<d := by exact_mod_cast pos_of_ne_zero hd
      rw [scheduleField,ite_eq_left (by linarith : s<s+(d:ℝ))]
      change step a (Real.sqrt (s+d-s)) (smoothEvolve f ls).val x=(smoothEvolve f ((a,d)::ls)).val x
      rw [add_sub_cancel_left]
      rfl

lemma scheduleField_after (f : SmoothField) (ls : Schedule) (s t x : ℝ)
    (ht : s+width ls≤t) : (scheduleField f ls s t).val x=f.val x := by
  induction ls generalizing s with
  | nil => rfl
  | cons l ls ih =>
    rcases l with ⟨a,d⟩
    rw [width_cons] at ht
    rw [scheduleField,ite_eq_right (by linarith [schedule_width_nonneg ls] : ¬ t<s+(d:ℝ))]
    apply ih
    linarith

lemma scheduleField_PDE (f : SmoothField) (ls : Schedule) (s t x : ℝ)
    (hs : s≤t) (ht : t<s+width ls) :
    scheduleDerivative f ls s t x=-(1/2:ℝ)*((scheduleField f ls s t).d2 x+
      finiteTimeCoefficient ls s t*((scheduleField f ls s t).d1 x)^2) := by
  induction ls generalizing s with
  | nil =>
    simp only [width,List.map_nil,List.sum_nil,add_zero] at ht
    exact False.elim (not_lt_of_ge hs ht)
  | cons l ls ih =>
    rcases l with ⟨a,d⟩
    simp only [scheduleDerivative,scheduleField,finiteTimeCoefficient]
    split_ifs with hcut
    · exact ite_eq_left hcut
    · apply ih (s+d) (le_of_not_gt hcut)
      rw [width_cons] at ht
      linarith

 

structure GeneralScheduleTimeRealization (f : SmoothField) (ls : Schedule) (s : ℝ) where
  test : TimeQuadraticTest
  val_eq : ∀ t x,test.val t x=(scheduleField f ls s t).val x
  d1_eq : ∀ t x,test.d1 t x=(scheduleField f ls s t).d1 x
  d2_eq : ∀ t x,test.d2 t x=(scheduleField f ls s t).d2 x
  dt_eq : ∀ t x,test.dt t x=scheduleDerivative f ls s t x

 

def generalScheduleTimeRealization (f : SmoothField) (ls : Schedule)
    (s : ℝ) (hs : 0 ≤ s) (he : s + width ls ≤ 1) : GeneralScheduleTimeRealization f ls s := by
  induction ls generalizing s with
  | nil =>
    exact ⟨(f).staticTimeTest,fun _ _ => rfl,
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
    let slab := (smoothEvolve f ls).slabTimeTest a c
    have hmatch (x : ℝ) : slab.val c x=tail.test.val c x := by
      change (fieldOnInterval (smoothEvolve f ls) a c c).val x=tail.test.val c x
      rw [fieldOnInterval_right,tail.val_eq,scheduleField_start,smoothEvolve_val]
    refine ⟨slab.glue tail.test c ⟨hc0,hc1⟩ hmatch,?_,?_,?_,?_⟩
    · intro t x
      simp only [TimeQuadraticTest.glue,TimeQuadraticTest.splice,scheduleField,
        SmoothField.slabTimeTest,slab,c]
      split_ifs
      · rfl
      · exact tail.val_eq t x
    · intro t x
      simp only [TimeQuadraticTest.glue,TimeQuadraticTest.splice,scheduleField,
        SmoothField.slabTimeTest,slab,c]
      split_ifs
      · rfl
      · exact tail.d1_eq t x
    · intro t x
      simp only [TimeQuadraticTest.glue,TimeQuadraticTest.splice,scheduleField,
        SmoothField.slabTimeTest,slab,c]
      split_ifs
      · rfl
      · exact tail.d2_eq t x
    · intro t x
      simp only [TimeQuadraticTest.glue,TimeQuadraticTest.splice,scheduleDerivative,
        SmoothField.slabTimeTest,slab,c]
      split_ifs
      · rfl
      · exact tail.dt_eq t x

variable {K M : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

lemma generalSchedule_verification (hW : IsBrownianReal W P)
    (b : Drift K M)
    (hc : ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x))
    (f : SmoothField) (ls : Schedule) (c : ℝ≥0) (hc0 : c≠0) (hc1 : c≤1)
    (hw : width ls=c) :
    (∫ ω,f.val (solution b (brownianPath W ω)
      ⟨c,by exact ⟨c.coe_nonneg,by exact_mod_cast hc1⟩⟩) ∂P)-(smoothEvolve f ls).val 0 =
      ∫ t in (0:ℝ)..(c:ℝ),∫ ω,
        (scheduleField f ls 0 t).d1 (extend (solution b (brownianPath W ω)) t)*
          b.val t (extend (solution b (brownianPath W ω)) t)-
        finiteTimeCoefficient ls 0 t/2*
          ((scheduleField f ls 0 t).d1 (extend (solution b (brownianPath W ω)) t))^2 ∂P := by
  let r := generalScheduleTimeRealization f ls 0 le_rfl (by rw [hw,zero_add];exact_mod_cast hc1)
  have hh := brownian_solution_time_generator_at hW b r.test c hc0 hc1 hc
  have hsub : uIcc (0:ℝ) c⊆uIcc (0:ℝ) 1 := by
    rw [uIcc_of_le c.coe_nonneg,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl (by exact_mod_cast hc1)
  have hj := (timeGeneratorC2_intervalIntegrable hW b r.test hc).mono_set hsub
  have ht := (timeDerivativeC2_intervalIntegrable hW b r.test hc).mono_set hsub
  have h1 (x : ℝ) : r.test.val c x=f.val x := by
    rw [r.val_eq,scheduleField_after f ls 0 c x (by rw [hw,zero_add])]
  have h0 : r.test.val 0 0=(smoothEvolve f ls).val 0 := by rw [r.val_eq,scheduleField_start]
  simp_rw [h1,h0] at hh
  rw [hh,←intervalIntegral.integral_add hj ht]
  apply intervalIntegral.integral_congr_Ioo_of_le c.coe_nonneg
  intro t ht
  change (∫ ω,generatorC2 (r.test.slice t) b t (extend (solution b (brownianPath W ω)) t) ∂P)+
    (∫ ω,r.test.dt t (extend (solution b (brownianPath W ω)) t) ∂P)=_
  rw [←integral_add (generatorC2_integrable hW b _ t) (timeDerivativeC2_integrable_inner hW b r.test t)]
  apply integral_congr_ae
  filter_upwards [] with ω
  simp only [generatorC2,TimeQuadraticTest.slice,r.d1_eq,r.d2_eq,r.dt_eq]
  rw [scheduleField_PDE f ls 0 t _ ht.1.le (by simpa only [hw,zero_add] using ht.2)]
  ring

lemma finiteTimeCoefficient_nonneg (ls : Schedule) (s t : ℝ) :
    0≤finiteTimeCoefficient ls s t := by
  induction ls generalizing s with
  | nil => exact le_rfl
  | cons l ls ih => simp only [finiteTimeCoefficient];split_ifs;exact l.1.coe_nonneg;exact ih _

 

lemma generalSchedule_terminal_comparison (hW : IsBrownianReal W P)
    (b : Drift K M)
    (hc : ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x))
    (f g : SmoothField) (ls : Schedule) (c : ℝ≥0) (hc0 : c≠0) (hc1 : c≤1)
    (hw : width ls=c)
    (hb : ∀ t∈Ioo (0:ℝ) c,∀ x,b.val t x=finiteTimeCoefficient ls 0 t*(scheduleField f ls 0 t).d1 x) :
    (∫ ω,g.val (solution b (brownianPath W ω)
      ⟨c,by exact ⟨c.coe_nonneg,by exact_mod_cast hc1⟩⟩) ∂P)-
      (∫ ω,f.val (solution b (brownianPath W ω)
      ⟨c,by exact ⟨c.coe_nonneg,by exact_mod_cast hc1⟩⟩) ∂P) ≤
      (smoothEvolve g ls).val 0-(smoothEvolve f ls).val 0 := by
  let rf := generalScheduleTimeRealization f ls 0 le_rfl (by rw [hw,zero_add];exact_mod_cast hc1)
  let rg := generalScheduleTimeRealization g ls 0 le_rfl (by rw [hw,zero_add];exact_mod_cast hc1)
  have hf := brownian_solution_time_generator_at hW b rf.test c hc0 hc1 hc
  have hg := brownian_solution_time_generator_at hW b rg.test c hc0 hc1 hc
  have hsub : uIcc (0:ℝ) c⊆uIcc (0:ℝ) 1 := by
    rw [uIcc_of_le c.coe_nonneg,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl (by exact_mod_cast hc1)
  have hif := (timeGeneratorC2_intervalIntegrable hW b rf.test hc).add
    (timeDerivativeC2_intervalIntegrable hW b rf.test hc)
  have hig := (timeGeneratorC2_intervalIntegrable hW b rg.test hc).add
    (timeDerivativeC2_intervalIntegrable hW b rg.test hc)
  have hle : (∫ t in (0:ℝ)..(c:ℝ),timeGeneratorC2 P W b rg.test t+timeDerivativeC2 P W b rg.test t) ≤
      ∫ t in (0:ℝ)..(c:ℝ),timeGeneratorC2 P W b rf.test t+timeDerivativeC2 P W b rf.test t := by
    apply intervalIntegral.integral_mono_ae_restrict c.coe_nonneg (hig.mono_set hsub) (hif.mono_set hsub)
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (show ∀ᵐ t ∂volume,t≠(0:ℝ) by simp [ae_iff,measure_singleton]),
      ae_restrict_of_ae (show ∀ᵐ t ∂volume,t≠(c:ℝ) by simp [ae_iff,measure_singleton])] with t ht hn0 hne
    have htt : t∈Ioo (0:ℝ) c := ⟨ht.1.lt_of_ne (Ne.symm hn0),ht.2.lt_of_ne hne⟩
    change (∫ ω,generatorC2 (rg.test.slice t) b t (extend (solution b (brownianPath W ω)) t) ∂P)+
        (∫ ω,rg.test.dt t (extend (solution b (brownianPath W ω)) t) ∂P) ≤
      (∫ ω,generatorC2 (rf.test.slice t) b t (extend (solution b (brownianPath W ω)) t) ∂P)+
        (∫ ω,rf.test.dt t (extend (solution b (brownianPath W ω)) t) ∂P)
    rw [←integral_add (generatorC2_integrable hW b _ t) (timeDerivativeC2_integrable_inner hW b rg.test t),
      ←integral_add (generatorC2_integrable hW b _ t) (timeDerivativeC2_integrable_inner hW b rf.test t)]
    apply integral_mono ((generatorC2_integrable hW b _ t).add (timeDerivativeC2_integrable_inner hW b rg.test t))
      ((generatorC2_integrable hW b _ t).add (timeDerivativeC2_integrable_inner hW b rf.test t))
    intro ω
    simp only [Pi.add_apply, generatorC2,TimeQuadraticTest.slice,rg.d1_eq,rg.d2_eq,rg.dt_eq,rf.d1_eq,rf.d2_eq,rf.dt_eq]
    rw [scheduleField_PDE g ls 0 t _ ht.1 (by simpa only [hw,zero_add] using htt.2),
      scheduleField_PDE f ls 0 t _ ht.1 (by simpa only [hw,zero_add] using htt.2),hb t htt]
    have hsquare := mul_nonneg (finiteTimeCoefficient_nonneg ls 0 t)
      (sq_nonneg ((scheduleField g ls 0 t).d1 (extend (solution b (brownianPath W ω)) t) -
        (scheduleField f ls 0 t).d1 (extend (solution b (brownianPath W ω)) t)))
    nlinarith [hsquare]

  rw [intervalIntegral.integral_add ((timeGeneratorC2_intervalIntegrable hW b rg.test hc).mono_set hsub)
      ((timeDerivativeC2_intervalIntegrable hW b rg.test hc).mono_set hsub),
    intervalIntegral.integral_add ((timeGeneratorC2_intervalIntegrable hW b rf.test hc).mono_set hsub)
      ((timeDerivativeC2_intervalIntegrable hW b rf.test hc).mono_set hsub),←hg,←hf] at hle
  have he (r : GeneralScheduleTimeRealization f ls 0) (x : ℝ) : r.test.val c x=f.val x := by
    rw [r.val_eq,scheduleField_after f ls 0 c x (by rw [hw,zero_add])]
  have heg (x : ℝ) : rg.test.val c x=g.val x := by
    rw [rg.val_eq,scheduleField_after g ls 0 c x (by rw [hw,zero_add])]
  simp_rw [he rf,heg,rf.val_eq,rg.val_eq,scheduleField_start] at hle
  linarith

 

lemma generalSchedule_actual_transport (hW : IsBrownianReal W P)
    (b : Drift K M)
    (hc : ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x))
    (f g : SmoothField) (R : ℝ≥0) (hR : ∀ x, |g.val x|≤R)
    (ls : Schedule) (c : ℝ≥0) (hc0 : c≠0) (hc1 : c≤1)
    (hw : width ls=c)
    (hb : ∀ t∈Ioo (0:ℝ) c,∀ x,b.val t x=finiteTimeCoefficient ls 0 t*(scheduleField f ls 0 t).d1 x) :
    (∫ ω,g.val (solution b (brownianPath W ω)
      ⟨c,by exact ⟨c.coe_nonneg,by exact_mod_cast hc1⟩⟩) ∂P) =
      linearEvolve f.val g.val ls 0 := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  let X : Ω → ℝ := fun ω => solution b (brownianPath W ω)
    ⟨c,by exact ⟨c.coe_nonneg,by exact_mod_cast hc1⟩⟩
  let J : ℝ := ∫ ω,g.val (X ω) ∂P
  let V : ℝ → ℝ := fun u => evolve ls (terminalPerturbation f g u).val 0-
    evolve ls f.val 0-Real.sin u*J
  have hX : Integrable X P := brownian_solution_integrable hW b _
  have hif : Integrable (fun ω => f.val (X ω)) P := (f.staticTimeTest.slice 0).integrable_comp hX
  have hig : Integrable (fun ω => g.val (X ω)) P := (g.staticTimeTest.slice 0).integrable_comp hX
  have hle (u : ℝ) : 0≤V u := by
    have hh := generalSchedule_terminal_comparison hW b hc f (terminalPerturbation f g u)
      ls c hc0 hc1 hw hb
    change (∫ ω,f.val (X ω)+Real.sin u*g.val (X ω) ∂P)-
      (∫ ω,f.val (X ω) ∂P) ≤ _ at hh
    rw [integral_add hif (hig.const_mul _),integral_const_mul] at hh
    simp only [smoothEvolve_val] at hh
    dsimp only [V,J]
    linarith
  have he : V 0=0 := by
    simp only [V,terminalPerturbation,Real.sin_zero,zero_mul,add_zero,sub_self]
  have hm : IsLocalMin V 0 := by
    filter_upwards [] with u
    rw [he]
    exact hle u
  have hd : HasDerivAt V (linearEvolve f.val g.val ls 0-J) 0 := by
    have hh := ((hasDerivAt_evolve_terminal f g R hR ls 0).sub_const (evolve ls f.val 0)).sub
      ((Real.hasDerivAt_sin 0).mul_const J)
    convert! hh using 1
    simp only [Real.cos_zero,one_mul]
  have hz := hm.hasDerivAt_eq_zero hd
  change J=_
  linarith

end ParisiFinite

 

 

 

open MeasureTheory Matrix InnerProductSpace Filter
open scoped BigOperators Topology RealInnerProductSpace NNReal

namespace ParisiSpectral

 

def PositiveDefinite {E : Type*} [Sub E] (f : E → ℝ) : Prop :=
  Matrix.PosSemidef (fun x y : E => f (x-y))

section Kernel
variable {A : Type*} (K : Matrix A A ℝ)

def operatorKernel : Matrix A A (ℝ →L[ℝ] ℝ) :=
  fun x y => K x y • ContinuousLinearMap.id ℝ ℝ

lemma operatorKernel_posSemidef (hK : K.PosSemidef) :
    (operatorKernel K).PosSemidef := by
  apply (RKHS.posSemidef_tfae.out 1 3).mpr
  refine ⟨?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro x y
    simp only [operatorKernel, star_smul, star_trivial, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_id]
    rw [show K y x = K x y from hK.1.apply x y]
  · intro f
    have hp := hK.2 f
    simp only [operatorKernel, _root_.smul_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul, RCLike.re_to_real, RCLike.inner_apply, starRingEnd_apply, star_trivial] at *
    have he : (f.sum fun x w => f.sum fun y z => z * (K y x * w)) =
        (f.sum fun x w => f.sum fun y z => w * K x y * z) := by
      apply Finsupp.sum_congr
      intro x hx
      apply Finsupp.sum_congr
      intro y hy
      rw [show K y x = K x y from hK.1.apply x y]
      ring
    rwa [he]

variable [Fact K.PosSemidef]
local instance : Fact (operatorKernel K).PosSemidef := ⟨operatorKernel_posSemidef K Fact.out⟩

abbrev KernelHilbert := RKHS.OfKernel (operatorKernel K)

def kernelFeature (x : A) : KernelHilbert K :=
  RKHS.kerFun (KernelHilbert K) x (1 : ℝ)

lemma inner_kernelFeature (x y : A) :
    ⟪kernelFeature K x, kernelFeature K y⟫_ℝ = K x y := by
  have he := RKHS.kernel_inner (H := KernelHilbert K) y x (1 : ℝ) 1
  simpa only [kernelFeature, KernelHilbert, RKHS.OfKernel.kernel_ofKernel,
    operatorKernel, _root_.smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, mul_one, RCLike.inner_apply, starRingEnd_apply, star_trivial, one_mul,
      show K y x = K x y from (Fact.out : K.PosSemidef).1.apply x y] using he.symm

lemma norm_kernelFeature_sq (x : A) :
    ‖kernelFeature K x‖^2 = K x x := by
  rw [← real_inner_self_eq_norm_sq, inner_kernelFeature]

lemma norm_kernelFeature_sub_sq (x y : A) :
    ‖kernelFeature K x - kernelFeature K y‖^2 = K x x + K y y - 2*K x y := by
  rw [norm_sub_sq_real, norm_kernelFeature_sq, norm_kernelFeature_sq, inner_kernelFeature]
  ring

lemma continuous_kernelFeature [TopologicalSpace A]
    (hc : Continuous (fun p : A × A => K p.1 p.2)) :
    Continuous (kernelFeature K) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  change Filter.Tendsto _ _ _
  rw [Metric.tendsto_nhds]
  intro ε hε
  have ht : Tendsto (fun y => K y y + K x x - 2*K y x) (𝓝 x) (𝓝 0) := by
    have h1 : Continuous (fun y => K y y) := hc.comp (continuous_id.prodMk continuous_id)
    have h2 : Continuous (fun y => K y x) := hc.comp (continuous_id.prodMk continuous_const)
    have h3 := (h1.add (continuous_const (y := K x x)) |>.sub (h2.const_mul 2)).continuousAt (x := x)
    change Tendsto (fun y => K y y + K x x - 2 * K y x) (𝓝 x)
      (𝓝 (K x x + K x x - 2 * K x x)) at h3
    rwa [show K x x + K x x - 2 * K x x = 0 by ring] at h3
  filter_upwards [ht.eventually (gt_mem_nhds (sq_pos_of_pos hε))] with y hy
  rw [dist_eq_norm]
  have hn := norm_kernelFeature_sub_sq K y x
  nlinarith [norm_nonneg (kernelFeature K y - kernelFeature K x)]

 
lemma posSemidef_inner {V : Type*} [SeminormedAddCommGroup V]
    [InnerProductSpace ℝ V] {B : Type*} (v : B → V) :
    Matrix.PosSemidef (fun x y => ⟪v x, v y⟫_ℝ) := by
  classical
  refine ⟨?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro x y
    simp only [star_trivial, real_inner_comm]
  · intro c
    have hp : 0 ≤ ⟪∑ x ∈ c.support, c x • v x, ∑ x ∈ c.support, c x • v x⟫_ℝ := real_inner_self_nonneg
    simpa only [Finsupp.sum, sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right, star_trivial, mul_assoc, mul_left_comm, mul_comm,
      real_inner_comm] using hp

lemma posSemidef_kernel_average {B Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : B → Ω → A)
    (hi : ∀ x, Integrable (fun z => kernelFeature K (T x z)) μ) :
    Matrix.PosSemidef (fun x y => ∫ z, ∫ w, K (T x z) (T y w) ∂μ ∂μ) := by
  have he (x y : B) : (∫ z, ∫ w, K (T x z) (T y w) ∂μ ∂μ) =
      ⟪∫ z, kernelFeature K (T x z) ∂μ, ∫ w, kernelFeature K (T y w) ∂μ⟫_ℝ := by
    simp_rw [← inner_kernelFeature K, integral_inner (hi y)]
    simp_rw [real_inner_comm (∫ w, kernelFeature K (T y w) ∂μ)]
    rw [integral_inner (hi x), real_inner_comm]
  simpa only [he] using posSemidef_inner (fun x => ∫ z, kernelFeature K (T x z) ∂μ)

end Kernel
namespace PositiveDefinite

variable {f g : ℝ → ℝ}

lemma at_zero (hf : PositiveDefinite f) : 0 ≤ f 0 := by
  simpa only [sub_self] using hf.diag_nonneg (i := (0 : ℝ))

lemma even (hf : PositiveDefinite f) (x : ℝ) : f (-x) = f x := by
  simpa only [star_trivial, zero_sub, sub_zero] using hf.1.apply x 0

lemma mul (hf : PositiveDefinite f) (hg : PositiveDefinite g) :
    PositiveDefinite (fun x => f x * g x) := hf.hadamard hg

lemma add (hf : PositiveDefinite f) (hg : PositiveDefinite g) :
    PositiveDefinite (fun x => f x + g x) := Matrix.PosSemidef.add hf hg

lemma smul (hf : PositiveDefinite f) {c : ℝ} (hc : 0 ≤ c) :
    PositiveDefinite (fun x => c * f x) := Matrix.PosSemidef.smul hf hc

lemma comp_linear (hf : PositiveDefinite f) (a : ℝ) :
    PositiveDefinite (fun x => f (a*x)) := by
  have hp := hf.submatrix (fun x => a*x)
  change Matrix.PosSemidef (fun i j : ℝ => f (a*i-a*j)) at hp
  simpa only [PositiveDefinite, ← mul_sub] using hp

lemma constant {c : ℝ} (hc : 0 ≤ c) : PositiveDefinite (fun _ : ℝ => c) := by
  have hp := posSemidef_inner (fun _ : ℝ => (1 : ℝ))
  have he : (fun x y : ℝ => ⟪(1 : ℝ), 1⟫_ℝ) = (fun _ _ : ℝ => (1 : ℝ)) := by
    ext x y
    simp only [RCLike.inner_apply, map_one, mul_one]
  rw [he] at hp
  have hp' := hp.smul hc
  change Matrix.PosSemidef (fun x y : ℝ => c * 1) at hp'
  simpa only [PositiveDefinite, mul_one] using hp' 

lemma pow (hf : PositiveDefinite f) (n : ℕ) : PositiveDefinite (fun x => (f x)^n) := by
  induction n with
  | zero => simpa only [pow_zero] using constant zero_le_one
  | succ n ih => simpa only [pow_succ] using ih.mul hf

lemma norm_le (hf : PositiveDefinite f) (x : ℝ) : ‖f x‖ ≤ f 0 := by
  let K : Matrix ℝ ℝ ℝ := fun x y => f (x-y)
  let : Fact K.PosSemidef := ⟨hf⟩
  have h1 := norm_kernelFeature_sub_sq K x 0
  have h2 := norm_add_sq_real (kernelFeature K x) (kernelFeature K 0)
  rw [norm_kernelFeature_sq, norm_kernelFeature_sq, inner_kernelFeature] at h2
  simp only [K, sub_zero, sub_self] at h1 h2
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith [sq_nonneg ‖kernelFeature K x - kernelFeature K 0‖,
    sq_nonneg ‖kernelFeature K x + kernelFeature K 0‖]

lemma continuous_feature (hf : PositiveDefinite f) (hc : Continuous f) :
    letI : Fact (Matrix.PosSemidef (fun x y : ℝ => f (x-y))) := ⟨hf⟩
    Continuous (kernelFeature (fun x y : ℝ => f (x-y))) := by
  let : Fact (Matrix.PosSemidef (fun x y : ℝ => f (x-y))) := ⟨hf⟩
  apply continuous_kernelFeature
  exact hc.comp (continuous_fst.sub continuous_snd)

lemma posSemidef_limit {B I : Type*} {l : Filter I} [l.NeBot]
    {K : I → Matrix B B ℝ} {L : Matrix B B ℝ}
    (hK : ∀ i, (K i).PosSemidef)
    (ht : ∀ x y, Tendsto (fun i => K i x y) l (𝓝 (L x y))) : L.PosSemidef := by
  classical
  refine ⟨Matrix.IsHermitian.ext (fun x y => ?_), fun c => ?_⟩
  · simp only [star_trivial]
    apply tendsto_nhds_unique (ht y x)
    have he : (fun i => K i y x) = (fun i => K i x y) := by
      funext i
      exact (hK i).1.apply x y
    rw [he]
    exact ht x y
  · apply le_of_tendsto_of_tendsto tendsto_const_nhds
      (tendsto_finsetSum c.support fun x hx =>
        tendsto_finsetSum c.support fun y hy =>
          ((ht x y).const_mul (c x)).mul_const (c y))
    exact Filter.Eventually.of_forall (fun i => (hK i).2 c)

lemma limit {I : Type*} {l : Filter I} [l.NeBot] {g : I → ℝ → ℝ}
    (hg : ∀ i, PositiveDefinite (g i))
    (ht : ∀ x, Tendsto (fun i => g i x) l (𝓝 (f x))) : PositiveDefinite f :=
  posSemidef_limit hg (fun x y => ht (x-y))

end PositiveDefinite

open ProbabilityTheory

 
def heat (t : ℝ≥0) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z, f (x+z) ∂gaussianReal 0 t

lemma gaussian_double_difference {f : ℝ → ℝ} (hc : Continuous f)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (t : ℝ≥0) (x : ℝ) :
    (∫ z, ∫ w, f (x+z-w) ∂gaussianReal 0 t ∂gaussianReal 0 t) = heat (t+t) f x := by
  have he (z : ℝ) : (∫ w, f (x+z-w) ∂gaussianReal 0 t) =
      (∫ w, f (x+z+w) ∂gaussianReal 0 t) := by
    have hh := integral_map (μ := gaussianReal 0 t) (f := fun w => f (x+z+w)) measurable_neg.aemeasurable
      ((hc.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
    rw [gaussianReal_map_neg, neg_zero] at hh
    simpa only [sub_eq_add_neg] using hh.symm
  simp_rw [he]
  have hi : Integrable (fun z => f (x+z)) (gaussianReal 0 t ∗ gaussianReal 0 t) := by
    rw [gaussianReal_conv_gaussianReal]
    exact Integrable.of_bound (hc.comp (continuous_const.add continuous_id)).aestronglyMeasurable C
      (ae_of_all _ fun z => hC _)
  have he' := integral_conv hi
  rw [gaussianReal_conv_gaussianReal, zero_add] at he'
  simpa only [heat, add_assoc] using he'.symm

lemma PositiveDefinite.heat {f : ℝ → ℝ} (hf : PositiveDefinite f)
    (hc : Continuous f) (t : ℝ≥0) : PositiveDefinite (heat t f) := by
  let K : Matrix ℝ ℝ ℝ := fun x y => f (x-y)
  let : Fact K.PosSemidef := ⟨hf⟩
  have hcont : Continuous (kernelFeature K) := hf.continuous_feature hc
  have hi (x : ℝ) : Integrable (fun z => kernelFeature K (x+z)) (gaussianReal 0 (t/2)) := by
    apply Integrable.of_bound (hcont.comp (continuous_const.add continuous_id)).aestronglyMeasurable
      (Real.sqrt (f 0))
    filter_upwards [] with z
    have hn := norm_kernelFeature_sq K (x+z)
    simp only [K, sub_self] at hn
    exact (Real.le_sqrt (norm_nonneg _) hf.at_zero).mpr hn.le
  have hp := posSemidef_kernel_average K (gaussianReal 0 (t/2)) (fun x z : ℝ => x+z) hi
  have he : (fun x y : ℝ => ∫ z, ∫ w, K (x+z) (y+w) ∂gaussianReal 0 (t/2)
      ∂gaussianReal 0 (t/2)) = (fun x y : ℝ => ParisiSpectral.heat t f (x-y)) := by
    funext x y
    have hh := gaussian_double_difference hc hf.norm_le (t/2) (x-y)
    rw [add_halves] at hh
    rw [← hh]
    apply integral_congr_ae
    filter_upwards [] with z
    apply integral_congr_ae
    filter_upwards [] with w
    change f ((x+z)-(y+w)) = f (x-y+z-w)
    congr 1
    ring
  exact (congrArg Matrix.PosSemidef he).mp hp

end ParisiSpectral

 

open MeasureTheory Set Real Matrix
open scoped BigOperators

namespace ParisiSpectral

 

lemma gamma_laplace {r b : ℝ} (hr : 0 < r) (hb : 0 < b) :
    (∫ u in Ioi (0 : ℝ), u ^ (r - 1) * exp (-b * u)) =
      b ^ (-r) * Gamma r := by
  simpa only [rpow_one, sub_add_cancel, div_one, one_div_one, mul_one] using
    (integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := r - 1)
      (b := b) zero_lt_one (by linarith) hb)

lemma gamma_laplace_integrable {r b : ℝ} (hr : 0 < r) (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => u ^ (r - 1) * exp (-b * u)) (Ioi 0) := by
  simpa only [rpow_one] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := r - 1)
      (b := b) (by linarith) zero_lt_one hb)

 
def hyperbolicFeature (r x u : ℝ) : ℝ := exp (r * x - u * exp (2 * x))

lemma hyperbolicFeature_mul (r x y u : ℝ) :
    hyperbolicFeature r x u * hyperbolicFeature r y u =
    exp (r * (x + y)) * exp (-(exp (2*x) + exp (2*y)) * u) := by
  simp only [hyperbolicFeature, ← exp_add]
  congr 1
  ring

lemma exp_sum_cosh (x y : ℝ) :
    exp (2*x) + exp (2*y) = 2 * exp (x+y) * cosh (x-y) := by
  rw [cosh_eq]
  have h₁ : exp (x+y) * exp (x-y) = exp (2*x) := by
    rw [← exp_add]
    congr 1
    ring
  have h₂ : exp (x+y) * exp (-(x-y)) = exp (2*y) := by
    rw [← exp_add]
    congr 1
    ring
  nlinarith

lemma hyperbolic_gram_integral {r : ℝ} (hr : 0 < r) (x y : ℝ) :
    (∫ u in Ioi (0 : ℝ), u ^ (r-1) *
      (hyperbolicFeature r x u * hyperbolicFeature r y u)) =
    (2 : ℝ) ^ (-r) * Gamma r * (cosh (x-y)) ^ (-r) := by
  simp_rw [hyperbolicFeature_mul]
  have hb : 0 < exp (2*x) + exp (2*y) := add_pos (exp_pos _) (exp_pos _)
  calc
    _ = exp (r*(x+y)) *
        ∫ u in Ioi (0 : ℝ), u ^ (r-1) * exp (-(exp (2*x)+exp (2*y))*u) := by
      rw [← integral_const_mul]
      congr 1
      funext u
      ring
    _ = exp (r*(x+y)) * ((exp (2*x)+exp (2*y)) ^ (-r) * Gamma r) := by
      rw [gamma_laplace hr hb]
    _ = (2 : ℝ) ^ (-r) * Gamma r * (cosh (x-y)) ^ (-r) := by
      rw [exp_sum_cosh, mul_rpow (by positivity) (by positivity),
        mul_rpow (by positivity) (by positivity), rpow_def_of_pos (exp_pos _), log_exp]
      have he : exp (r*(x+y)) * exp ((x+y)*(-r)) = 1 := by
        rw [← exp_add]
        rw [show r*(x+y) + (x+y)*(-r) = 0 by ring, exp_zero]
      calc
        _ = (exp (r*(x+y)) * exp ((x+y)*(-r))) *
            ((2 : ℝ)^(-r) * Gamma r * (cosh (x-y))^(-r)) := by ring
        _ = _ := by rw [he, one_mul]

lemma hyperbolic_gram_integrable {r : ℝ} (hr : 0 < r) (x y : ℝ) :
    IntegrableOn (fun u : ℝ => u ^ (r-1) *
      (hyperbolicFeature r x u * hyperbolicFeature r y u)) (Ioi 0) := by
  have hi := (gamma_laplace_integrable hr
    (add_pos (exp_pos (2*x)) (exp_pos (2*y)))).const_mul (exp (r*(x+y)))
  apply hi.congr
  filter_upwards [] with u
  rw [hyperbolicFeature_mul]
  ring

 

lemma posSemidef_integral_gram {A Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (v : A → Ω → ℝ) (w : Ω → ℝ)
    (hw : ∀ᵐ z ∂μ, 0 ≤ w z)
    (hi : ∀ a b, Integrable (fun z => w z * (v a z * v b z)) μ) :
    Matrix.PosSemidef (fun a b => ∫ z, w z * (v a z * v b z) ∂μ) := by
  classical
  refine ⟨?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro a b
    simp only [star_trivial]
    apply integral_congr_ae
    filter_upwards [] with z
    ring
  · intro c
    simp only [Finsupp.sum, star_trivial]
    have hij (a b : A) : Integrable
        (fun z => c a * (w z * (v a z * v b z)) * c b) μ :=
      ((hi a b).const_mul (c a)).mul_const (c b)
    have he : (∑ a ∈ c.support, ∑ b ∈ c.support,
        c a * (∫ z, w z * (v a z * v b z) ∂μ) * c b) =
        ∫ z, w z * (∑ a ∈ c.support, c a * v a z)^2 ∂μ := by
      simp_rw [← integral_const_mul, ← integral_mul_const]
      simp_rw [← integral_finsetSum _ (fun b hb => hij _ b)]
      rw [← integral_finsetSum _ (fun a ha => integrable_finsetSum _ (fun b hb => hij a b))]
      congr 1
      funext z
      simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    rw [he]
    apply integral_nonneg_of_ae
    filter_upwards [hw] with z hz
    exact mul_nonneg hz (sq_nonneg _)

 

theorem cosh_neg_rpow_posSemidef {r : ℝ} (hr : 0 < r) :
    Matrix.PosSemidef (fun x y : ℝ => (cosh (x-y)) ^ (-r)) := by
  have hp := posSemidef_integral_gram (volume.restrict (Ioi (0 : ℝ)))
    (hyperbolicFeature r) (fun u : ℝ => u ^ (r-1))
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu => rpow_nonneg hu.le _))
    (hyperbolic_gram_integrable hr)
  have hc : 0 < (2 : ℝ)^(-r) * Gamma r :=
    mul_pos (rpow_pos_of_pos (by norm_num) _) (Gamma_pos_of_pos hr)
  have hps := hp.smul (inv_nonneg.mpr hc.le)
  have he : ((2 ^ (-r) * Gamma r)⁻¹ •
      (fun a b : ℝ => ∫ z in Ioi (0 : ℝ), z ^ (r-1) *
        (hyperbolicFeature r a z * hyperbolicFeature r b z)) : Matrix ℝ ℝ ℝ) =
      (fun x y : ℝ => (cosh (x-y)) ^ (-r)) := by
    ext x y
    simp only [Pi.smul_apply, smul_eq_mul, hyperbolic_gram_integral hr]
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]
  exact (congrArg Matrix.PosSemidef he).mp hps

end ParisiSpectral

end

end OAI
