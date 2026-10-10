import Mathlib
import OAI.Probability.ParisiFinite.GlobalDyadicFieldError

namespace OAI

/-! Scaled Time Mem. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiPath
variable {K M : ℝ≥0}

lemma scaledTime_mem (c : ℝ≥0) (hc : c≤1) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    (c:ℝ)*t∈Icc (0:ℝ) 1 := by
  refine ⟨mul_nonneg c.coe_nonneg ht.1,?_⟩
  exact (mul_le_mul_of_nonneg_left ht.2 c.coe_nonneg).trans (by simpa only [mul_one,NNReal.coe_one] using (NNReal.coe_le_coe.mpr hc))

def rescalePath (c : ℝ≥0) (hc : c≤1) (X : Path) : Path where
  toFun t := (Real.sqrt c)⁻¹*X ⟨(c:ℝ)*t,scaledTime_mem c hc t.property⟩
  continuous_toFun := continuous_const.mul (X.continuous.comp
    ((continuous_const.mul continuous_subtype_val).subtype_mk _))

lemma extend_rescalePath (c : ℝ≥0) (hc : c≤1) (X : Path) {t : ℝ}
    (ht : t∈Icc (0:ℝ) 1) :
    extend (rescalePath c hc X) t=(Real.sqrt c)⁻¹*extend X ((c:ℝ)*t) := by
  rw [extend_of_mem _ ht,extend_of_mem _ (scaledTime_mem c hc ht)]
  rfl

def Drift.rescale (b : Drift K M) (c : ℝ≥0) : Drift (c*K) (NNReal.sqrt c*M) where
  val := fun t x => Real.sqrt c*b.val ((c:ℝ)*t) (Real.sqrt c*x)
  measurable := measurable_const.mul (b.measurable.comp
    ((measurable_const.mul measurable_fst).prodMk (measurable_const.mul measurable_snd)))
  bound := fun t x => by
    rw [norm_mul,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    simpa only [NNReal.coe_mul,Real.coe_sqrt] using
      mul_le_mul_of_nonneg_left (b.bound _ _) (Real.sqrt_nonneg c)
  lipschitz := fun t => LipschitzWith.of_dist_le_mul fun x y => by
    simp only [Real.dist_eq,←mul_sub,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _),NNReal.coe_mul]
    calc
      _ ≤ Real.sqrt c*((K:ℝ)*|Real.sqrt c*x-Real.sqrt c*y|) :=
        mul_le_mul_of_nonneg_left ((b.lipschitz _).dist_le_mul _ _) (Real.sqrt_nonneg c)
      _ = _ := by
        rw [←mul_sub,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
        calc
          _ = (Real.sqrt c*Real.sqrt c)*K*|x-y| := by ring
          _ = _ := by rw [Real.mul_self_sqrt c.coe_nonneg]

lemma solution_rescale (b : Drift K M) (c : ℝ≥0) (hc0 : c≠0) (hc : c≤1) (W : Path) :
    rescalePath c hc (solution b W)=solution (b.rescale c) (rescalePath c hc W) := by
  have cr : (c:ℝ)≠0 := by exact_mod_cast hc0
  have sr : Real.sqrt c≠0 := (Real.sqrt_pos.2 (by exact_mod_cast (pos_iff_ne_zero.2 hc0))).ne'
  have hs : Real.sqrt c*Real.sqrt c=(c:ℝ) := Real.mul_self_sqrt c.coe_nonneg
  apply solution_unique
  intro t
  change (Real.sqrt c)⁻¹*solution b W ⟨(c:ℝ)*t,scaledTime_mem c hc t.property⟩=
    (Real.sqrt c)⁻¹*W ⟨(c:ℝ)*t,scaledTime_mem c hc t.property⟩+
      ∫ u in (0:ℝ)..(t:ℝ), Real.sqrt c*b.val ((c:ℝ)*u)
        (Real.sqrt c*extend (rescalePath c hc (solution b W)) u)
  rw [solution_eq,mul_add]
  congr 1
  have he : (∫ u in (0:ℝ)..(t:ℝ),Real.sqrt c*b.val ((c:ℝ)*u)
      (Real.sqrt c*extend (rescalePath c hc (solution b W)) u))=
      ∫ u in (0:ℝ)..(t:ℝ),Real.sqrt c*b.val ((c:ℝ)*u)
        (extend (solution b W) ((c:ℝ)*u)) := by
    apply intervalIntegral.integral_congr_Ioo_of_le t.property.1
    intro u hu
    dsimp only
    rw [extend_rescalePath c hc _ ⟨hu.1.le,hu.2.le.trans t.property.2⟩,
      ←mul_assoc,mul_inv_cancel₀ sr,one_mul]
  rw [he,intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_mul_left (fun u => b.val u (extend (solution b W) u)) cr,mul_zero,
    smul_eq_mul]
  have hr : (Real.sqrt c)⁻¹=Real.sqrt c*(c:ℝ)⁻¹ := by
    field_simp
    nlinarith [Real.sq_sqrt c.coe_nonneg]
  rw [hr]
  ring

lemma Drift.rescale_joint (b : Drift K M) (c : ℝ≥0) (hc0 : c≠0) (hc : c≤1)
    (hb : ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x)) :
    ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry (b.rescale c).val) (t,x) := by
  have cr : (c:ℝ)≠0 := by exact_mod_cast hc0
  have hh := (volume.quasiMeasurePreserving_smul cr).ae hb
  filter_upwards [hh] with t ht hmem x
  have hh : ContinuousAt (fun p : ℝ×ℝ => b.val ((c:ℝ)*p.1) (Real.sqrt c*p.2)) (t,x) :=
    ContinuousAt.comp (g := uncurry b.val)
      (f := fun p : ℝ×ℝ => ((c:ℝ)*p.1,Real.sqrt c*p.2))
      (ht (scaledTime_mem c hc hmem) (Real.sqrt c*x))
      (by fun_prop)
  exact continuousAt_const.mul hh

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

lemma brownianPath_rescale (hW : IsBrownianReal W P) (c : ℝ≥0) (hc0 : c≠0) (hc : c≤1) :
    ∀ᵐ ω ∂P,rescalePath c hc (brownianPath W ω)=
      brownianPath (fun t ω => (Real.sqrt c)⁻¹*W (c*t) ω) ω := by
  filter_upwards [brownianPath_eq_ae hW,brownianPath_eq_ae (hW.smul hc0)] with ω hω hω'
  ext t
  change (Real.sqrt c)⁻¹*brownianPath W ω ⟨(c:ℝ)*t,scaledTime_mem c hc t.property⟩=_
  rw [hω,hω']
  rfl

lemma brownian_solution_rescale (hW : IsBrownianReal W P) (b : Drift K M)
    (c : ℝ≥0) (hc0 : c≠0) (hc : c≤1) :
    ∀ᵐ ω ∂P,∀ t : Time,
      solution (b.rescale c) (brownianPath (fun t ω => (Real.sqrt c)⁻¹*W (c*t) ω) ω) t=
        (Real.sqrt c)⁻¹*solution b (brownianPath W ω) ⟨(c:ℝ)*t,scaledTime_mem c hc t.property⟩ := by
  filter_upwards [brownianPath_rescale hW c hc0 hc] with ω hω t
  rw [←hω,←solution_rescale b c hc0 hc]
  rfl

end ParisiPath

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiPath

namespace TimeQuadraticTest

def rescale (f : TimeQuadraticTest) (c : ℝ≥0) (hc0 : c≠0) (hc : c≤1) : TimeQuadraticTest where
  val := fun t x => f.val ((c:ℝ)*t) (Real.sqrt c*x)
  d1 := fun t x => Real.sqrt c*f.d1 ((c:ℝ)*t) (Real.sqrt c*x)
  d2 := fun t x => (c:ℝ)*f.d2 ((c:ℝ)*t) (Real.sqrt c*x)
  dt := fun t x => (c:ℝ)*f.dt ((c:ℝ)*t) (Real.sqrt c*x)
  hasD1 := fun t x => by
    convert (f.hasD1 ((c:ℝ)*t) (Real.sqrt c*x)).comp x
      ((hasDerivAt_id x).const_mul (Real.sqrt c)) using 1 <;> first | rfl | ring
  hasD2 := fun t x => by
    convert! ((f.hasD2 ((c:ℝ)*t) (Real.sqrt c*x)).comp x
      ((hasDerivAt_id x).const_mul (Real.sqrt c))).const_mul (Real.sqrt c) using 1
    calc
      _ = (Real.sqrt c*Real.sqrt c)*f.d2 ((c:ℝ)*t) (Real.sqrt c*x) := by
        rw [Real.mul_self_sqrt c.coe_nonneg]
      _ = _ := by ring
  continuousD2 := fun t => continuous_const.mul
    ((f.continuousD2 _).comp (continuous_const.mul continuous_id))
  c1 := NNReal.sqrt c*f.c1
  c2 := c*f.c2
  ct := c*f.ct
  bound1 := fun t x => by
    rw [norm_mul,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    simpa only [NNReal.coe_mul,Real.coe_sqrt] using
      mul_le_mul_of_nonneg_left (f.bound1 ((c:ℝ)*t) (Real.sqrt c*x)) (Real.sqrt_nonneg c)
  bound2 := fun t x => by
    rw [norm_mul,Real.norm_of_nonneg c.coe_nonneg]
    exact mul_le_mul_of_nonneg_left (f.bound2 _ _) c.coe_nonneg
  boundT := fun t x => by
    rw [norm_mul,Real.norm_of_nonneg c.coe_nonneg]
    exact mul_le_mul_of_nonneg_left (f.boundT _ _) c.coe_nonneg
  measT := measurable_const.mul (f.measT.comp
    ((measurable_const.mul measurable_fst).prodMk (measurable_const.mul measurable_snd)))
  continuousT := fun t => continuous_const.mul
    ((f.continuousT _).comp (continuous_const.mul continuous_id))
  jointD1 := by
    have cr : (c:ℝ)≠0 := by exact_mod_cast hc0
    filter_upwards [(volume.quasiMeasurePreserving_smul cr).ae f.jointD1] with t ht hmem x
    have hh : ContinuousAt (fun p : ℝ×ℝ => f.d1 ((c:ℝ)*p.1) (Real.sqrt c*p.2)) (t,x) :=
      ContinuousAt.comp (g := uncurry f.d1)
        (f := fun p : ℝ×ℝ => ((c:ℝ)*p.1,Real.sqrt c*p.2))
        (ht (scaledTime_mem c hc hmem) (Real.sqrt c*x)) (by fun_prop)
    exact continuousAt_const.mul hh
  jointD2 := by
    have cr : (c:ℝ)≠0 := by exact_mod_cast hc0
    filter_upwards [(volume.quasiMeasurePreserving_smul cr).ae f.jointD2] with t ht hmem x
    have hh : ContinuousAt (fun p : ℝ×ℝ => f.d2 ((c:ℝ)*p.1) (Real.sqrt c*p.2)) (t,x) :=
      ContinuousAt.comp (g := uncurry f.d2)
        (f := fun p : ℝ×ℝ => ((c:ℝ)*p.1,Real.sqrt c*p.2))
        (ht (scaledTime_mem c hc hmem) (Real.sqrt c*x)) (by fun_prop)
    exact continuousAt_const.mul hh
  integralT := fun a ha b hb x => by
    rw [f.integralT _ (scaledTime_mem c hc ha) _ (scaledTime_mem c hc hb),
      intervalIntegral.integral_const_mul]
    exact (intervalIntegral.smul_integral_comp_mul_left (fun t => f.dt t (Real.sqrt c*x)) (c:ℝ)).symm

end TimeQuadraticTest

variable {K M : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

lemma brownian_solution_rescale_extend (hW : IsBrownianReal W P) (b : Drift K M)
    (c : ℝ≥0) (hc0 : c≠0) (hc : c≤1) :
    ∀ᵐ ω ∂P,∀ t∈Icc (0:ℝ) 1,
      Real.sqrt c*extend (solution (b.rescale c)
        (brownianPath (fun t ω => (Real.sqrt c)⁻¹*W (c*t) ω) ω)) t=
          extend (solution b (brownianPath W ω)) ((c:ℝ)*t) := by
  have sr : Real.sqrt c≠0 := (Real.sqrt_pos.2 (by exact_mod_cast (pos_iff_ne_zero.2 hc0))).ne'
  filter_upwards [brownian_solution_rescale hW b c hc0 hc] with ω hω t ht
  rw [extend_of_mem _ ht,hω,extend_of_mem _ (scaledTime_mem c hc ht),
    ←mul_assoc,mul_inv_cancel₀ sr,one_mul]

lemma timeGeneratorC2_rescale (hW : IsBrownianReal W P) (b : Drift K M) (f : TimeQuadraticTest)
    (c : ℝ≥0) (hc0 : c≠0) (hc : c≤1) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    timeGeneratorC2 P (fun t ω => (Real.sqrt c)⁻¹*W (c*t) ω)
      (b.rescale c) (f.rescale c hc0 hc) t=(c:ℝ)*timeGeneratorC2 P W b f ((c:ℝ)*t) := by
  unfold timeGeneratorC2 expectedGeneratorC2 generatorC2
  rw [←MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  filter_upwards [brownian_solution_rescale_extend hW b c hc0 hc] with ω hω
  let x := extend (solution b (brownianPath W ω)) ((c:ℝ)*t)
  let y := extend (solution (b.rescale c)
    (brownianPath (fun t ω => (Real.sqrt c)⁻¹*W (c*t) ω) ω)) t
  have hy : Real.sqrt c*y=x := hω t ht
  change Real.sqrt c*f.d1 ((c:ℝ)*t) (Real.sqrt c*y)*
    (Real.sqrt c*b.val ((c:ℝ)*t) (Real.sqrt c*y))+
    1/2*((c:ℝ)*f.d2 ((c:ℝ)*t) (Real.sqrt c*y))=
      (c:ℝ)*(f.d1 ((c:ℝ)*t) x*b.val ((c:ℝ)*t) x+1/2*f.d2 ((c:ℝ)*t) x)
  rw [hy]
  have hs := Real.mul_self_sqrt c.coe_nonneg
  calc
    _ = (Real.sqrt c*Real.sqrt c)*(f.d1 ((c:ℝ)*t) x*b.val ((c:ℝ)*t) x)+
      (c:ℝ)*(1/2*f.d2 ((c:ℝ)*t) x) := by ring
    _ = _ := by rw [hs]; ring

lemma timeDerivativeC2_rescale (hW : IsBrownianReal W P) (b : Drift K M) (f : TimeQuadraticTest)
    (c : ℝ≥0) (hc0 : c≠0) (hc : c≤1) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    timeDerivativeC2 P (fun t ω => (Real.sqrt c)⁻¹*W (c*t) ω)
      (b.rescale c) (f.rescale c hc0 hc) t=(c:ℝ)*timeDerivativeC2 P W b f ((c:ℝ)*t) := by
  unfold timeDerivativeC2
  rw [←MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  filter_upwards [brownian_solution_rescale_extend hW b c hc0 hc] with ω hω
  dsimp only [TimeQuadraticTest.rescale]
  rw [hω t ht]

 
theorem brownian_solution_time_generator_at (hW : IsBrownianReal W P)
    (b : Drift K M) (f : TimeQuadraticTest) (c : ℝ≥0) (hc0 : c≠0) (hc : c≤1)
    (hb : ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x)) :
    (∫ ω,f.val c (solution b (brownianPath W ω) ⟨c,by exact ⟨c.coe_nonneg,by exact_mod_cast hc⟩⟩) ∂P)-f.val 0 0=
      (∫ t in (0:ℝ)..(c:ℝ),timeGeneratorC2 P W b f t)+
        (∫ t in (0:ℝ)..(c:ℝ),timeDerivativeC2 P W b f t) := by
  have hid := brownian_solution_time_generator_identity_C2 (hW.smul hc0)
    (b.rescale c) (f.rescale c hc0 hc) (b.rescale_joint c hc0 hc hb)
  have hterm : (∫ ω,(f.rescale c hc0 hc).val 1
      (solution (b.rescale c) (brownianPath (fun t ω => (Real.sqrt c)⁻¹*W (c*t) ω) ω) ⟨1,by simp⟩) ∂P)=
      ∫ ω,f.val c (solution b (brownianPath W ω) ⟨c,by exact ⟨c.coe_nonneg,by exact_mod_cast hc⟩⟩) ∂P := by
    apply integral_congr_ae
    filter_upwards [brownian_solution_rescale_extend hW b c hc0 hc] with ω hω
    have he := hω 1 ⟨zero_le_one,le_rfl⟩
    rw [extend_of_mem _ ⟨zero_le_one,le_rfl⟩,mul_one,extend_of_mem _
      ⟨c.coe_nonneg,by exact_mod_cast hc⟩] at he
    dsimp only [TimeQuadraticTest.rescale]
    rw [mul_one,he]
  have hgen : (∫ t in (0:ℝ)..1,timeGeneratorC2 P (fun t ω => (Real.sqrt c)⁻¹*W (c*t) ω)
      (b.rescale c) (f.rescale c hc0 hc) t)=∫ t in (0:ℝ)..(c:ℝ),timeGeneratorC2 P W b f t := by
    calc
      _ = ∫ t in (0:ℝ)..1,(c:ℝ)*timeGeneratorC2 P W b f ((c:ℝ)*t) :=
        intervalIntegral.integral_congr_Ioo_of_le zero_le_one fun t ht =>
          timeGeneratorC2_rescale hW b f c hc0 hc ⟨ht.1.le,ht.2.le⟩
      _ = _ := by
        rw [intervalIntegral.integral_const_mul]
        simpa only [smul_eq_mul,mul_zero,mul_one] using
          intervalIntegral.smul_integral_comp_mul_left (timeGeneratorC2 P W b f) (a := 0) (b := 1) (c:ℝ)
  have hdt : (∫ t in (0:ℝ)..1,timeDerivativeC2 P (fun t ω => (Real.sqrt c)⁻¹*W (c*t) ω)
      (b.rescale c) (f.rescale c hc0 hc) t)=∫ t in (0:ℝ)..(c:ℝ),timeDerivativeC2 P W b f t := by
    calc
      _ = ∫ t in (0:ℝ)..1,(c:ℝ)*timeDerivativeC2 P W b f ((c:ℝ)*t) :=
        intervalIntegral.integral_congr_Ioo_of_le zero_le_one fun t ht =>
          timeDerivativeC2_rescale hW b f c hc0 hc ⟨ht.1.le,ht.2.le⟩
      _ = _ := by
        rw [intervalIntegral.integral_const_mul]
        simpa only [smul_eq_mul,mul_zero,mul_one] using
          intervalIntegral.smul_integral_comp_mul_left (timeDerivativeC2 P W b f) (a := 0) (b := 1) (c:ℝ)
  rw [hterm,hgen,hdt] at hid
  simpa only [TimeQuadraticTest.rescale,mul_zero] using hid

end ParisiPath

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite
open ParisiPath
variable {K M : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

def finiteSquareKernel (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (b : Drift K M)
    (t x : ℝ) : ℝ :=
  ((finiteTimeField β hβ ls 0 t).d2 x)^2+
    2*(finiteTimeField β hβ ls 0 t).d1 x*(finiteTimeField β hβ ls 0 t).d2 x*
      (b.val t x-finiteTimeCoefficient ls 0 t*(finiteTimeField β hβ ls 0 t).d1 x)

lemma finiteSquareKernel_bound (β : ℝ≥0) (hβ : 0<β) (ls : Schedule)
    (ha : ∀ l∈ls,l.1≤β) (b : Drift K M) (t x : ℝ) :
    ‖finiteSquareKernel β hβ ls b t x‖≤(β:ℝ)^2+2*(β:ℝ)*((M:ℝ)+(β:ℝ)) := by
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
  rw [finiteSquareKernel,Real.norm_eq_abs]
  apply (abs_add_le _ _).trans
  simp only [abs_pow,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ (β:ℝ)^2+2*1*(β:ℝ)*((M:ℝ)+(β:ℝ)) := by gcongr
    _ = _ := by ring

lemma finiteSquareKernel_integrable (hW : IsBrownianReal W P)
    (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (ha : ∀ l∈ls,l.1≤β)
    (b : Drift K M) (t : ℝ) :
    Integrable (fun ω => finiteSquareKernel β hβ ls b t
      (extend (solution b (brownianPath W ω)) t)) P := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  refine Integrable.of_bound (C := (β:ℝ)^2+2*(β:ℝ)*((M:ℝ)+(β:ℝ))) ?_ ?_
  · have hx := aemeasurable_solution_eval b (brownianPath W) (brownianPath_aemeasurable_eval hW)
      (projIcc 0 1 zero_le_one t)
    have h1 := (finiteTimeField β hβ ls 0 t).continuousD1
    have h2 := (finiteTimeField β hβ ls 0 t).continuousD2
    have hc : Continuous (finiteSquareKernel β hβ ls b t) := by
      unfold finiteSquareKernel
      exact (h2.pow 2).add (((continuous_const.mul h1).mul h2).mul
        ((b.lipschitz t).continuous.sub (continuous_const.mul h1)))
    exact hc.measurable.comp_aemeasurable hx |>.aestronglyMeasurable
  · exact ae_of_all _ fun ω => finiteSquareKernel_bound β hβ ls ha b t _

lemma expected_finiteSquareKernel_eq (hW : IsBrownianReal W P)
    (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (hw : width ls=1) (b : Drift K M)
    (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
    (∫ ω,finiteSquareKernel β hβ ls b t (extend (solution b (brownianPath W ω)) t) ∂P)=
      timeGeneratorC2 P W b (scheduleGradientSquare β hβ ls 0 le_rfl (by rw [hw];norm_num)).test t+
      timeDerivativeC2 P W b (scheduleGradientSquare β hβ ls 0 le_rfl (by rw [hw];norm_num)).test t := by
  let r := scheduleGradientSquare β hβ ls 0 le_rfl (by rw [hw];norm_num)
  change _=(∫ ω,generatorC2 (r.test.slice t) b t (extend (solution b (brownianPath W ω)) t) ∂P)+
    (∫ ω,r.test.dt t (extend (solution b (brownianPath W ω)) t) ∂P)
  rw [←integral_add (generatorC2_integrable hW b _ t) (timeDerivativeC2_integrable_inner hW b r.test t)]
  apply integral_congr_ae
  filter_upwards [] with ω
  have hh := r.cancel t ht.1.le (by simpa only [hw,zero_add] using ht.2)
    (extend (solution b (brownianPath W ω)) t) (b.val t (extend (solution b (brownianPath W ω)) t))
  dsimp only [generatorC2,TimeQuadraticTest.slice,finiteSquareKernel]
  linarith

lemma expected_finiteSquareKernel_aestronglyMeasurable (hW : IsBrownianReal W P)
    (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (hw : width ls=1) (b : Drift K M)
    (hc : ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x)) :
    AEStronglyMeasurable (fun t => ∫ ω,finiteSquareKernel β hβ ls b t
      (extend (solution b (brownianPath W ω)) t) ∂P) (volume.restrict (Ioc (0:ℝ) 1)) := by
  let r := scheduleGradientSquare β hβ ls 0 le_rfl (by rw [hw];norm_num)
  have hj := timeGeneratorC2_intervalIntegrable hW b r.test hc
  have ht := timeDerivativeC2_intervalIntegrable hW b r.test hc
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hj ht
  apply (hj.aestronglyMeasurable.add ht.aestronglyMeasurable).congr
  have hnot : ∀ᵐ t ∂volume,t≠(1:ℝ) := by simp [ae_iff,measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae hnot] with t hmem hn
  exact (expected_finiteSquareKernel_eq hW β hβ ls hw b t ⟨hmem.1,hmem.2.lt_of_ne hn⟩).symm

lemma expected_finiteSquareKernel_bound (hW : IsBrownianReal W P)
    (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (ha : ∀ l∈ls,l.1≤β) (b : Drift K M) (t : ℝ) :
    ‖∫ ω,finiteSquareKernel β hβ ls b t (extend (solution b (brownianPath W ω)) t) ∂P‖≤
      (β:ℝ)^2+2*(β:ℝ)*((M:ℝ)+(β:ℝ)) := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact (norm_integral_le_of_norm_le_const (μ:=P) (ae_of_all P fun ω =>
    finiteSquareKernel_bound β hβ ls ha b t _)).trans_eq (by simp)

 
theorem finite_schedule_square_verification (hW : IsBrownianReal W P)
    (b : Drift K M)
    (hc : ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x))
    (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (hw : width ls=1)
    (c : ℝ≥0) (hc0 : c≠0) (hc1 : c≤1) :
    (∫ ω,((finiteTimeField β hβ ls 0 c).d1
      (solution b (brownianPath W ω) ⟨c,by exact ⟨c.coe_nonneg,by exact_mod_cast hc1⟩⟩))^2 ∂P)-
      ((smoothRecursion β hβ ls).d1 0)^2=
        ∫ t in (0:ℝ)..(c:ℝ),∫ ω,finiteSquareKernel β hβ ls b t
          (extend (solution b (brownianPath W ω)) t) ∂P := by
  let r := scheduleGradientSquare β hβ ls 0 le_rfl (by rw [hw];norm_num)
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
  exact (expected_finiteSquareKernel_eq hW β hβ ls hw b t
    ⟨ht.1,ht.2.trans_le (by exact_mod_cast hc1)⟩).symm

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite
open ParisiPath
variable {K M : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

def squareKernel (β : ℝ≥0) (γ : ℝ≥0 → ℝ≥0) (b : Drift K M) (t x : ℝ) : ℝ :=
  (fieldCurvature β γ (Real.toNNReal t) x)^2+
    2*fieldGradient β γ (Real.toNNReal t) x*fieldCurvature β γ (Real.toNNReal t) x*
      (b.val t x-(γ (Real.toNNReal t):ℝ)*fieldGradient β γ (Real.toNNReal t) x)

lemma global_dyadic_squareKernel_tendsto (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0}
    (hγ : Monotone γ) (hb : ∀ t,γ t≤β) (b : Drift K M) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1)
    (hc : Tendsto (fun n => finiteTimeCoefficient (dyadicSchedule γ false 0 1 n) 0 t)
      atTop (𝓝 (γ (Real.toNNReal t):ℝ))) (x : ℝ) :
    Tendsto (fun n => finiteSquareKernel β hβ (dyadicSchedule γ false 0 1 n) b t x)
      atTop (𝓝 (squareKernel β γ b t x)) := by
  have hr : Real.toNNReal t<1 := by
    exact_mod_cast (show (Real.toNNReal t:ℝ)<1 by rw [Real.coe_toNNReal _ ht.1.le];exact ht.2)
  have hg := (global_dyadic_gradient_tendstoUniformly β hβ hγ hb _ hr).tendsto_at x
  have ha := (global_dyadic_curvature_tendstoUniformly β hβ hγ hb _ hr).tendsto_at x
  rw [Real.coe_toNNReal _ ht.1.le] at hg ha
  exact (ha.pow 2).add (((hg.const_mul 2).mul ha).mul (tendsto_const_nhds.sub (hc.mul hg)))

lemma expected_global_dyadic_squareKernel_tendsto (hW : IsBrownianReal W P)
    (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t≤β)
    (b : Drift K M) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1)
    (hc : Tendsto (fun n => finiteTimeCoefficient (dyadicSchedule γ false 0 1 n) 0 t)
      atTop (𝓝 (γ (Real.toNNReal t):ℝ))) :
    Tendsto (fun n => ∫ ω,finiteSquareKernel β hβ (dyadicSchedule γ false 0 1 n) b t
      (extend (solution b (brownianPath W ω)) t) ∂P) atTop
      (𝓝 (∫ ω,squareKernel β γ b t (extend (solution b (brownianPath W ω)) t) ∂P)) := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  apply tendsto_integral_of_dominated_convergence
    (fun _ : Ω => (β:ℝ)^2+2*(β:ℝ)*((M:ℝ)+(β:ℝ)))
    (fun n => (finiteSquareKernel_integrable hW β hβ _ (dyadicSchedule_coeff_bound hb false 0 1 n) b t).aestronglyMeasurable)
    (integrable_const _) (fun n => ae_of_all _ fun ω =>
      finiteSquareKernel_bound β hβ _ (dyadicSchedule_coeff_bound hb false 0 1 n) b t _)
  exact ae_of_all _ fun ω => global_dyadic_squareKernel_tendsto β hβ hγ hb b t ht hc _

lemma expected_global_dyadic_gradient_square_tendsto (hW : IsBrownianReal W P)
    (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t≤β)
    (b : Drift K M) (c : ℝ≥0) (hc : c<1) :
    Tendsto (fun n => ∫ ω,((finiteTimeField β hβ (dyadicSchedule γ false 0 1 n) 0 c).d1
      (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc.le⟩))^2 ∂P) atTop
      (𝓝 (∫ ω,(fieldGradient β γ c
        (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc.le⟩))^2 ∂P)) := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hx := aemeasurable_solution_eval b (brownianPath W) (brownianPath_aemeasurable_eval hW)
    ⟨c,c.coe_nonneg,by exact_mod_cast hc.le⟩
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (1:ℝ))
  · intro n
    exact (((finiteTimeField β hβ _ 0 c).continuousD1.measurable.comp_aemeasurable hx).pow_const 2).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [] with ω
    rw [norm_pow]
    have hh := (finiteTimeField β hβ (dyadicSchedule γ false 0 1 n) 0 c).normD1
      (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc.le⟩)
    have hh' : ‖(finiteTimeField β hβ (dyadicSchedule γ false 0 1 n) 0 c).d1
        (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc.le⟩)‖≤1 := by
      simpa only [(finiteTimeField_curvature β hβ _ (dyadicSchedule_coeff_bound hb false 0 1 n) 0 c).1,NNReal.coe_one,Real.norm_eq_abs] using hh
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) hh' 2
  · exact ae_of_all _ fun ω => ((global_dyadic_gradient_tendstoUniformly β hβ hγ hb c hc).tendsto_at _).pow 2

 

theorem canonical_square_verification (hW : IsBrownianReal W P) (b : Drift K M)
    (hc : ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x))
    (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t≤β)
    (c : ℝ≥0) (hc0 : c≠0) (hc1 : c<1) :
    (∫ ω,(fieldGradient β γ c
      (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc1.le⟩))^2 ∂P)-
      (fieldGradient β γ 0 0)^2=
        ∫ t in (0:ℝ)..(c:ℝ),∫ ω,squareKernel β γ b t
          (extend (solution b (brownianPath W ω)) t) ∂P := by
  have hsub : Ioc (0:ℝ) c⊆Ioc (0:ℝ) 1 := Ioc_subset_Ioc le_rfl (by exact_mod_cast hc1.le)
  have hi : Tendsto (fun n => ∫ t in (0:ℝ)..(c:ℝ),∫ ω,
      finiteSquareKernel β hβ (dyadicSchedule γ false 0 1 n) b t
        (extend (solution b (brownianPath W ω)) t) ∂P) atTop
      (𝓝 (∫ t in (0:ℝ)..(c:ℝ),∫ ω,squareKernel β γ b t
        (extend (solution b (brownianPath W ω)) t) ∂P)) := by
    have hmeas (n : ℕ) : AEStronglyMeasurable
        (fun t => ∫ ω,finiteSquareKernel β hβ (dyadicSchedule γ false 0 1 n) b t
          (extend (solution b (brownianPath W ω)) t) ∂P) (volume.restrict (uIoc (0:ℝ) c)) := by
      rw [uIoc_of_le c.coe_nonneg]
      exact (expected_finiteSquareKernel_aestronglyMeasurable hW β hβ _
        (by simpa only [NNReal.coe_one] using dyadicSchedule_width γ false 0 1 n) b hc).mono_measure
          (Measure.restrict_mono_set _ hsub)
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => (β:ℝ)^2+2*(β:ℝ)*((M:ℝ)+(β:ℝ))) (Eventually.of_forall hmeas)
      (Eventually.of_forall fun n => ae_of_all _ fun t _ =>
        expected_finiteSquareKernel_bound hW β hβ _ (dyadicSchedule_coeff_bound hb false 0 1 n) b t)
      intervalIntegrable_const
    filter_upwards [global_dyadic_coefficient_tendsto_ae hγ] with t ht hmem
    rw [uIoc_of_le c.coe_nonneg] at hmem
    have hti : t∈Ioo (0:ℝ) 1 := ⟨hmem.1,hmem.2.trans_lt (by exact_mod_cast hc1)⟩
    exact expected_global_dyadic_squareKernel_tendsto hW β hβ hγ hb b t hti (ht hti)
  have h0 : Tendsto (fun n => ((smoothRecursion β hβ (dyadicSchedule γ false 0 1 n)).d1 0)^2)
      atTop (𝓝 ((fieldGradient β γ 0 0)^2)) := by
    have hh := ((global_dyadic_gradient_tendstoUniformly β hβ hγ hb 0 (by norm_num)).tendsto_at 0).pow 2
    simpa only [NNReal.coe_zero,finiteTimeField_d1_start] using hh
  have he : (fun n => (∫ ω,((finiteTimeField β hβ (dyadicSchedule γ false 0 1 n) 0 c).d1
      (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc1.le⟩))^2 ∂P)-
      ((smoothRecursion β hβ (dyadicSchedule γ false 0 1 n)).d1 0)^2)=
    (fun n => ∫ t in (0:ℝ)..(c:ℝ),∫ ω,finiteSquareKernel β hβ (dyadicSchedule γ false 0 1 n) b t
      (extend (solution b (brownianPath W ω)) t) ∂P) := by
    funext n
    exact finite_schedule_square_verification hW b hc β hβ _
      (by simpa only [NNReal.coe_one] using dyadicSchedule_width γ false 0 1 n) c hc0 hc1.le
  exact tendsto_nhds_unique
    ((expected_global_dyadic_gradient_square_tendsto hW β hβ hγ hb b c hc1).sub h0) (he ▸ hi)

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite
open ParisiPath
variable {K M : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

def finiteVerificationKernel (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (b : Drift K M)
    (t x : ℝ) : ℝ :=
  (finiteTimeField β hβ ls 0 t).d1 x*b.val t x-
    finiteTimeCoefficient ls 0 t/2*((finiteTimeField β hβ ls 0 t).d1 x)^2

def verificationKernel (β : ℝ≥0) (γ : ℝ≥0 → ℝ≥0) (b : Drift K M)
    (t x : ℝ) : ℝ :=
  fieldGradient β γ (Real.toNNReal t) x*b.val t x-
    (γ (Real.toNNReal t):ℝ)/2*(fieldGradient β γ (Real.toNNReal t) x)^2

lemma finiteVerificationKernel_bound (β : ℝ≥0) (hβ : 0<β) (ls : Schedule)
    (ha : ∀ l∈ls,l.1≤β) (b : Drift K M) (t x : ℝ) :
    ‖finiteVerificationKernel β hβ ls b t x‖ ≤ (M:ℝ)+(β:ℝ)/2 := by
  have hm : |(finiteTimeField β hβ ls 0 t).d1 x|≤1 := by
    simpa only [(finiteTimeField_curvature β hβ ls ha 0 t).1,NNReal.coe_one] using
      (finiteTimeField β hβ ls 0 t).normD1 x
  have hc := finiteTimeCoefficient_bound β ls ha 0 t
  have hbm : |b.val t x|≤(M:ℝ) := by simpa only [Real.norm_eq_abs] using b.bound t x
  rw [finiteVerificationKernel,Real.norm_eq_abs]
  calc
    _ ≤ |(finiteTimeField β hβ ls 0 t).d1 x*b.val t x|+
        |finiteTimeCoefficient ls 0 t/2*((finiteTimeField β hβ ls 0 t).d1 x)^2| := abs_sub _ _
    _ ≤ (M:ℝ)+(β:ℝ)/2 := by
      rw [abs_mul,abs_mul,abs_div,abs_of_nonneg (sq_nonneg ((finiteTimeField β hβ ls 0 t).d1 x)),abs_of_pos (by norm_num : (0:ℝ)<2)]
      have h1 : |(finiteTimeField β hβ ls 0 t).d1 x| *|b.val t x|≤(M:ℝ) := by
        exact (mul_le_mul hm hbm (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
      have hsq : ((finiteTimeField β hβ ls 0 t).d1 x)^2≤1 := by
        simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) hm 2
      have h2 : |finiteTimeCoefficient ls 0 t|/2*((finiteTimeField β hβ ls 0 t).d1 x)^2≤(β:ℝ)/2 :=
        (mul_le_mul (div_le_div_of_nonneg_right hc (by norm_num)) hsq
          (sq_nonneg _) (by positivity)).trans_eq (mul_one _)
      exact add_le_add h1 h2

lemma finiteVerificationKernel_integrable (hW : IsBrownianReal W P)
    (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (ha : ∀ l∈ls,l.1≤β)
    (b : Drift K M) (t : ℝ) :
    Integrable (fun ω => finiteVerificationKernel β hβ ls b t
      (extend (solution b (brownianPath W ω)) t)) P := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  apply Integrable.of_bound (C := (M:ℝ)+(β:ℝ)/2)
  · have hx := aemeasurable_solution_eval b (brownianPath W) (brownianPath_aemeasurable_eval hW)
      (projIcc 0 1 zero_le_one t)
    exact (((finiteTimeField β hβ ls 0 t).continuousD1.mul (b.lipschitz t).continuous).sub
      (continuous_const.mul ((finiteTimeField β hβ ls 0 t).continuousD1.pow 2))).measurable.comp_aemeasurable hx
      |>.aestronglyMeasurable
  · exact ae_of_all _ fun ω => finiteVerificationKernel_bound β hβ ls ha b t _

lemma expected_finiteVerificationKernel_eq (hW : IsBrownianReal W P)
    (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (hw : width ls=1) (b : Drift K M)
    (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
    (∫ ω,finiteVerificationKernel β hβ ls b t (extend (solution b (brownianPath W ω)) t) ∂P)=
      timeGeneratorC2 P W b (scheduleTimeRealization β hβ ls 0 le_rfl (by rw [hw];norm_num)).test t+
      timeDerivativeC2 P W b (scheduleTimeRealization β hβ ls 0 le_rfl (by rw [hw];norm_num)).test t := by
  let r := scheduleTimeRealization β hβ ls 0 le_rfl (by rw [hw];norm_num)
  change _=(∫ ω,generatorC2 (r.test.slice t) b t (extend (solution b (brownianPath W ω)) t) ∂P)+
    (∫ ω,r.test.dt t (extend (solution b (brownianPath W ω)) t) ∂P)
  rw [←integral_add (generatorC2_integrable hW b _ t) (timeDerivativeC2_integrable_inner hW b r.test t)]
  apply integral_congr_ae
  filter_upwards [] with ω
  simp only [generatorC2,TimeQuadraticTest.slice,r.d1_eq,r.d2_eq,r.dt_eq,finiteVerificationKernel]
  rw [finiteTimeField_PDE β hβ ls 0 t _ ht.1.le (by simpa only [hw,zero_add] using ht.2)]
  ring

lemma expected_finiteVerificationKernel_aestronglyMeasurable (hW : IsBrownianReal W P)
    (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (hw : width ls=1) (b : Drift K M)
    (hc : ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x)) :
    AEStronglyMeasurable (fun t => ∫ ω,finiteVerificationKernel β hβ ls b t
      (extend (solution b (brownianPath W ω)) t) ∂P) (volume.restrict (Ioc (0:ℝ) 1)) := by
  let r := scheduleTimeRealization β hβ ls 0 le_rfl (by rw [hw];norm_num)
  have hj := timeGeneratorC2_intervalIntegrable hW b r.test hc
  have ht := timeDerivativeC2_intervalIntegrable hW b r.test hc
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hj ht
  apply (hj.aestronglyMeasurable.add ht.aestronglyMeasurable).congr
  have hnot : ∀ᵐ t ∂volume,t≠(1:ℝ) := by simp [ae_iff,measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae hnot] with t hmem hn
  exact (expected_finiteVerificationKernel_eq hW β hβ ls hw b t ⟨hmem.1,hmem.2.lt_of_ne hn⟩).symm

lemma expected_finiteVerificationKernel_bound (hW : IsBrownianReal W P)
    (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (ha : ∀ l∈ls,l.1≤β) (b : Drift K M) (t : ℝ) :
    ‖∫ ω,finiteVerificationKernel β hβ ls b t (extend (solution b (brownianPath W ω)) t) ∂P‖ ≤
      (M:ℝ)+(β:ℝ)/2 := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact (norm_integral_le_of_norm_le_const (μ:=P) (ae_of_all P fun ω =>
    finiteVerificationKernel_bound β hβ ls ha b t (extend (solution b (brownianPath W ω)) t))).trans_eq (by simp)

lemma global_dyadic_verificationKernel_tendsto (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0}
    (hγ : Monotone γ) (hb : ∀ t,γ t≤β) (b : Drift K M) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1)
    (hc : Tendsto (fun n => finiteTimeCoefficient (dyadicSchedule γ false 0 1 n) 0 t)
      atTop (𝓝 (γ (Real.toNNReal t):ℝ))) (x : ℝ) :
    Tendsto (fun n => finiteVerificationKernel β hβ (dyadicSchedule γ false 0 1 n) b t x)
      atTop (𝓝 (verificationKernel β γ b t x)) := by
  have hr : Real.toNNReal t < 1 := by
    exact_mod_cast (show (Real.toNNReal t:ℝ)<1 by rw [Real.coe_toNNReal _ ht.1.le];exact ht.2)
  have hg := (global_dyadic_gradient_tendstoUniformly β hβ hγ hb _ hr).tendsto_at x
  rw [Real.coe_toNNReal _ ht.1.le] at hg
  exact (hg.mul_const (b.val t x)).sub ((hc.div_const 2).mul (hg.pow 2))

lemma expected_global_dyadic_verificationKernel_tendsto (hW : IsBrownianReal W P)
    (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t≤β)
    (b : Drift K M) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1)
    (hc : Tendsto (fun n => finiteTimeCoefficient (dyadicSchedule γ false 0 1 n) 0 t)
      atTop (𝓝 (γ (Real.toNNReal t):ℝ))) :
    Tendsto (fun n => ∫ ω,finiteVerificationKernel β hβ (dyadicSchedule γ false 0 1 n) b t
      (extend (solution b (brownianPath W ω)) t) ∂P) atTop
      (𝓝 (∫ ω,verificationKernel β γ b t (extend (solution b (brownianPath W ω)) t) ∂P)) := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (M:ℝ)+(β:ℝ)/2)
    (fun n => (finiteVerificationKernel_integrable hW β hβ _ (dyadicSchedule_coeff_bound hb false 0 1 n) b t).aestronglyMeasurable)
    (integrable_const _) (fun n => ae_of_all _ fun ω =>
      finiteVerificationKernel_bound β hβ _ (dyadicSchedule_coeff_bound hb false 0 1 n) b t _)
  exact ae_of_all _ fun ω => global_dyadic_verificationKernel_tendsto β hβ hγ hb b t ht hc _

 

theorem canonical_verification (hW : IsBrownianReal W P) (b : Drift K M)
    (hc : ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x))
    (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t≤β) :
    (∫ ω,terminal β (solution b (brownianPath W ω) ⟨1,by simp⟩) ∂P)-field β γ 0 0 =
      ∫ t in (0:ℝ)..1,∫ ω,verificationKernel β γ b t
        (extend (solution b (brownianPath W ω)) t) ∂P := by
  have hi : Tendsto (fun n => ∫ t in (0:ℝ)..1,∫ ω,
      finiteVerificationKernel β hβ (dyadicSchedule γ false 0 1 n) b t
        (extend (solution b (brownianPath W ω)) t) ∂P) atTop
      (𝓝 (∫ t in (0:ℝ)..1,∫ ω,verificationKernel β γ b t
        (extend (solution b (brownianPath W ω)) t) ∂P)) := by
    have hmeas (n : ℕ) : AEStronglyMeasurable
        (fun t => ∫ ω,finiteVerificationKernel β hβ (dyadicSchedule γ false 0 1 n) b t
          (extend (solution b (brownianPath W ω)) t) ∂P) (volume.restrict (uIoc (0:ℝ) 1)) := by
      rw [uIoc_of_le zero_le_one]
      exact expected_finiteVerificationKernel_aestronglyMeasurable hW β hβ _
        (by simpa only [NNReal.coe_one] using dyadicSchedule_width γ false 0 1 n) b hc
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => (M:ℝ)+(β:ℝ)/2) (Eventually.of_forall hmeas)
      (Eventually.of_forall fun n => ae_of_all _ fun t _ =>
        expected_finiteVerificationKernel_bound hW β hβ _ (dyadicSchedule_coeff_bound hb false 0 1 n) b t)
      intervalIntegrable_const
    have hn : ∀ᵐ t ∂volume,t≠(1:ℝ) := by simp [ae_iff,measure_singleton]
    filter_upwards [global_dyadic_coefficient_tendsto_ae hγ,hn] with t ht hn hmem
    rw [uIoc_of_le zero_le_one] at hmem
    have hti : t∈Ioo (0:ℝ) 1 := ⟨hmem.1,hmem.2.lt_of_ne hn⟩
    exact expected_global_dyadic_verificationKernel_tendsto hW β hβ hγ hb b t hti (ht hti)
  have hf : Tendsto (fun n => recursion β (dyadicSchedule γ false 0 1 n) 0) atTop (𝓝 (field β γ 0 0)) := by
    have hh := (global_dyadic_field_tendstoUniformly β hβ hγ hb 0 (by norm_num)).tendsto_at 0
    simpa only [NNReal.coe_zero,finiteTimeField_start] using hh
  have he : (fun n => (∫ ω,terminal β (solution b (brownianPath W ω) ⟨1,by simp⟩) ∂P)-
      recursion β (dyadicSchedule γ false 0 1 n) 0)=
    (fun n => ∫ t in (0:ℝ)..1,∫ ω,finiteVerificationKernel β hβ (dyadicSchedule γ false 0 1 n) b t
      (extend (solution b (brownianPath W ω)) t) ∂P) := by
    funext n
    exact finite_schedule_verification hW b hc β hβ _ (by simpa only [NNReal.coe_one] using dyadicSchedule_width γ false 0 1 n)
  exact tendsto_nhds_unique (tendsto_const_nhds.sub hf) (he ▸ hi)

end ParisiFinite

end

end OAI
