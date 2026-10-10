import Mathlib
import OAI.Probability.ParisiFinite.InnovationEulerMemLp

namespace OAI

/-! Time Cubic Test. -/

noncomputable section

open MeasureTheory Filter Function Set
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
open ContinuousLinearMap
open scoped Convolution
namespace ParisiPath
open ProbabilityTheory
open scoped BigOperators ENNReal
variable {K M : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

 

structure TimeCubicTest where
  val : ℝ → ℝ → ℝ
  dt : ℝ → ℝ → ℝ
  smooth : ∀ t, ContDiff ℝ 3 (val t)
  c1 : ℝ≥0
  c2 : ℝ≥0
  c3 : ℝ≥0
  ct : ℝ≥0
  bound1 : ∀ t x, ‖deriv (val t) x‖≤c1
  bound2 : ∀ t x, ‖iteratedDeriv 2 (val t) x‖≤c2
  bound3 : ∀ t x, ‖iteratedDeriv 3 (val t) x‖≤c3
  boundT : ∀ t x, ‖dt t x‖≤ct
  measT : Measurable (uncurry dt)
  continuousT : ∀ t,Continuous (dt t)
  jointD1 : ∀ᵐ t ∂volume,t ∈ Icc (0:ℝ) 1 →
    ∀ x,ContinuousAt (fun p : ℝ×ℝ => deriv (val p.1) p.2) (t,x)
  jointD2 : ∀ᵐ t ∂volume,t ∈ Icc (0:ℝ) 1 →
    ∀ x,ContinuousAt (fun p : ℝ×ℝ => iteratedDeriv 2 (val p.1) p.2) (t,x)
  integralT : ∀ a∈Icc (0:ℝ) 1,∀ b∈Icc (0:ℝ) 1,∀ x,
    val b x-val a x=∫ t in a..b,dt t x

def TimeCubicTest.slice (f : TimeCubicTest) (t : ℝ) : CubicTest where
  val := f.val t
  smooth := f.smooth t
  c1 := f.c1
  c2 := f.c2
  c3 := f.c3
  bound1 := f.bound1 t
  bound2 := f.bound2 t
  bound3 := f.bound3 t

lemma expected_kernel_measurable {g : ℝ → ℝ → ℝ}
    (hg : Measurable (uncurry g)) {X : Ω → ℝ} (hX : AEMeasurable X P) [SFinite P] :
    Measurable (fun t => ∫ ω,g t (X ω) ∂P) := by
  have hh : Measurable (fun p : ℝ×Ω => g p.1 (hX.mk X p.2)) :=
    hg.comp (measurable_fst.prodMk (hX.measurable_mk.comp measurable_snd))
  have he : (fun t => ∫ ω,g t (X ω) ∂P)=(fun t => ∫ ω,g t (hX.mk X ω) ∂P) := by
    funext t
    exact integral_congr_ae (hX.ae_eq_mk.fun_comp (g t))
  rw [he]
  exact hh.stronglyMeasurable.integral_prod_right.measurable

lemma expected_kernel_interval_swap {g : ℝ → ℝ → ℝ}
    (hg : Measurable (uncurry g)) {X : Ω → ℝ} (hX : AEMeasurable X P)
    [IsProbabilityMeasure P] {C : ℝ} (hb : ∀ t x,‖g t x‖≤C)
    {a c : ℝ} (hac : a≤c) :
    (∫ ω,(∫ t in a..c,g t (X ω)) ∂P)=∫ t in a..c,∫ ω,g t (X ω) ∂P := by
  have hm : Measurable (fun p : ℝ×Ω => g p.1 (hX.mk X p.2)) :=
    hg.comp (measurable_fst.prodMk (hX.measurable_mk.comp measurable_snd))
  have hi : Integrable (fun p : ℝ×Ω => g p.1 (hX.mk X p.2))
      ((volume.restrict (Ioc a c)).prod P) := by
    apply (integrable_const C).mono' hm.aestronglyMeasurable
    exact ae_of_all _ fun p => hb _ _
  simp only [intervalIntegral.integral_of_le hac]
  calc
    _ = ∫ ω,(∫ t in Ioc a c,g t (hX.mk X ω)) ∂P := by
      apply integral_congr_ae
      filter_upwards [hX.ae_eq_mk] with ω hω
      simp only [hω]
    _ = ∫ t in Ioc a c,∫ ω,g t (hX.mk X ω) ∂P := (integral_integral_swap hi).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun t => integral_congr_ae (hX.ae_eq_mk.fun_comp (g t)).symm

end ParisiPath

namespace ParisiPath
open ProbabilityTheory
open scoped BigOperators ENNReal
variable {K M : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

 
def timeFrozenGenerator (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (b : Drift K M) (f : TimeCubicTest) (n : ℕ) (t : ℝ) : ℝ :=
  expectedFrozenGenerator P W b (f.slice (freeze n t)) n t

def timeGenerator (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (b : Drift K M) (f : TimeCubicTest) (t : ℝ) : ℝ :=
  expectedGenerator P W b (f.slice t) t

 
def timeFrozenDerivative (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (b : Drift K M) (f : TimeCubicTest) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ ω,f.dt t (euler b (brownianPath W ω) n (⌊t*(n+1:ℕ)⌋₊+1)) ∂P

def timeDerivative (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (b : Drift K M) (f : TimeCubicTest) (t : ℝ) : ℝ :=
  ∫ ω,f.dt t (extend (solution b (brownianPath W ω)) t) ∂P

lemma timeFrozenGenerator_measurable (b : Drift K M) (f : TimeCubicTest) (n : ℕ) :
    Measurable (timeFrozenGenerator P W b f n) :=
  (measurable_of_countable (f:=fun k : ℕ => ∫ ω,generator (f.slice (grid n k)) b (grid n k)
    (euler b (brownianPath W ω) n k) ∂P)).comp (by fun_prop)

lemma timeFrozenGenerator_bound (hW : IsBrownianReal W P) (b : Drift K M)
    (f : TimeCubicTest) (n : ℕ) (t : ℝ) :
    ‖timeFrozenGenerator P W b f n t‖≤(f.c1:ℝ)*(M:ℝ)+(f.c2:ℝ)/2 :=
  expectedFrozenGenerator_bound hW b (f.slice (freeze n t)) n t

lemma timeFrozenDerivative_measurable (hW : IsBrownianReal W P) (b : Drift K M)
    (f : TimeCubicTest) (n : ℕ) : Measurable (timeFrozenDerivative P W b f n) := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hm : Measurable (fun p : ℕ×ℝ => ∫ ω,f.dt p.2
      (euler b (brownianPath W ω) n (p.1+1)) ∂P) := by
    apply measurable_from_prod_countable_right
    intro k
    exact expected_kernel_measurable f.measT
      (aemeasurable_euler b (brownianPath W) (brownianPath_aemeasurable_eval hW) n (k+1))
  exact hm.comp ((by fun_prop : Measurable (fun t : ℝ => ⌊t*(n+1:ℕ)⌋₊)).prodMk measurable_id)

lemma timeFrozenDerivative_bound (hW : IsBrownianReal W P) (b : Drift K M)
    (f : TimeCubicTest) (n : ℕ) (t : ℝ) : ‖timeFrozenDerivative P W b f n t‖≤f.ct := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact (norm_integral_le_of_norm_le_const (ae_of_all _ fun ω => f.boundT t _)).trans_eq (by simp)

lemma timeFrozenGenerator_tendsto (hW : IsBrownianReal W P) (b : Drift K M)
    (f : TimeCubicTest)
    (hc : ∀ᵐ t ∂volume,t ∈ Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x)) :
    ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → Tendsto (fun n => timeFrozenGenerator P W b f n t)
      atTop (𝓝 (timeGenerator P W b f t)) := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  filter_upwards [hc,f.jointD1,f.jointD2] with t ht hd1 hd2 hmem
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (f.c1:ℝ)*(M:ℝ)+(f.c2:ℝ)/2)
    (fun n => (generator_frozen_aemeasurable hW b (f.slice (freeze n t)) n t).aestronglyMeasurable)
    (integrable_const _) (fun n => ae_of_all _ fun ω => generator_bound _ b _ _)
  exact ae_of_all _ fun ω => by
    have hx := frozenEuler_tendsto b (brownianPath W ω)
      (reference_ae_continuous_of_joint b hc _) hmem
    have hp := (freeze_tendsto hmem.1).prodMk_nhds hx
    have hb := (ht hmem _).tendsto.comp hp
    exact (((hd1 hmem _).tendsto.comp hp).mul hb).add
      (((hd2 hmem _).tendsto.comp hp).const_mul (1/2:ℝ))

lemma nextFrozenEuler_tendsto (b : Drift K M) (X : Path)
    (hc : ∀ᵐ t ∂volume,t ∈ Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x))
    {t : ℝ} (ht : t∈Ico (0:ℝ) 1) :
    Tendsto (fun n => euler b X n (⌊t*(n+1:ℕ)⌋₊+1)) atTop
      (𝓝 (extend (solution b X) t)) := by
  have hk (n : ℕ) : ⌊t*(n+1:ℕ)⌋₊+1≤n+1 := by
    apply Nat.succ_le_iff.mpr
    apply (Nat.floor_lt (mul_nonneg ht.1 (by positivity))).mpr
    simpa only [one_mul] using mul_lt_mul_of_pos_right ht.2 (by positivity : (0:ℝ)<(n+1:ℕ))
  have hg : Tendsto (fun n => grid n (⌊t*(n+1:ℕ)⌋₊+1)) atTop (𝓝 t) := by
    simp_rw [grid_succ]
    simpa only [add_zero,freeze] using (freeze_tendsto ht.1).add mesh_tendsto_zero
  have h0 : Tendsto (fun n => euler b X n (⌊t*(n+1:ℕ)⌋₊+1)-
      extend (solution b X) (grid n (⌊t*(n+1:ℕ)⌋₊+1))) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => euler_error_bound b X n _ (hk n))
    simpa only [zero_mul] using (totalResidual_tendsto_zero b (solution b X)
      (reference_ae_continuous_of_joint b hc _)).mul_const (Real.exp (K:ℝ))
  have h1 := (continuous_extend (solution b X)).continuousAt.tendsto.comp hg
  simpa only [Function.comp_def,sub_add_cancel,zero_add] using h0.add h1

lemma timeFrozenDerivative_tendsto (hW : IsBrownianReal W P) (b : Drift K M)
    (f : TimeCubicTest)
    (hc : ∀ᵐ t ∂volume,t ∈ Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x))
    {t : ℝ} (ht : t∈Ico (0:ℝ) 1) :
    Tendsto (fun n => timeFrozenDerivative P W b f n t) atTop (𝓝 (timeDerivative P W b f t)) := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (f.ct:ℝ))
    (fun n => ((f.continuousT t).measurable.comp_aemeasurable
      (aemeasurable_euler b (brownianPath W) (brownianPath_aemeasurable_eval hW)
        n (⌊t*(n+1:ℕ)⌋₊+1))).aestronglyMeasurable)
    (integrable_const _) (fun n => ae_of_all _ fun ω => f.boundT t _)
  exact ae_of_all _ fun ω => (f.continuousT t).continuousAt.tendsto.comp
    (nextFrozenEuler_tendsto b (brownianPath W ω) hc ht)

lemma timeFrozenGenerator_intervalIntegrable (hW : IsBrownianReal W P)
    (b : Drift K M) (f : TimeCubicTest) (n : ℕ) (a c : ℝ) :
    IntervalIntegrable (timeFrozenGenerator P W b f n) volume a c := by
  apply (intervalIntegrable_const (c := (f.c1:ℝ)*(M:ℝ)+(f.c2:ℝ)/2)).mono_fun'
    (timeFrozenGenerator_measurable b f n).aestronglyMeasurable
  exact Eventually.of_forall fun t => timeFrozenGenerator_bound hW b f n t

lemma timeFrozenDerivative_intervalIntegrable (hW : IsBrownianReal W P)
    (b : Drift K M) (f : TimeCubicTest) (n : ℕ) (a c : ℝ) :
    IntervalIntegrable (timeFrozenDerivative P W b f n) volume a c := by
  apply (intervalIntegrable_const (c := (f.ct:ℝ))).mono_fun'
    (timeFrozenDerivative_measurable hW b f n).aestronglyMeasurable
  exact Eventually.of_forall fun t => timeFrozenDerivative_bound hW b f n t

lemma timeFrozenGenerator_integral_tendsto (hW : IsBrownianReal W P)
    (b : Drift K M) (f : TimeCubicTest)
    (hc : ∀ᵐ t ∂volume,t ∈ Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x)) :
    Tendsto (fun n => ∫ t in (0:ℝ)..1,timeFrozenGenerator P W b f n t) atTop
      (𝓝 (∫ t in (0:ℝ)..1,timeGenerator P W b f t)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => (f.c1:ℝ)*(M:ℝ)+(f.c2:ℝ)/2)
    (Eventually.of_forall fun n => (timeFrozenGenerator_measurable b f n).aestronglyMeasurable.restrict)
    (Eventually.of_forall fun n => ae_of_all _ fun t _ => timeFrozenGenerator_bound hW b f n t)
    (intervalIntegrable_const) ?_
  filter_upwards [timeFrozenGenerator_tendsto hW b f hc] with t ht hmem
  rw [uIoc_of_le zero_le_one] at hmem
  exact ht ⟨hmem.1.le,hmem.2⟩

lemma timeFrozenDerivative_integral_tendsto (hW : IsBrownianReal W P)
    (b : Drift K M) (f : TimeCubicTest)
    (hc : ∀ᵐ t ∂volume,t ∈ Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x)) :
    Tendsto (fun n => ∫ t in (0:ℝ)..1,timeFrozenDerivative P W b f n t) atTop
      (𝓝 (∫ t in (0:ℝ)..1,timeDerivative P W b f t)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => (f.ct:ℝ))
    (Eventually.of_forall fun n => (timeFrozenDerivative_measurable hW b f n).aestronglyMeasurable.restrict)
    (Eventually.of_forall fun n => ae_of_all _ fun t _ => timeFrozenDerivative_bound hW b f n t)
    (intervalIntegrable_const) ?_
  have hn : ∀ᵐ t ∂volume,t≠(1:ℝ) := by simp [ae_iff,measure_singleton]
  filter_upwards [hn] with t ht hmem
  rw [uIoc_of_le zero_le_one] at hmem
  exact timeFrozenDerivative_tendsto hW b f hc ⟨hmem.1.le,hmem.2.lt_of_ne ht⟩

end ParisiPath

namespace ParisiPath
open ProbabilityTheory
open scoped BigOperators ENNReal
variable {K M : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

lemma brownianEuler_integrable_at (hW : IsBrownianReal W P) (b : Drift K M)
    (n k : ℕ) (hk : k≤n+1) : Integrable (fun ω => euler b (brownianPath W ω) n k) P := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  apply (innovationEuler_memLp (standardStep_hasLaw hW (by norm_num : (0:ℝ≥0)<1) n)
    b 1 n k (p:=1) (by norm_num) |>.integrable le_rfl).congr
  exact (innovationEuler_eq_euler hW b n).mono fun ω hω => hω k hk

lemma brownianEuler_generator_step (hW : IsBrownianReal W P) (b : Drift K M)
    (f : CubicTest) (n k : ℕ) (hk : k≤n) :
    ‖((∫ ω,f.val (euler b (brownianPath W ω) n (k+1)) ∂P)-
      (∫ ω,f.val (euler b (brownianPath W ω) n k) ∂P))-
      mesh n*(∫ ω,generator f b (grid n k) (euler b (brownianPath W ω) n k) ∂P)‖≤
      (mesh n*Real.sqrt (mesh n))*
        ((f.c3:ℝ)/6*thirdMomentBound M+(f.c2:ℝ)*(M:ℝ)^2/2) := by
  have hh := innovationEuler_generator_step (standardStep_independent hW 1 n)
    (standardStep_hasLaw hW (by norm_num : (0:ℝ≥0)<1) n) b f (by norm_num : (1:ℝ≥0)≤1) n k
  simp only [NNReal.coe_one,one_mul] at hh
  have he (j : ℕ) (hj : j≤n+1) (g : ℝ → ℝ) :
      (∫ ω,g (innovationEuler b 1 n j (fun l => standardStep W 1 n l ω)) ∂P)=
        ∫ ω,g (euler b (brownianPath W ω) n j) ∂P :=
    integral_congr_ae ((innovationEuler_eq_euler hW b n).mono fun ω hω => congrArg g (hω j hj))
  rw [he (k+1) (by omega) f.val,he k (by omega) f.val,he k (by omega) (generator f b (grid n k))] at hh
  exact hh

lemma timeFrozenGenerator_cell_integral (_hW : IsBrownianReal W P)
    (b : Drift K M) (f : TimeCubicTest) (n k : ℕ) :
    (∫ t in (grid n k)..(grid n (k+1)),timeFrozenGenerator P W b f n t)=
      mesh n*(∫ ω,generator (f.slice (grid n k)) b (grid n k)
        (euler b (brownianPath W ω) n k) ∂P) := by
  have hnot : ∀ᵐ s ∂volume,s≠grid n (k+1) := by simp [ae_iff,measure_singleton]
  calc
    _ = ∫ _ in (grid n k)..(grid n (k+1)),
        (∫ ω,generator (f.slice (grid n k)) b (grid n k)
          (euler b (brownianPath W ω) n k) ∂P) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hnot] with t ht hmem
      rw [uIoc_of_le (grid_mono n (Nat.le_succ k))] at hmem
      have hcell : t∈Ico (grid n k) (grid n (k+1)) := ⟨hmem.1.le,hmem.2.lt_of_ne ht⟩
      simp only [timeFrozenGenerator,expectedFrozenGenerator,frozenEuler,freeze_on_cell n k hcell,
        freeze_index_on_cell n k hcell]
    _ = _ := by rw [intervalIntegral.integral_const,grid_succ];simp

lemma timeFrozenDerivative_cell_integral (hW : IsBrownianReal W P)
    (b : Drift K M) (f : TimeCubicTest) (n k : ℕ) (hk : k≤n) :
    (∫ t in (grid n k)..(grid n (k+1)),timeFrozenDerivative P W b f n t)=
      (∫ ω,f.val (grid n (k+1)) (euler b (brownianPath W ω) n (k+1)) ∂P)-
        (∫ ω,f.val (grid n k) (euler b (brownianPath W ω) n (k+1)) ∂P) := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hnot : ∀ᵐ s ∂volume,s≠grid n (k+1) := by simp [ae_iff,measure_singleton]
  calc
    _ = ∫ t in (grid n k)..(grid n (k+1)),
        (∫ ω,f.dt t (euler b (brownianPath W ω) n (k+1)) ∂P) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hnot] with t ht hmem
      rw [uIoc_of_le (grid_mono n (Nat.le_succ k))] at hmem
      have hcell : t∈Ico (grid n k) (grid n (k+1)) := ⟨hmem.1.le,hmem.2.lt_of_ne ht⟩
      simp only [timeFrozenDerivative,freeze_index_on_cell n k hcell]
    _ = ∫ ω,(∫ t in (grid n k)..(grid n (k+1)),
        f.dt t (euler b (brownianPath W ω) n (k+1))) ∂P :=
      (expected_kernel_interval_swap f.measT
        (aemeasurable_euler b (brownianPath W) (brownianPath_aemeasurable_eval hW) n (k+1))
        f.boundT (grid_mono n (Nat.le_succ k))).symm
    _ = ∫ ω,(f.val (grid n (k+1)) (euler b (brownianPath W ω) n (k+1))-
        f.val (grid n k) (euler b (brownianPath W ω) n (k+1))) ∂P := by
      apply integral_congr_ae
      exact ae_of_all _ fun ω => (f.integralT _ (grid_mem n k (by omega))
        _ (grid_mem n (k+1) (by omega)) _).symm
    _ = _ := integral_sub ((f.slice _).integrable_comp (brownianEuler_integrable_at hW b n (k+1) (by omega)))
      ((f.slice _).integrable_comp (brownianEuler_integrable_at hW b n (k+1) (by omega)))

lemma timeEuler_weak_step (hW : IsBrownianReal W P)
    (b : Drift K M) (f : TimeCubicTest) (n k : ℕ) (hk : k≤n) :
    ‖((∫ ω,f.val (grid n (k+1)) (euler b (brownianPath W ω) n (k+1)) ∂P)-
      (∫ ω,f.val (grid n k) (euler b (brownianPath W ω) n k) ∂P))-
      ((∫ t in (grid n k)..(grid n (k+1)),timeFrozenGenerator P W b f n t)+
        (∫ t in (grid n k)..(grid n (k+1)),timeFrozenDerivative P W b f n t))‖≤
      (mesh n*Real.sqrt (mesh n))*
        ((f.c3:ℝ)/6*thirdMomentBound M+(f.c2:ℝ)*(M:ℝ)^2/2) := by
  rw [timeFrozenGenerator_cell_integral hW b f n k,timeFrozenDerivative_cell_integral hW b f n k hk]
  convert! brownianEuler_generator_step hW b (f.slice (grid n k)) n k hk using 1
  congr 1
  dsimp only [TimeCubicTest.slice]
  ring

lemma timeEuler_weak_error (hW : IsBrownianReal W P)
    (b : Drift K M) (f : TimeCubicTest) (n : ℕ) :
    ‖(∫ ω,f.val 1 (euler b (brownianPath W ω) n (n+1)) ∂P)-f.val 0 0-
      ((∫ t in (0:ℝ)..1,timeFrozenGenerator P W b f n t)+
        (∫ t in (0:ℝ)..1,timeFrozenDerivative P W b f n t))‖≤
        Real.sqrt (mesh n)*((f.c3:ℝ)/6*thirdMomentBound M+(f.c2:ℝ)*(M:ℝ)^2/2) := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  let A (k : ℕ) := ∫ ω,f.val (grid n k) (euler b (brownianPath W ω) n k) ∂P
  let C (k : ℕ) := (∫ t in (grid n k)..(grid n (k+1)),timeFrozenGenerator P W b f n t)+
    (∫ t in (grid n k)..(grid n (k+1)),timeFrozenDerivative P W b f n t)
  have h0 : A 0=f.val 0 0 := by
    dsimp only [A]
    rw [grid_zero]
    calc
      _ = ∫ _ : Ω,f.val 0 0 ∂P := by
        apply integral_congr_ae
        filter_upwards [innovationEuler_eq_euler hW b n] with ω hω
        rw [←hω 0 (by omega)]
        rfl
      _ = _ := by simp
  have hC : (∑ k∈Finset.range (n+1),C k)=
      (∫ t in (0:ℝ)..1,timeFrozenGenerator P W b f n t)+
        (∫ t in (0:ℝ)..1,timeFrozenDerivative P W b f n t) := by
    dsimp only [C]
    rw [Finset.sum_add_distrib,
      intervalIntegral.sum_integral_adjacent_intervals
        (fun k _ => timeFrozenGenerator_intervalIntegrable hW b f n _ _),
      intervalIntegral.sum_integral_adjacent_intervals
        (fun k _ => timeFrozenDerivative_intervalIntegrable hW b f n _ _),grid_zero,grid_end]
  have hsum : A (n+1)-A 0-(∑ k∈Finset.range (n+1),C k)=
      ∑ k∈Finset.range (n+1),(A (k+1)-A k-C k) := by
    rw [Finset.sum_sub_distrib,Finset.sum_range_sub A]
  have hb : ‖A (n+1)-A 0-(∑ k∈Finset.range (n+1),C k)‖≤
      (n+1:ℕ)*(mesh n*Real.sqrt (mesh n))*
        ((f.c3:ℝ)/6*thirdMomentBound M+(f.c2:ℝ)*(M:ℝ)^2/2) := by
    rw [hsum]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun k hk =>
      timeEuler_weak_step hW b f n k (by have := Finset.mem_range.mp hk;omega))).trans_eq (by simp;ring))
  rw [h0,hC] at hb
  dsimp only [A] at hb
  rw [grid_end] at hb
  convert! hb using 1
  rw [←mul_assoc,show (n+1:ℕ)*mesh n=1 from grid_end n,one_mul]

 

theorem brownian_solution_time_generator_identity (hW : IsBrownianReal W P)
    (b : Drift K M) (f : TimeCubicTest)
    (hc : ∀ᵐ t ∂volume,t ∈ Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x)) :
    (∫ ω,f.val 1 (solution b (brownianPath W ω) ⟨1,by simp⟩) ∂P)-f.val 0 0=
      (∫ t in (0:ℝ)..1,timeGenerator P W b f t)+(∫ t in (0:ℝ)..1,timeDerivative P W b f t) := by
  have hl := (brownianEuler_expected_test_tendsto hW b (f.slice 1) hc).sub_const (f.val 0 0)
  have hr := (timeFrozenGenerator_integral_tendsto hW b f hc).add
    (timeFrozenDerivative_integral_tendsto hW b f hc)
  have hz : Tendsto (fun n => (∫ ω,f.val 1 (euler b (brownianPath W ω) n (n+1)) ∂P)-f.val 0 0-
      ((∫ t in (0:ℝ)..1,timeFrozenGenerator P W b f n t)+
        (∫ t in (0:ℝ)..1,timeFrozenDerivative P W b f n t))) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (timeEuler_weak_error hW b f)
    simpa only [Real.sqrt_zero,zero_mul,Function.comp_def] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp mesh_tendsto_zero).mul_const
        ((f.c3:ℝ)/6*thirdMomentBound M+(f.c2:ℝ)*(M:ℝ)^2/2)
  exact sub_eq_zero.mp (tendsto_nhds_unique (hl.sub hr) hz)

end ParisiPath

namespace ParisiPath
open ProbabilityTheory
open scoped BigOperators ENNReal

 

structure TimeQuadraticTest where
  val : ℝ → ℝ → ℝ
  d1 : ℝ → ℝ → ℝ
  d2 : ℝ → ℝ → ℝ
  dt : ℝ → ℝ → ℝ
  hasD1 : ∀ t x,HasDerivAt (val t) (d1 t x) x
  hasD2 : ∀ t x,HasDerivAt (d1 t) (d2 t x) x
  continuousD2 : ∀ t,Continuous (d2 t)
  c1 : ℝ≥0
  c2 : ℝ≥0
  ct : ℝ≥0
  bound1 : ∀ t x,‖d1 t x‖≤c1
  bound2 : ∀ t x,‖d2 t x‖≤c2
  boundT : ∀ t x,‖dt t x‖≤ct
  measT : Measurable (uncurry dt)
  continuousT : ∀ t,Continuous (dt t)
  jointD1 : ∀ᵐ t ∂volume,t ∈ Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry d1) (t,x)
  jointD2 : ∀ᵐ t ∂volume,t ∈ Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry d2) (t,x)
  integralT : ∀ a∈Icc (0:ℝ) 1,∀ b∈Icc (0:ℝ) 1,∀ x,
    val b x-val a x=∫ t in a..b,dt t x

def TimeQuadraticTest.slice (f : TimeQuadraticTest) (t : ℝ) : QuadraticTest where
  val := f.val t
  d1 := f.d1 t
  d2 := f.d2 t
  hasD1 := f.hasD1 t
  hasD2 := f.hasD2 t
  continuousD2 := f.continuousD2 t
  c1 := f.c1
  c2 := f.c2
  bound1 := f.bound1 t
  bound2 := f.bound2 t

lemma smoothConvolution_joint_continuousAt (φ : ContDiffBump (0:ℝ)) {g : ℝ → ℝ → ℝ}
    (hcont : ∀ t,Continuous (g t)) {C : ℝ≥0} (hb : ∀ t x,‖g t x‖≤C)
    {t x : ℝ} (ht : ∀ y,ContinuousAt (uncurry g) (t,y)) :
    ContinuousAt (fun p : ℝ×ℝ => smoothConvolution φ (g p.1) p.2) (t,x) := by
  change ContinuousAt (fun p : ℝ×ℝ => ∫ z,φ.normed volume z*g p.1 (p.2-z)) (t,x)
  apply continuousAt_of_dominated
    (F := fun p : ℝ×ℝ => fun z => φ.normed volume z*g p.1 (p.2-z))
    (bound := fun z => φ.normed volume z*(C:ℝ))
    (Eventually.of_forall fun p => (φ.continuous_normed.mul
      ((hcont p.1).comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
    (Eventually.of_forall fun p => ae_of_all _ fun z => ?_)
    (φ.integrable_normed.mul_const _) (ae_of_all _ fun z => ?_)
  · rw [norm_mul,Real.norm_of_nonneg (φ.nonneg_normed z)]
    exact mul_le_mul_of_nonneg_left (hb _ _) (φ.nonneg_normed z)
  · have hh : ContinuousAt (fun p : ℝ×ℝ => g p.1 (p.2-z)) (t,x) :=
      ContinuousAt.comp (g := uncurry g) (f := fun p : ℝ×ℝ => (p.1,p.2-z))
        (ht (x-z))
        (continuous_fst.continuousAt.prodMk (continuous_snd.continuousAt.sub_const z))
    exact continuousAt_const.mul hh

lemma smoothConvolution_joint_measurable (φ : ContDiffBump (0:ℝ)) {g : ℝ → ℝ → ℝ}
    (hg : Measurable (uncurry g)) :
    Measurable (fun p : ℝ×ℝ => smoothConvolution φ (g p.1) p.2) := by
  have hh : Measurable (fun p : (ℝ×ℝ)×ℝ => φ.normed volume p.2*g p.1.1 (p.1.2-p.2)) :=
    (φ.continuous_normed.measurable.comp measurable_snd).mul
      (hg.comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).sub measurable_snd)))
  exact hh.stronglyMeasurable.integral_prod_right.measurable

lemma smoothConvolution_time_integral (φ : ContDiffBump (0:ℝ)) (f : TimeQuadraticTest)
    {a c : ℝ} (ha : a∈Icc (0:ℝ) 1) (hc : c∈Icc (0:ℝ) 1) (x : ℝ) :
    smoothConvolution φ (f.val c) x-smoothConvolution φ (f.val a) x=
      ∫ t in a..c,smoothConvolution φ (f.dt t) x := by
  have hm : Measurable (fun p : ℝ×ℝ => φ.normed volume p.2*f.dt p.1 (x-p.2)) :=
    (φ.continuous_normed.measurable.comp measurable_snd).mul
      (f.measT.comp (measurable_fst.prodMk (measurable_const.sub measurable_snd)))
  let : IsFiniteMeasure (volume.restrict (uIoc a c)) := by
    change IsFiniteMeasure (volume.restrict (Ioc (min a c) (max a c)))
    infer_instance
  have hi : Integrable (fun p : ℝ×ℝ => φ.normed volume p.2*f.dt p.1 (x-p.2))
      ((volume.restrict (uIoc a c)).prod volume) := by
    apply ((integrable_const (f.ct:ℝ)).mul_prod φ.integrable_normed).mono'
      hm.aestronglyMeasurable
    exact ae_of_all _ fun p => by
      rw [norm_mul,Real.norm_of_nonneg (φ.nonneg_normed p.2)]
      exact (mul_le_mul_of_nonneg_left (f.boundT _ _) (φ.nonneg_normed p.2)).trans_eq (mul_comm _ _)
  calc
    _ = ∫ z,φ.normed volume z*(f.val c (x-z)-f.val a (x-z)) := by
      rw [smoothConvolution_eq,smoothConvolution_eq,
        ←integral_sub
          (show Integrable (fun z => φ.normed volume z*f.val c (x-z)) volume from
            smoothConvolution_integrable φ (f.slice c).continuous x)
          (show Integrable (fun z => φ.normed volume z*f.val a (x-z)) volume from
            smoothConvolution_integrable φ (f.slice a).continuous x)]
      congr 1
      funext z
      ring
    _ = ∫ z,(∫ t in a..c,φ.normed volume z*f.dt t (x-z)) := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        dsimp only
        rw [f.integralT a ha c hc,intervalIntegral.integral_const_mul]
    _ = _ := (intervalIntegral_integral_swap hi).symm

def TimeQuadraticTest.mollify (f : TimeQuadraticTest) (φ : ContDiffBump (0:ℝ)) : TimeCubicTest where
  val := fun t => smoothConvolution φ (f.val t)
  dt := fun t => smoothConvolution φ (f.dt t)
  smooth := fun t => smoothConvolution_smooth φ (f.slice t).continuous
  c1 := f.c1
  c2 := f.c2
  c3 := ⟨(∫ z,‖deriv (φ.normed volume) z‖)*(f.c2:ℝ),by positivity⟩
  ct := f.ct
  bound1 := fun t x => (f.slice t).mollify φ |>.bound1 x
  bound2 := fun t x => (f.slice t).mollify φ |>.bound2 x
  bound3 := fun t x => (f.slice t).mollify φ |>.bound3 x
  boundT := fun t x => smoothConvolution_bound φ (f.continuousT t) (f.boundT t) x
  measT := smoothConvolution_joint_measurable φ f.measT
  continuousT := fun t => (smoothConvolution_smooth φ (f.continuousT t)).continuous
  jointD1 := by
    filter_upwards [f.jointD1] with t ht hmem x
    have he : (fun p : ℝ×ℝ => deriv (smoothConvolution φ (f.val p.1)) p.2)=
        fun p : ℝ×ℝ => smoothConvolution φ (f.d1 p.1) p.2 := by
      funext p
      exact congrFun (smoothConvolution_d1 φ (f.slice p.1)) p.2
    rw [he]
    exact smoothConvolution_joint_continuousAt φ (fun s => (f.slice s).continuous_d1)
      f.bound1 (ht hmem)
  jointD2 := by
    filter_upwards [f.jointD2] with t ht hmem x
    have he : (fun p : ℝ×ℝ => iteratedDeriv 2 (smoothConvolution φ (f.val p.1)) p.2)=
        fun p : ℝ×ℝ => smoothConvolution φ (f.d2 p.1) p.2 := by
      funext p
      exact congrFun (smoothConvolution_d2 φ (f.slice p.1)) p.2
    rw [he]
    exact smoothConvolution_joint_continuousAt φ f.continuousD2 f.bound2 (ht hmem)
  integralT := fun _ ha _ hc x => smoothConvolution_time_integral φ f ha hc x

end ParisiPath

namespace ParisiPath
open ProbabilityTheory
open scoped BigOperators ENNReal
variable {K M : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

lemma timeGenerator_aestronglyMeasurable (hW : IsBrownianReal W P)
    (b : Drift K M) (f : TimeCubicTest)
    (hc : ∀ᵐ t ∂volume,t ∈ Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x)) :
    AEStronglyMeasurable (timeGenerator P W b f) (volume.restrict (Ioc (0:ℝ) 1)) := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (timeFrozenGenerator_measurable (P:=P) (W:=W) b f n).aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_of_ae (timeFrozenGenerator_tendsto hW b f hc),
    ae_restrict_mem measurableSet_Ioc] with t ht hmem
  exact ht ⟨hmem.1.le,hmem.2⟩

lemma timeDerivative_aestronglyMeasurable (hW : IsBrownianReal W P)
    (b : Drift K M) (f : TimeCubicTest)
    (hc : ∀ᵐ t ∂volume,t ∈ Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x)) :
    AEStronglyMeasurable (timeDerivative P W b f) (volume.restrict (Ioc (0:ℝ) 1)) := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (timeFrozenDerivative_measurable hW b f n).aestronglyMeasurable.restrict)
  have hn : ∀ᵐ t ∂volume,t≠(1:ℝ) := by simp [ae_iff,measure_singleton]
  filter_upwards [ae_restrict_of_ae hn,ae_restrict_mem measurableSet_Ioc] with t ht hmem
  exact timeFrozenDerivative_tendsto hW b f hc ⟨hmem.1.le,hmem.2.lt_of_ne ht⟩

lemma timeDerivative_bound (hW : IsBrownianReal W P) (b : Drift K M)
    (f : TimeCubicTest) (t : ℝ) : ‖timeDerivative P W b f t‖≤f.ct := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact (norm_integral_le_of_norm_le_const (ae_of_all _ fun ω => f.boundT t _)).trans_eq (by simp)

def timeGeneratorC2 (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (b : Drift K M) (f : TimeQuadraticTest) (t : ℝ) : ℝ :=
  expectedGeneratorC2 P W b (f.slice t) t

def timeDerivativeC2 (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (b : Drift K M) (f : TimeQuadraticTest) (t : ℝ) : ℝ :=
  ∫ ω,f.dt t (extend (solution b (brownianPath W ω)) t) ∂P

lemma mollify_timeGenerator_tendsto (hW : IsBrownianReal W P)
    (b : Drift K M) (f : TimeQuadraticTest) (t : ℝ) :
    Tendsto (fun n => timeGenerator P W b (f.mollify (shrinkingBump n)) t) atTop
      (𝓝 (timeGeneratorC2 P W b f t)) :=
  mollify_expectedGenerator_tendsto hW b (f.slice t) t

lemma mollify_timeDerivative_tendsto (hW : IsBrownianReal W P)
    (b : Drift K M) (f : TimeQuadraticTest) (t : ℝ) :
    Tendsto (fun n => timeDerivative P W b (f.mollify (shrinkingBump n)) t) atTop
      (𝓝 (timeDerivativeC2 P W b f t)) := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hX := aemeasurable_solution_eval b (brownianPath W) (brownianPath_aemeasurable_eval hW)
    (projIcc 0 1 zero_le_one t)
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (f.ct:ℝ))
    (fun n => (((f.mollify (shrinkingBump n)).continuousT t).measurable.comp_aemeasurable hX).aestronglyMeasurable)
    (integrable_const _) (fun n => ae_of_all _ fun ω => (f.mollify (shrinkingBump n)).boundT t _)
  exact ae_of_all _ fun ω => smoothConvolution_tendsto (f.continuousT t) _

lemma mollify_timeGenerator_integral_tendsto (hW : IsBrownianReal W P)
    (b : Drift K M) (f : TimeQuadraticTest)
    (hc : ∀ᵐ t ∂volume,t ∈ Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x)) :
    Tendsto (fun n => ∫ t in (0:ℝ)..1,timeGenerator P W b (f.mollify (shrinkingBump n)) t)
      atTop (𝓝 (∫ t in (0:ℝ)..1,timeGeneratorC2 P W b f t)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => (f.c1:ℝ)*(M:ℝ)+(f.c2:ℝ)/2)
    (Eventually.of_forall fun n => ?_)
    (Eventually.of_forall fun n => ae_of_all _ fun t _ =>
      expectedGenerator_bound hW b ((f.mollify (shrinkingBump n)).slice t) t)
    (intervalIntegrable_const) (ae_of_all _ fun t _ => mollify_timeGenerator_tendsto hW b f t)
  rw [uIoc_of_le zero_le_one]
  exact timeGenerator_aestronglyMeasurable hW b _ hc

lemma mollify_timeDerivative_integral_tendsto (hW : IsBrownianReal W P)
    (b : Drift K M) (f : TimeQuadraticTest)
    (hc : ∀ᵐ t ∂volume,t ∈ Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x)) :
    Tendsto (fun n => ∫ t in (0:ℝ)..1,timeDerivative P W b (f.mollify (shrinkingBump n)) t)
      atTop (𝓝 (∫ t in (0:ℝ)..1,timeDerivativeC2 P W b f t)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => (f.ct:ℝ))
    (Eventually.of_forall fun n => ?_)
    (Eventually.of_forall fun n => ae_of_all _ fun t _ => timeDerivative_bound hW b _ t)
    (intervalIntegrable_const) (ae_of_all _ fun t _ => mollify_timeDerivative_tendsto hW b f t)
  rw [uIoc_of_le zero_le_one]
  exact timeDerivative_aestronglyMeasurable hW b _ hc

 

theorem brownian_solution_time_generator_identity_C2 (hW : IsBrownianReal W P)
    (b : Drift K M) (f : TimeQuadraticTest)
    (hc : ∀ᵐ t ∂volume,t ∈ Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x)) :
    (∫ ω,f.val 1 (solution b (brownianPath W ω) ⟨1,by simp⟩) ∂P)-f.val 0 0=
      (∫ t in (0:ℝ)..1,timeGeneratorC2 P W b f t)+(∫ t in (0:ℝ)..1,timeDerivativeC2 P W b f t) := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hv := mollify_expected_test_tendsto (f.slice 1) (brownian_solution_integrable hW b ⟨1,by simp⟩)
  have h0 := smoothConvolution_tendsto (f.slice 0).continuous 0
  have he : (fun n => (∫ ω,(f.mollify (shrinkingBump n)).val 1
      (solution b (brownianPath W ω) ⟨1,by simp⟩) ∂P)-(f.mollify (shrinkingBump n)).val 0 0)=
      (fun n => (∫ t in (0:ℝ)..1,timeGenerator P W b (f.mollify (shrinkingBump n)) t)+
        (∫ t in (0:ℝ)..1,timeDerivative P W b (f.mollify (shrinkingBump n)) t)) := by
    funext n
    exact brownian_solution_time_generator_identity hW b _ hc
  have hr := (mollify_timeGenerator_integral_tendsto hW b f hc).add
    (mollify_timeDerivative_integral_tendsto hW b f hc)
  exact tendsto_nhds_unique (hv.sub h0) (he ▸ hr)

end ParisiPath

end

end OAI
