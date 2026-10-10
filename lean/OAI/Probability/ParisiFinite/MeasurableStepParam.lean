import Mathlib
import OAI.Probability.ParisiFinite.ScaledTimeMem

namespace OAI

/-! Measurable Step Param. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Filter Function
open scoped Topology NNReal ENNReal
namespace ParisiFinite

lemma measurable_step_param {α : Type*} [MeasurableSpace α]
    {a s x : α → ℝ} {f : α → ℝ → ℝ}
    (ha : Measurable a) (hs : Measurable s) (hx : Measurable x)
    (hf : Measurable (uncurry f)) :
    Measurable (fun p => step (a p) (s p) (f p) (x p)) := by
  have hm : Measurable (fun q : α × ℝ => f q.1 (x q.1 + s q.1 * q.2)) :=
    hf.comp (measurable_fst.prodMk ((hx.comp measurable_fst).add
      ((hs.comp measurable_fst).mul measurable_snd)))
  have hi : Measurable (fun p => ∫ z, f p (x p+s p*z) ∂gaussianReal 0 1) :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  have he : Measurable (fun p => ∫ z, Real.exp (a p*f p (x p+s p*z)) ∂gaussianReal 0 1) :=
    ((ha.comp measurable_fst).mul hm).exp.stronglyMeasurable.integral_prod_right'.measurable
  exact Measurable.ite (measurableSet_eq_fun ha measurable_const) hi (he.log.div ha)

lemma measurable_evolve_ofFn {α : Type*} [MeasurableSpace α] (n : ℕ)
    (a d : Fin n → α → ℝ≥0) (ha : ∀ i,Measurable (a i)) (hd : ∀ i,Measurable (d i))
    {f : α → ℝ → ℝ} (hf : Measurable (uncurry f)) :
    Measurable (fun q : α × ℝ =>
      evolve (List.ofFn fun i => (a i q.1,d i q.1)) (f q.1) q.2) := by
  induction n with
  | zero => simpa only [List.ofFn_zero,evolve,Function.comp_def,uncurry] using
      hf.comp (measurable_fst.prodMk measurable_snd)
  | succ n ih =>
    have ht := ih (fun i => a i.succ) (fun i => d i.succ)
      (fun i => ha i.succ) (fun i => hd i.succ)
    simp only [List.ofFn_succ,evolve]
    refine measurable_step_param ((ha 0).coe_nnreal_real.comp measurable_fst)
      (((hd 0).coe_nnreal_real.sqrt).comp measurable_fst) measurable_snd ?_
    exact ht.comp (measurable_fst.fst.prodMk measurable_snd)

 

lemma measurable_field (β : ℝ≥0) {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) :
    Measurable (fun q : ℝ≥0 × ℝ => field β γ q.1 q.2) := by
  have hg := hγ.measurable
  have hstep (n : ℕ) : Measurable (fun q : ℝ≥0 × ℝ =>
      evolve (dyadicSchedule γ false q.1 (1-q.1) n) (terminal β) q.2) := by
    simp_rw [dyadicSchedule_eq_uniform,uniformLower]
    refine measurable_evolve_ofFn (2^n)
      (fun i t => γ (t+(1-t)*(i : ℕ)/((2^n : ℕ) : ℝ≥0)))
      (fun _ t => (1-t)/((2^n : ℕ) : ℝ≥0)) ?_ ?_ (f := fun _ => terminal β) ?_
    · intro i
      exact hg.comp (by fun_prop)
    · intro i
      fun_prop
    · unfold uncurry terminal
      fun_prop
  exact Measurable.iSup hstep

 

lemma measurable_fieldGradient (β : ℝ≥0) (hβ : 0 < β)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t, γ t ≤ β) :
    Measurable (fun q : ℝ≥0 × ℝ => fieldGradient β γ q.1 q.2) := by
  let ε (n : ℕ) : ℝ := 1 / (n+1 : ℕ)
  have hε : Tendsto ε atTop (𝓝[≠] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨SKCavity.tendsto_succ_reciprocal, ?_⟩
    exact Filter.Eventually.of_forall fun n => by
      simp only [Set.mem_compl_iff,Set.mem_singleton_iff,ε]
      positivity
  have hm (n : ℕ) : Measurable (fun q : ℝ≥0 × ℝ =>
      (ε n)⁻¹ * (field β γ q.1 (q.2+ε n) - field β γ q.1 q.2)) := by
    exact (((measurable_field β hγ).comp
      (measurable_fst.prodMk (measurable_snd.add_const (ε n)))).sub
      (measurable_field β hγ)).const_mul _
  apply measurable_of_tendsto_metrizable hm
  refine tendsto_pi_nhds.mpr fun q => ?_
  simpa only [smul_eq_mul,Function.comp_def] using
    (hasDerivAt_field β hβ hγ hb q.1 q.2).tendsto_slope_zero.comp hε

 
def parisiDrift (β : ℝ≥0) (ρ : ProbabilityMeasure OrderPoint) (t x : ℝ) : ℝ :=
  (measureCoefficient ρ β (Real.toNNReal t) : ℝ) *
    fieldGradient β (measureCoefficient ρ β) (Real.toNNReal t) x

lemma parisiDrift_measurable (β : ℝ≥0) (hβ : 0 < β)
    (ρ : ProbabilityMeasure OrderPoint) :
    Measurable (uncurry (parisiDrift β ρ)) := by
  have hm := measureCoefficient_mono ρ β
  have hb (t : ℝ≥0) : measureCoefficient ρ β t ≤ β :=
    NNReal.coe_le_coe.mp (measureCoefficient_bound ρ β t)
  have ht : Measurable (fun q : ℝ × ℝ => Real.toNNReal q.1) := by fun_prop
  exact (hm.measurable.comp ht).coe_nnreal_real.mul
    ((measurable_fieldGradient β hβ hm hb).comp (ht.prodMk measurable_snd))

lemma parisiDrift_bound (β : ℝ≥0) (hβ : 0 < β)
    (ρ : ProbabilityMeasure OrderPoint) (t x : ℝ) :
    ‖parisiDrift β ρ t x‖ ≤ β := by
  have hb (s : ℝ≥0) : measureCoefficient ρ β s ≤ β :=
    NNReal.coe_le_coe.mp (measureCoefficient_bound ρ β s)
  rw [parisiDrift,Real.norm_eq_abs,abs_mul,NNReal.abs_eq]
  calc
    _ ≤ (measureCoefficient ρ β (Real.toNNReal t) : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left
        (fieldGradient_bound β hβ (measureCoefficient_mono ρ β) hb _ _) (by positivity)
    _ ≤ β := by simpa using measureCoefficient_bound ρ β (Real.toNNReal t)

lemma parisiDrift_lipschitz (β : ℝ≥0) (hβ : 0 < β)
    (ρ : ProbabilityMeasure OrderPoint) (t : ℝ) :
    LipschitzWith (β*β) (parisiDrift β ρ t) := by
  have hb (s : ℝ≥0) : measureCoefficient ρ β s ≤ β :=
    NNReal.coe_le_coe.mp (measureCoefficient_bound ρ β s)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,parisiDrift,parisiDrift,← mul_sub,abs_mul,NNReal.abs_eq]
  calc
    _ ≤ (measureCoefficient ρ β (Real.toNNReal t) : ℝ) * (β * dist x y) :=
      mul_le_mul_of_nonneg_left
        ((fieldGradient_lipschitz β hβ (measureCoefficient_mono ρ β) hb _).dist_le_mul x y)
        (by positivity)
    _ ≤ (β*β : ℝ≥0) * dist x y := by
      simp only [NNReal.coe_mul]
      calc
        _ ≤ (β : ℝ) * (β * dist x y) :=
          mul_le_mul_of_nonneg_right (measureCoefficient_bound ρ β _) (by positivity)
        _ = _ := by ring

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite
open ParisiPath

 

structure BoundedCoefficient (β : ℝ≥0) where
  val : ℝ≥0 → ℝ≥0
  mono : Monotone val
  bound : ∀ t,val t≤β

namespace BoundedCoefficient
variable {β : ℝ≥0}

def ofMeasure (β : ℝ≥0) (ρ : ProbabilityMeasure OrderPoint) : BoundedCoefficient β where
  val := measureCoefficient ρ β
  mono := measureCoefficient_mono ρ β
  bound := fun t => NNReal.coe_le_coe.mp (measureCoefficient_bound ρ β t)

def real (c : BoundedCoefficient β) (t : ℝ) : ℝ := c.val (Real.toNNReal t)

lemma measurable_real (c : BoundedCoefficient β) : Measurable c.real :=
  (c.mono.measurable.comp (by fun_prop : Measurable Real.toNNReal)).coe_nnreal_real

lemma real_nonneg (c : BoundedCoefficient β) (t : ℝ) : 0≤c.real t := (c.val _).coe_nonneg
lemma real_le (c : BoundedCoefficient β) (t : ℝ) : c.real t≤β := NNReal.coe_le_coe.mpr (c.bound _)

def drift (c : BoundedCoefficient β) (t x : ℝ) : ℝ :=
  c.real t*fieldGradient β c.val (Real.toNNReal t) x

lemma drift_measurable (c : BoundedCoefficient β) (hβ : 0<β) : Measurable (uncurry c.drift) := by
  exact (c.measurable_real.comp measurable_fst).mul
    ((measurable_fieldGradient β hβ c.mono c.bound).comp
      ((by fun_prop : Measurable (fun q : ℝ × ℝ => Real.toNNReal q.1)).prodMk measurable_snd))

lemma drift_bound (c : BoundedCoefficient β) (hβ : 0<β) (t x : ℝ) : ‖c.drift t x‖≤β := by
  rw [drift,Real.norm_eq_abs,abs_mul,abs_of_nonneg (c.real_nonneg t)]
  exact (mul_le_mul_of_nonneg_left (fieldGradient_bound β hβ c.mono c.bound _ _)
    (c.real_nonneg t)).trans (by simpa only [mul_one] using c.real_le t)

lemma drift_lipschitz (c : BoundedCoefficient β) (hβ : 0<β) (t : ℝ) : LipschitzWith (β*β) (c.drift t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,drift,←mul_sub,abs_mul,abs_of_nonneg (c.real_nonneg t),NNReal.coe_mul]
  calc
    _ ≤ c.real t*((β:ℝ)*|x-y|) := mul_le_mul_of_nonneg_left
      ((fieldGradient_lipschitz β hβ c.mono c.bound _).dist_le_mul x y) (c.real_nonneg t)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right (c.real_le t) (mul_nonneg β.coe_nonneg (abs_nonneg (x-y)))]

def driftData (c : BoundedCoefficient β) (hβ : 0<β) : Drift (β*β) β where
  val := c.drift
  measurable := c.drift_measurable hβ
  bound := c.drift_bound hβ
  lipschitz := c.drift_lipschitz hβ

lemma drift_joint_ae_continuous (c : BoundedCoefficient β) (hβ : 0<β) :
    ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry c.drift) (t,x) := by
  have hm : Monotone c.real := fun s t h =>
    NNReal.coe_le_coe.mpr (c.mono (Real.toNNReal_le_toNNReal h))
  have hc : ∀ᵐ t ∂volume,ContinuousAt c.real t := by
    rw [ae_iff]
    exact hm.countable_not_continuousAt.measure_zero volume
  have h0 : ∀ᵐ t ∂volume,t≠(0:ℝ) := by simp [ae_iff,measure_singleton]
  have h1 : ∀ᵐ t ∂volume,t≠(1:ℝ) := by simp [ae_iff,measure_singleton]
  have hg := continuous_fieldGradient_joint β hβ c.mono c.bound
  have hG : Continuous (fun q : ℝ × ℝ => fieldGradient β c.val
      (Real.toNNReal (projIcc 0 1 zero_le_one q.1)) q.2) :=
    hg.comp (((show Continuous (projIcc (0:ℝ) 1 zero_le_one) from continuous_projIcc).comp
      continuous_fst).prodMk continuous_snd)
  filter_upwards [hc,h0,h1] with t ht ht0 ht1 hmem x
  have ht' : t∈Ioo (0:ℝ) 1 := ⟨lt_of_le_of_ne hmem.1 (Ne.symm ht0),lt_of_le_of_ne hmem.2 ht1⟩
  have hG' : ContinuousAt (fun q : ℝ × ℝ => fieldGradient β c.val (Real.toNNReal q.1) q.2) (t,x) := by
    apply hG.continuousAt.congr_of_eventuallyEq
    filter_upwards [continuousAt_fst.preimage_mem_nhds (Ioo_mem_nhds ht'.1 ht'.2)] with q hq
    rw [projIcc_of_mem zero_le_one ⟨hq.1.le,hq.2.le⟩]
  exact (ht.comp continuousAt_fst).mul hG'

 

def spin (c : BoundedCoefficient β) (X : Path) (t : ℝ) : ℝ :=
  fieldGradient β c.val (Real.toNNReal (projIcc 0 1 zero_le_one t)) (extend X t)

lemma spin_eq (c : BoundedCoefficient β) (X : Path) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    c.spin X t=fieldGradient β c.val (Real.toNNReal t) (extend X t) := by
  simp only [spin,projIcc_of_mem zero_le_one ht]

lemma continuous_spin (c : BoundedCoefficient β) (hβ : 0<β) (X : Path) : Continuous (c.spin X) :=
  (continuous_fieldGradient_joint β hβ c.mono c.bound).comp
    ((show Continuous (projIcc (0:ℝ) 1 zero_le_one) from continuous_projIcc).prodMk (continuous_extend X))

lemma norm_spin_le (c : BoundedCoefficient β) (hβ : 0<β) (X : Path) (t : ℝ) : ‖c.spin X t‖≤1 :=
  fieldGradient_bound β hβ c.mono c.bound _ _

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
variable {K M : ℝ≥0}

lemma spin_aestronglyMeasurable (hW : IsBrownianReal W P) (c : BoundedCoefficient β)
    (hβ : 0<β) (b : Drift K M) (t : ℝ) :
    AEStronglyMeasurable (fun ω => c.spin (solution b (brownianPath W ω)) t) P := by
  exact ((fieldGradient_lipschitz β hβ c.mono c.bound _).continuous.measurable.comp_aemeasurable
    (aemeasurable_solution_eval b (brownianPath W) (brownianPath_aemeasurable_eval hW)
      (projIcc 0 1 zero_le_one t))).aestronglyMeasurable

lemma spin_integrable (hW : IsBrownianReal W P) (c : BoundedCoefficient β)
    (hβ : 0<β) (b : Drift K M) (t : ℝ) :
    Integrable (fun ω => c.spin (solution b (brownianPath W ω)) t) P := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact Integrable.of_bound (c.spin_aestronglyMeasurable hW hβ b t) 1
    (ae_of_all _ fun ω => c.norm_spin_le hβ _ t)

def expectedProduct (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (c d : BoundedCoefficient β)
    (b : Drift K M) (t : ℝ) : ℝ :=
  ∫ ω,c.spin (solution b (brownianPath W ω)) t*d.spin (solution b (brownianPath W ω)) t ∂P

lemma norm_spin_product_le (c d : BoundedCoefficient β) (hβ : 0<β) (X : Path) (t : ℝ) :
    ‖c.spin X t*d.spin X t‖≤1 := by
  rw [norm_mul]
  exact (mul_le_mul (c.norm_spin_le hβ X t) (d.norm_spin_le hβ X t) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

lemma spin_product_integrable (hW : IsBrownianReal W P) (c d : BoundedCoefficient β)
    (hβ : 0<β) (b : Drift K M) (t : ℝ) :
    Integrable (fun ω => c.spin (solution b (brownianPath W ω)) t*
      d.spin (solution b (brownianPath W ω)) t) P := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact Integrable.of_bound ((c.spin_aestronglyMeasurable hW hβ b t).mul
    (d.spin_aestronglyMeasurable hW hβ b t)) 1 (ae_of_all _ fun ω => norm_spin_product_le c d hβ _ t)

lemma expectedProduct_continuous (hW : IsBrownianReal W P) (c d : BoundedCoefficient β)
    (hβ : 0<β) (b : Drift K M) : Continuous (expectedProduct P W c d b) := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  apply continuous_of_dominated (bound := fun _ => (1:ℝ))
    (fun t => (spin_product_integrable hW c d hβ b t).aestronglyMeasurable)
    (fun t => ae_of_all _ fun ω => norm_spin_product_le c d hβ _ t) (integrable_const _)
  exact ae_of_all _ fun ω => (c.continuous_spin hβ _).mul (d.continuous_spin hβ _)

lemma expectedProduct_bound (hW : IsBrownianReal W P) (c d : BoundedCoefficient β)
    (hβ : 0<β) (b : Drift K M) (t : ℝ) : ‖expectedProduct P W c d b t‖≤1 := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact (norm_integral_le_of_norm_le_const (μ := P) (ae_of_all _ fun ω => norm_spin_product_le c d hβ _ t)).trans_eq (by simp)

lemma expectedProduct_comm (c d : BoundedCoefficient β) (b : Drift K M) (t : ℝ) :
    expectedProduct P W c d b t=expectedProduct P W d c b t := by
  simp only [expectedProduct,mul_comm]

lemma real_intervalIntegrable (c : BoundedCoefficient β) (a b : ℝ) :
    IntervalIntegrable c.real volume a b := by
  apply (intervalIntegrable_const (c := (β:ℝ))).mono_fun' c.measurable_real.aestronglyMeasurable
  exact Eventually.of_forall fun t => by simpa only [Real.norm_eq_abs,abs_of_nonneg (c.real_nonneg t)] using c.real_le t

lemma expectedProduct_psd (hW : IsBrownianReal W P) (c d : BoundedCoefficient β)
    (hβ : 0<β) (b : Drift K M) (t : ℝ) :
    2*expectedProduct P W c d b t ≤ expectedProduct P W c c b t+expectedProduct P W d d b t := by
  unfold expectedProduct
  rw [←integral_const_mul,←integral_add (spin_product_integrable hW c c hβ b t)
    (spin_product_integrable hW d d hβ b t)]
  apply integral_mono_ae ((spin_product_integrable hW c d hβ b t).const_mul 2)
    ((spin_product_integrable hW c c hβ b t).add (spin_product_integrable hW d d hβ b t))
  exact ae_of_all _ fun ω => by
    dsimp only [Pi.add_apply]
    nlinarith [sq_nonneg (c.spin (solution b (brownianPath W ω)) t-d.spin (solution b (brownianPath W ω)) t)]

lemma weightedProduct_intervalIntegrable (hW : IsBrownianReal W P) (c d e : BoundedCoefficient β)
    (hβ : 0<β) (b : Drift K M) :
    IntervalIntegrable (fun t => c.real t*expectedProduct P W d e b t) volume 0 1 :=
  (c.real_intervalIntegrable 0 1).mul_continuousOn (expectedProduct_continuous hW d e hβ b).continuousOn

def feedbackKernel (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (hβ : 0<β)
    (c d : BoundedCoefficient β) (t : ℝ) : ℝ :=
  d.real t*expectedProduct P W c d (d.driftData hβ) t-
    c.real t/2*expectedProduct P W c c (d.driftData hβ) t

lemma feedbackKernel_intervalIntegrable (hW : IsBrownianReal W P) (c d : BoundedCoefficient β)
    (hβ : 0<β) : IntervalIntegrable (feedbackKernel P W hβ c d) volume 0 1 := by
  apply (weightedProduct_intervalIntegrable hW d c d hβ _).sub
  have hh := (weightedProduct_intervalIntegrable hW c c c hβ (d.driftData hβ)).div_const 2
  convert! hh using 1
  ext t
  ring

lemma expected_verificationKernel_eq_feedback (hW : IsBrownianReal W P) (c d : BoundedCoefficient β)
    (hβ : 0<β) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    (∫ ω,verificationKernel β c.val (d.driftData hβ) t
      (extend (solution (d.driftData hβ) (brownianPath W ω)) t) ∂P)=feedbackKernel P W hβ c d t := by
  unfold feedbackKernel expectedProduct
  rw [←integral_const_mul,←integral_const_mul,←integral_sub
    ((spin_product_integrable hW c d hβ (d.driftData hβ) t).const_mul _)
    ((spin_product_integrable hW c c hβ (d.driftData hβ) t).const_mul _)]
  apply integral_congr_ae
  filter_upwards [] with ω
  simp only [spin_eq _ _ _ ht,verificationKernel,driftData,drift,real]
  ring

 
theorem feedback_verification (hW : IsBrownianReal W P) (c d : BoundedCoefficient β) (hβ : 0<β) :
    (∫ ω,terminal β (solution (d.driftData hβ) (brownianPath W ω) ⟨1,by simp⟩) ∂P)-field β c.val 0 0=
      ∫ t in (0:ℝ)..1,feedbackKernel P W hβ c d t := by
  rw [canonical_verification hW (d.driftData hβ) (d.drift_joint_ae_continuous hβ) β hβ c.mono c.bound]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with t ht
  rw [uIoc_of_le zero_le_one] at ht
  exact expected_verificationKernel_eq_feedback hW c d hβ t ⟨ht.1.le,ht.2⟩

 
theorem field_comparison_lower (hW : IsBrownianReal W P) (c d : BoundedCoefficient β) (hβ : 0<β) :
    (∫ t in (0:ℝ)..1,(c.real t-d.real t)/2*expectedProduct P W c c (d.driftData hβ) t) ≤
      field β c.val 0 0-field β d.val 0 0 := by
  have hi : IntervalIntegrable (fun t => (c.real t-d.real t)/2*
      expectedProduct P W c c (d.driftData hβ) t) volume 0 1 := by
    have hh := ((weightedProduct_intervalIntegrable hW c c c hβ (d.driftData hβ)).sub
      (weightedProduct_intervalIntegrable hW d c c hβ (d.driftData hβ))).div_const 2
    convert! hh using 1
    ext t
    ring
  have he : field β c.val 0 0-field β d.val 0 0=
      ∫ t in (0:ℝ)..1,feedbackKernel P W hβ d d t-feedbackKernel P W hβ c d t := by
    rw [intervalIntegral.integral_sub (feedbackKernel_intervalIntegrable hW d d hβ)
      (feedbackKernel_intervalIntegrable hW c d hβ),←feedback_verification hW d d hβ,
      ←feedback_verification hW c d hβ]
    ring
  rw [he]
  apply intervalIntegral.integral_mono zero_le_one hi
    ((feedbackKernel_intervalIntegrable hW d d hβ).sub (feedbackKernel_intervalIntegrable hW c d hβ))
  intro t
  have hp := expectedProduct_psd hW c d hβ (d.driftData hβ) t
  have hpos := d.real_nonneg t
  dsimp only [feedbackKernel]
  nlinarith [mul_nonneg hpos (sub_nonneg.mpr hp)]

 
theorem field_comparison_upper (hW : IsBrownianReal W P) (c d : BoundedCoefficient β) (hβ : 0<β) :
    field β c.val 0 0-field β d.val 0 0 ≤
      ∫ t in (0:ℝ)..1,(c.real t-d.real t)/2*expectedProduct P W d d (c.driftData hβ) t := by
  have hh := field_comparison_lower hW d c hβ
  have he : (∫ t in (0:ℝ)..1,(d.real t-c.real t)/2*expectedProduct P W d d (c.driftData hβ) t)=
      -(∫ t in (0:ℝ)..1,(c.real t-d.real t)/2*expectedProduct P W d d (c.driftData hβ) t) := by
    rw [←intervalIntegral.integral_neg]
    congr 1
    ext t
    ring
  rw [he] at hh
  linarith

end BoundedCoefficient
end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite

lemma step_tendsto_coefficient_field {L : ℝ≥0} {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ n,LipschitzWith L (F n)) (hf : LipschitzWith L f)
    (hfn : ∀ x,Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    {A : ℕ → ℝ} {a : ℝ} (hA : ∀ n,0≤A n) (ha : 0≤a)
    (hAn : Tendsto A atTop (𝓝 a)) (s x : ℝ) :
    Tendsto (fun n => step (A n) s (F n) x) atTop (𝓝 (step a s f x)) := by
  have he := SKCavity.tendsto_succ_reciprocal
  have hp (k : ℕ) : 0 < (1:ℝ)/(k+1:ℕ) := by positivity
  have hlo : Tendsto (fun k : ℕ => max 0 (a-1/(k+1:ℕ))) atTop (𝓝 a) := by
    simpa only [sub_zero,max_eq_right ha] using (tendsto_const_nhds (x := (0:ℝ))).max ((tendsto_const_nhds (x := a)).sub he)
  have hup : Tendsto (fun k : ℕ => a+1/(k+1:ℕ)) atTop (𝓝 a) := by
    simpa only [add_zero] using tendsto_const_nhds.add he
  have hs := (step_analyticAt_coefficient hf a s x).continuousAt
  rw [tendsto_order]
  constructor
  · intro v hv
    by_cases hz : a=0
    · subst a
      filter_upwards [(step_tendsto hF hf hfn 0 s x).eventually (lt_mem_nhds hv)] with n hn
      exact hn.trans_le (step_parameter_mono (hF n) le_rfl (hA n) s x)
    · have hap : 0<a := lt_of_le_of_ne ha (Ne.symm hz)
      obtain ⟨k,hk⟩ := ((hs.tendsto.comp hlo).eventually (lt_mem_nhds hv)).exists
      have hlt : max 0 (a-1/(k+1:ℕ))<a := max_lt hap (sub_lt_self _ (hp k))
      filter_upwards [hAn.eventually (lt_mem_nhds hlt),
        (step_tendsto hF hf hfn (max 0 (a-1/(k+1:ℕ))) s x).eventually (lt_mem_nhds hk)] with n hn hn'
      exact hn'.trans_le (step_parameter_mono (hF n) (le_max_left _ _) hn.le s x)
  · intro v hv
    obtain ⟨k,hk⟩ := ((hs.tendsto.comp hup).eventually (gt_mem_nhds hv)).exists
    have hlt : a<a+1/(k+1:ℕ) := lt_add_of_pos_right _ (hp k)
    filter_upwards [hAn.eventually (gt_mem_nhds hlt),
      (step_tendsto hF hf hfn (a+1/(k+1:ℕ)) s x).eventually (gt_mem_nhds hk)] with n hn hn'
    exact (step_parameter_mono (hF n) (hA n) hn.le s x).trans_lt hn'

lemma dyadic_fixed_tendsto_coefficient {L : ℝ≥0} {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ n,LipschitzWith L (F n)) (hf : LipschitzWith L f)
    (hfn : ∀ x,Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    {G : ℕ → ℝ≥0 → ℝ≥0} {γ : ℝ≥0 → ℝ≥0}
    (hG : ∀ t,Tendsto (fun n => G n t) atTop (𝓝 (γ t)))
    (u : Bool) (t d : ℝ≥0) (k : ℕ) (x : ℝ) :
    Tendsto (fun n => evolve (dyadicSchedule (G n) u t d k) (F n) x) atTop
      (𝓝 (evolve (dyadicSchedule γ u t d k) f x)) := by
  induction k generalizing F f t d x with
  | zero =>
    simp only [dyadicSchedule,evolve]
    exact step_tendsto_coefficient_field hF hf hfn (fun n => (G n _).coe_nonneg)
      (γ _).coe_nonneg (NNReal.continuous_coe.continuousAt.tendsto.comp (hG _)) _ _
  | succ k ih =>
    simp only [dyadicSchedule,evolve_append]
    exact ih (fun n => evolve_lipschitz (hF n) _) (evolve_lipschitz hf _)
      (fun y => ih hF hf hfn (t+d/2) (d/2) y) t (d/2) x

lemma dyadicEvolution_tendsto_coefficient {G : ℕ → ℝ≥0 → ℝ≥0} {γ : ℝ≥0 → ℝ≥0}
    (hGm : ∀ n,Monotone (G n)) (hγ : Monotone γ) {β : ℝ}
    (hb : ∀ t,(γ t:ℝ)≤β) (hG : ∀ t,Tendsto (fun n => G n t) atTop (𝓝 (γ t)))
    {f : ℝ → ℝ} (hf : LipschitzWith 1 f) (t d : ℝ≥0) (x : ℝ) :
    Tendsto (fun n => dyadicEvolution (G n) t d f x) atTop
      (𝓝 (dyadicEvolution γ t d f x)) := by
  rw [tendsto_order]
  constructor
  · intro v hv
    obtain ⟨k,hk⟩ := ((dyadic_low_tendsto hf hγ t d x).eventually (lt_mem_nhds hv)).exists
    filter_upwards [(dyadic_fixed_tendsto_coefficient (fun _ => hf) hf
      (fun _ => tendsto_const_nhds) hG false t d k x).eventually (lt_mem_nhds hk)] with n hn
    exact hn.trans_le (le_ciSup (dyadic_low_bddAbove hf (hGm n) t d x) k)
  · intro v hv
    obtain ⟨k,hk⟩ := ((dyadic_high_tendsto hf hγ hb t d x).eventually (gt_mem_nhds hv)).exists
    filter_upwards [(dyadic_fixed_tendsto_coefficient (fun _ => hf) hf
      (fun _ => tendsto_const_nhds) hG true t d k x).eventually (gt_mem_nhds hk)] with n hn
    apply lt_of_le_of_lt ?_ hn
    apply le_of_tendsto (dyadic_low_tendsto hf (hGm n) t d x)
    filter_upwards [eventually_ge_atTop k] with j hj
    exact (dyadicSchedule_low_le_high hf (hGm n) t d j x).trans
      (dyadic_high_antitone hf (hGm n) t d x hj)

lemma field_tendsto_coefficient (β : ℝ≥0) (hβ : 0<β)
    {G : ℕ → ℝ≥0 → ℝ≥0} {γ : ℝ≥0 → ℝ≥0}
    (hGm : ∀ n,Monotone (G n)) (hγ : Monotone γ) (hb : ∀ t,γ t≤β)
    (hG : ∀ t,Tendsto (fun n => G n t) atTop (𝓝 (γ t))) (t : ℝ≥0) (x : ℝ) :
    Tendsto (fun n => field β (G n) t x) atTop (𝓝 (field β γ t x)) :=
  dyadicEvolution_tendsto_coefficient hGm hγ (fun t => NNReal.coe_le_coe.mpr (hb t)) hG
    (terminal_lipschitz (show (0:ℝ)<β from hβ)) t (1-t) x

 

lemma fieldGradient_tendsto_coefficient (β : ℝ≥0) (hβ : 0<β)
    {G : ℕ → ℝ≥0 → ℝ≥0} {γ : ℝ≥0 → ℝ≥0}
    (hGm : ∀ n,Monotone (G n)) (hGb : ∀ n t,G n t≤β)
    (hγ : Monotone γ) (hb : ∀ t,γ t≤β)
    (hG : ∀ t,Tendsto (fun n => G n t) atTop (𝓝 (γ t))) (t : ℝ≥0) (x : ℝ) :
    Tendsto (fun n => fieldGradient β (G n) t x) atTop (𝓝 (fieldGradient β γ t x)) := by
  let ε (k : ℕ) : ℝ := 1/(k+1:ℕ)
  have hp (k : ℕ) : 0<ε k := by dsimp [ε];positivity
  have he : Tendsto ε atTop (𝓝[≠] (0:ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨SKCavity.tendsto_succ_reciprocal,?_⟩
    exact Eventually.of_forall fun k => (hp k).ne'
  have hs : Tendsto (fun k => (field β γ t (x+ε k)-field β γ t x)/ε k) atTop
      (𝓝 (fieldGradient β γ t x)) := by
    simpa only [smul_eq_mul,Function.comp_def,div_eq_mul_inv,mul_comm] using
      (hasDerivAt_field β hβ hγ hb t x).tendsto_slope_zero.comp he
  have hh : Tendsto (fun k => (β:ℝ)*ε k) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero] using SKCavity.tendsto_succ_reciprocal.const_mul (β:ℝ)
  have hfn (k : ℕ) : Tendsto (fun n => (field β (G n) t (x+ε k)-field β (G n) t x)/ε k)
      atTop (𝓝 ((field β γ t (x+ε k)-field β γ t x)/ε k)) :=
    ((field_tendsto_coefficient β hβ hGm hγ hb hG t (x+ε k)).sub
      (field_tendsto_coefficient β hβ hGm hγ hb hG t x)).div_const _
  rw [tendsto_order]
  constructor
  · intro v hv
    have hl := hs.sub hh
    rw [sub_zero] at hl
    obtain ⟨k,hk⟩ := (hl.eventually (lt_mem_nhds hv)).exists
    filter_upwards [((hfn k).sub_const ((β:ℝ)*ε k)).eventually (lt_mem_nhds hk)] with n hn
    have hbnd := (abs_le.mp (field_slope_error β hβ (hGm n) (hGb n) t x (hp k))).2
    linarith
  · intro v hv
    have hl := hs.add hh
    rw [add_zero] at hl
    obtain ⟨k,hk⟩ := (hl.eventually (gt_mem_nhds hv)).exists
    filter_upwards [((hfn k).add_const ((β:ℝ)*ε k)).eventually (gt_mem_nhds hk)] with n hn
    have hbnd := (abs_le.mp (field_slope_error β hβ (hGm n) (hGb n) t x (hp k))).1
    linarith

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiPath
variable {K M : ℝ≥0}

lemma drift_comp_tendsto {B : ℕ → Drift K M} {b : Drift K M}
    (hB : ∀ t x,Tendsto (fun n => (B n).val t x) atTop (𝓝 (b.val t x)))
    {X : ℕ → Path} {Y : Path} (hX : Tendsto X atTop (𝓝 Y)) (t : ℝ) :
    Tendsto (fun n => (B n).val t (extend (X n) t)) atTop (𝓝 (b.val t (extend Y t))) := by
  have hx : Tendsto (fun n => extend (X n) t) atTop (𝓝 (extend Y t)) :=
    (show Continuous (fun V : Path => extend V t) by unfold extend;fun_prop).continuousAt.tendsto.comp hX
  have hd : Tendsto (fun n => (B n).val t (extend (X n) t)-(B n).val t (extend Y t))
      atTop (𝓝 (0:ℝ)) := by
    have hnorm (n : ℕ) : ‖(B n).val t (extend (X n) t)-(B n).val t (extend Y t)‖ ≤
        (K:ℝ)*‖extend (X n) t-extend Y t‖ := by
      simpa only [←dist_eq_norm] using (B n).lipschitz t |>.dist_le_mul (extend (X n) t) (extend Y t)
    exact squeeze_zero_norm hnorm
      (by simpa only [sub_self,norm_zero,mul_zero] using
        ((hx.sub_const (extend Y t)).norm.const_mul (K:ℝ)))
  simpa only [sub_add_cancel,zero_add] using hd.add (hB t (extend Y t))

lemma next_tendsto_drift {B : ℕ → Drift K M} {b : Drift K M}
    (hB : ∀ t x,Tendsto (fun n => (B n).val t x) atTop (𝓝 (b.val t x)))
    {X : ℕ → Path} {Y : Path} (hX : Tendsto X atTop (𝓝 Y)) (W : Path) :
    Tendsto (fun n => next (B n) W (X n)) atTop (𝓝 (next b W Y)) := by
  let R (n : ℕ) (t : ℝ) : ℝ := ‖(B n).val t (extend (X n) t)-b.val t (extend Y t)‖
  have hRm (n : ℕ) : Measurable (R n) :=
    (((B n).measurable.comp (measurable_id.prodMk (continuous_extend (X n)).measurable)).sub
      (b.measurable.comp (measurable_id.prodMk (continuous_extend Y).measurable))).norm
  have hRb (n : ℕ) (t : ℝ) : R n t ≤ 2*(M:ℝ) :=
    (norm_sub_le _ _).trans (by linarith [(B n).bound t (extend (X n) t),b.bound t (extend Y t)])
  have hRi (n : ℕ) : IntervalIntegrable (R n) volume 0 1 :=
    (intervalIntegrable_const (c := 2*(M:ℝ))).mono_fun' (hRm n).aestronglyMeasurable
      (Eventually.of_forall fun t => by simpa only [R,norm_norm] using hRb n t)
  have he : Tendsto (fun n => ∫ t in (0:ℝ)..1,R n t) atTop (𝓝 (0:ℝ)) := by
    have hh := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (a := (0:ℝ)) (b := 1) (μ := volume) (l := atTop) (F := R) (f := fun _ => (0:ℝ))
      (fun _ => 2*(M:ℝ)) (Eventually.of_forall fun n => (hRm n).aestronglyMeasurable.restrict)
      (Eventually.of_forall fun n => ae_of_all _ fun t _ => by simpa only [R,norm_norm] using hRb n t)
      intervalIntegrable_const (ae_of_all _ fun t _ => by
        simpa only [R,sub_self,norm_zero] using ((drift_comp_tendsto hB hX t).sub_const (b.val t (extend Y t))).norm)
    simpa only [intervalIntegral.integral_zero] using hh
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun n => dist_nonneg) (fun n => ?_) he
  apply (ContinuousMap.dist_le
    (intervalIntegral.integral_nonneg zero_le_one (fun t _ => norm_nonneg _))).mpr
  intro t
  rw [dist_eq_norm,next_apply,next_apply,add_sub_add_left_eq_sub,
    ←intervalIntegral.integral_sub (integrable_comp (B n) (X n) _ _) (integrable_comp b Y _ _)]
  calc
    _ ≤ ∫ s in (0:ℝ)..(t:ℝ),R n s := intervalIntegral.norm_integral_le_integral_norm t.property.1
    _ ≤ ∫ s in (0:ℝ)..1,R n s := intervalIntegral.integral_mono_interval le_rfl t.property.1
      t.property.2 (ae_of_all _ fun s => norm_nonneg _) (hRi n)

lemma iterate_tendsto_drift {B : ℕ → Drift K M} {b : Drift K M}
    (hB : ∀ t x,Tendsto (fun n => (B n).val t x) atTop (𝓝 (b.val t x)))
    (W X : Path) (k : ℕ) :
    Tendsto (fun n => ((next (B n) W)^[k]) X) atTop (𝓝 (((next b W)^[k]) X)) := by
  induction k with
  | zero => exact tendsto_const_nhds
  | succ k ih => simpa only [iterate_succ_apply'] using next_tendsto_drift hB ih W

 

theorem solution_tendsto_drift {B : ℕ → Drift K M} {b : Drift K M}
    (hB : ∀ t x,Tendsto (fun n => (B n).val t x) atTop (𝓝 (b.val t x))) (W : Path) :
    Tendsto (fun n => solution (B n) W) atTop (𝓝 (solution b W)) := by
  obtain ⟨k,hk⟩ := (FloorSemiring.tendsto_pow_div_factorial_atTop (K:ℝ)).eventually
    (gt_mem_nhds zero_lt_one) |>.exists
  let C : ℝ≥0 := ⟨(K:ℝ)^k/k.factorial,by positivity⟩
  have hc (b' : Drift K M) : ContractingWith C ((next b' W)^[k]) :=
    ⟨hk,LipschitzWith.of_dist_le_mul fun X Y => dist_iterate b' W X Y k⟩
  have ht := iterate_tendsto_drift hB W (solution b W) k
  rw [(solution_fixed b W).iterate k] at ht
  have hz : Tendsto (fun n => dist (solution b W) (((next (B n) W)^[k]) (solution b W))/(1-(C:ℝ)))
      atTop (𝓝 (0:ℝ)) := by
    simpa only [dist_self,zero_div] using ((tendsto_const_nhds (x := solution b W)).dist ht).div_const (1-(C:ℝ))
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hz
  rw [dist_comm]
  exact (hc (B n)).dist_le_of_fixedPoint _ ((solution_fixed (B n) W).iterate k)

end ParisiPath

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite
open ParisiPath
namespace BoundedCoefficient
variable {β : ℝ≥0} {C : ℕ → BoundedCoefficient β} {c : BoundedCoefficient β}

lemma real_tendsto (hC : ∀ t,Tendsto (fun n => (C n).val t) atTop (𝓝 (c.val t))) (t : ℝ) :
    Tendsto (fun n => (C n).real t) atTop (𝓝 (c.real t)) :=
  NNReal.continuous_coe.continuousAt.tendsto.comp (hC _)

lemma gradient_tendsto (hβ : 0<β)
    (hC : ∀ t,Tendsto (fun n => (C n).val t) atTop (𝓝 (c.val t))) (t : ℝ≥0) (x : ℝ) :
    Tendsto (fun n => fieldGradient β (C n).val t x) atTop (𝓝 (fieldGradient β c.val t x)) :=
  fieldGradient_tendsto_coefficient β hβ (fun n => (C n).mono) (fun n => (C n).bound)
    c.mono c.bound hC t x

lemma drift_tendsto (hβ : 0<β)
    (hC : ∀ t,Tendsto (fun n => (C n).val t) atTop (𝓝 (c.val t))) (t x : ℝ) :
    Tendsto (fun n => (C n).drift t x) atTop (𝓝 (c.drift t x)) :=
  (real_tendsto hC t).mul (gradient_tendsto hβ hC _ x)

lemma feedback_solution_tendsto (hβ : 0<β)
    (hC : ∀ t,Tendsto (fun n => (C n).val t) atTop (𝓝 (c.val t))) (W : Path) :
    Tendsto (fun n => solution ((C n).driftData hβ) W) atTop (𝓝 (solution (c.driftData hβ) W)) :=
  solution_tendsto_drift (drift_tendsto hβ hC) W

lemma spin_tendsto (hβ : 0<β)
    (hC : ∀ t,Tendsto (fun n => (C n).val t) atTop (𝓝 (c.val t)))
    {X : ℕ → Path} {Y : Path} (hX : Tendsto X atTop (𝓝 Y)) (t : ℝ) :
    Tendsto (fun n => (C n).spin (X n) t) atTop (𝓝 (c.spin Y t)) := by
  have hx : Tendsto (fun n => ParisiPath.extend (X n) t) atTop (𝓝 (ParisiPath.extend Y t)) :=
    (show Continuous (fun V : Path => ParisiPath.extend V t) by unfold ParisiPath.extend;fun_prop).continuousAt.tendsto.comp hX
  have hd : Tendsto (fun n => (C n).spin (X n) t-(C n).spin Y t) atTop (𝓝 (0:ℝ)) := by
    have hnorm (n : ℕ) : ‖(C n).spin (X n) t-(C n).spin Y t‖ ≤ (β:ℝ)*‖ParisiPath.extend (X n) t-ParisiPath.extend Y t‖ := by
      simpa only [←dist_eq_norm,spin] using
        (fieldGradient_lipschitz β hβ (C n).mono (C n).bound _).dist_le_mul (ParisiPath.extend (X n) t) (ParisiPath.extend Y t)
    exact squeeze_zero_norm hnorm (by simpa only [sub_self,norm_zero,mul_zero] using
      (hx.sub_const (ParisiPath.extend Y t)).norm.const_mul (β:ℝ))
  have hh : Tendsto (fun n => (C n).spin Y t) atTop (𝓝 (c.spin Y t)) :=
    gradient_tendsto hβ hC _ (ParisiPath.extend Y t)
  simpa only [sub_add_cancel,zero_add] using hd.add hh

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
variable {K M : ℝ≥0}

lemma expectedProduct_tendsto (hW : IsBrownianReal W P) (hβ : 0<β)
    {D : ℕ → BoundedCoefficient β} {d : BoundedCoefficient β}
    (hC : ∀ t,Tendsto (fun n => (C n).val t) atTop (𝓝 (c.val t)))
    (hD : ∀ t,Tendsto (fun n => (D n).val t) atTop (𝓝 (d.val t)))
    {B : ℕ → Drift K M} {b : Drift K M}
    (hB : ∀ t x,Tendsto (fun n => (B n).val t x) atTop (𝓝 (b.val t x))) (t : ℝ) :
    Tendsto (fun n => expectedProduct P W (C n) (D n) (B n) t) atTop
      (𝓝 (expectedProduct P W c d b t)) := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  apply tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
    (fun n => (spin_product_integrable hW (C n) (D n) hβ (B n) t).aestronglyMeasurable)
    (integrable_const _) (fun n => ae_of_all _ fun ω => norm_spin_product_le (C n) (D n) hβ _ t)
  exact ae_of_all _ fun ω => (spin_tendsto hβ hC (solution_tendsto_drift hB (brownianPath W ω)) t).mul
    (spin_tendsto hβ hD (solution_tendsto_drift hB (brownianPath W ω)) t)

end BoundedCoefficient
end ParisiFinite

end

end OAI
