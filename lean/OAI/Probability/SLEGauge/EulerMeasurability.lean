import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.BrownianNodes

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped NNReal ENNReal Topology
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set
namespace SLEExactGauge.BrownianCalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
lemma measurable_nodes_driver (v : E → ℝ → E)
    (hv : Measurable (Function.uncurry v)) (h : ℝ≥0) (x : E) (k : ℕ) :
    Measurable (fun b : Driver => stochasticNodes v h x k b) :=
  (measurable_stochasticNodes v hv h x k).comp
    (Measurable.of_eval fun time => (continuous_eval_const time).measurable)

lemma expected_nodes_step {W : Measure Driver}
    (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W)
    (A : SmoothTest E) (v : E → ℝ → E)
    (mv : Measurable (Function.uncurry v)) (M : ℝ) (hv : ∀ x b, ‖v x b‖ ≤ M)
    (hgen : ∀ x b, A.D x b (v x b)+deriv (deriv (A.F x)) b/2 ≤ 0)
    (h : ℝ≥0) (x : E) (k : ℕ) :
    (∫ b : Driver, A.F (stochasticNodes v h x (k+1) b) (b (((k+1:ℕ):ℝ≥0)*h))-
      A.F (stochasticNodes v h x k b) (b ((k:ℝ≥0)*h)) ∂W) ≤
      (A.Cx*M^2+A.Ccross*M/2)*(h:ℝ)^2 + A.C₃/3*(h:ℝ)*Real.sqrt h := by
  let s := (k:ℝ≥0)*h
  let X := fun p : Iic s → ℝ => stochasticNodes v h x k (extendHistory s p)
  let V := fun p : Iic s → ℝ => v (X p) (p ⟨s,by simp⟩)
  have mX : Measurable X := (measurable_stochasticNodes v mv h x k).comp
    (measurable_extendHistory s)
  have mV : Measurable V := mv.comp (mX.prodMk (measurable_pi_apply _))
  have he := expected_euler_step hW s h A.F A.D X V A.mF A.mB1 A.mB2 mX mV
    A.hD A.hsm A.hC₃ A.hCx A.hCcross A.hF A.hB1 A.hB2 A.hB3 A.hLipD A.hLipB2
    (fun p => hv _ _) (fun p => hgen _ _)
  have hn (b : Driver) : X (history s b) = stochasticNodes v h x k b :=
    stochasticNodes_history v h x k b
  have hs : ((k+1:ℕ):ℝ≥0)*h = s+h := by dsimp [s]; push_cast; ring
  simpa only [X, V, hn, history, stochasticNodes, hs] using he

 

theorem expected_nodes {W : Measure Driver}
    (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W)
    (A : SmoothTest E) (v : E → ℝ → E)
    (mv : Measurable (Function.uncurry v)) (M : ℝ) (hv : ∀ x b, ‖v x b‖ ≤ M)
    (hgen : ∀ x b, A.D x b (v x b)+deriv (deriv (A.F x)) b/2 ≤ 0)
    (h : ℝ≥0) (x : E) (k : ℕ) :
    (∫ b : Driver, A.F (stochasticNodes v h x k b) (b ((k:ℝ≥0)*h)) ∂W) ≤
      A.F x 0+(k:ℝ)*((A.Cx*M^2+A.Ccross*M/2)*(h:ℝ)^2 + A.C₃/3*(h:ℝ)*Real.sqrt h) := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  have hi (k : ℕ) : Integrable (fun b : Driver =>
      A.F (stochasticNodes v h x k b) (b ((k:ℝ≥0)*h))) W := by
    apply (integrable_const A.C₀).mono'
    · exact (A.mF.comp ((measurable_nodes_driver v mv h x k).prodMk
        (continuous_eval_const _).measurable)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun b => by simpa only [Real.norm_eq_abs] using A.hF _ _
  induction k with
  | zero => simp [stochasticNodes, map_zero]
  | succ k ih =>
    have he := expected_nodes_step hW A v mv M hv hgen h x k
    rw [integral_sub (hi (k+1)) (hi k)] at he
    push_cast at he ⊢
    linarith

end SLEExactGauge.BrownianCalculus

namespace SLEExactGauge.BrownianCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

 

theorem expected_nodes_limit {W : Measure Driver}
    (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W)
    (A : SmoothTest E) (v : E → ℝ → E)
    (mv : Measurable (Function.uncurry v)) (M : ℝ) (hv : ∀ x b, ‖v x b‖ ≤ M)
    (hgen : ∀ x b, A.D x b (v x b)+deriv (deriv (A.F x)) b/2 ≤ 0)
    (h : ℕ → ℝ≥0) (k : ℕ → ℕ) (x : E) (t : ℝ≥0) (X : Driver → E)
    (hh : Tendsto (fun n => (h n:ℝ)) atTop (𝓝 0))
    (htime : Tendsto (fun n => (k n:ℝ≥0)*h n) atTop (𝓝 t))
    (hX : ∀ᵐ (b : Driver) ∂W, Tendsto (fun n => stochasticNodes v (h n) x (k n) b) atTop (𝓝 (X b))) :
    (∫ b, A.F (X b) (b t) ∂W) ≤ A.F x 0 := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  have hc : ∀ᵐ (b : Driver) ∂W, Tendsto (fun n =>
      A.F (stochasticNodes v (h n) x (k n) b) (b ((k n:ℝ≥0)*h n)))
      atTop (𝓝 (A.F (X b) (b t))) := by
    filter_upwards [hX] with b hb
    exact A.cF.continuousAt.tendsto.comp (hb.prodMk_nhds (b.continuous.continuousAt.tendsto.comp htime))
  have hi : Tendsto (fun n => ∫ b : Driver,
      A.F (stochasticNodes v (h n) x (k n) b) (b ((k n:ℝ≥0)*h n)) ∂W)
      atTop (𝓝 (∫ b, A.F (X b) (b t) ∂W)) :=
    tendsto_integral_of_dominated_convergence (fun _ : Driver => A.C₀)
    (fun n => (A.mF.comp ((measurable_nodes_driver v mv (h n) x (k n)).prodMk
      (continuous_eval_const _).measurable)).aestronglyMeasurable)
    (integrable_const A.C₀)
    (fun n => Filter.Eventually.of_forall fun b => by simpa only [Real.norm_eq_abs] using A.hF _ _) hc
  have hk : Tendsto (fun n => (k n:ℝ)*(h n:ℝ)) atTop (𝓝 (t:ℝ)) := by
    simpa only [Function.comp_def, NNReal.coe_mul, NNReal.coe_natCast] using
      NNReal.continuous_coe.continuousAt.tendsto.comp htime
  have hs : Tendsto (fun n => Real.sqrt (h n:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hh
  have he : Tendsto (fun n => (k n:ℝ)*((A.Cx*M^2+A.Ccross*M/2)*(h n:ℝ)^2 +
      A.C₃/3*(h n:ℝ)*Real.sqrt (h n))) atTop (𝓝 0) := by
    have hh' := hk.mul (((tendsto_const_nhds (x := A.Cx*M^2+A.Ccross*M/2)).mul hh).add
      ((tendsto_const_nhds (x := A.C₃/3)).mul hs))
    convert! hh' using 1
    · ext n
      ring
    · simp
  have hb : Tendsto (fun n => A.F x 0+(k n:ℝ)*((A.Cx*M^2+A.Ccross*M/2)*(h n:ℝ)^2 +
      A.C₃/3*(h n:ℝ)*Real.sqrt (h n))) atTop (𝓝 (A.F x 0)) := by
    simpa using tendsto_const_nhds.add he
  exact le_of_tendsto_of_tendsto hi hb
    (Filter.Eventually.of_forall fun n => expected_nodes hW A v mv M hv hgen (h n) x (k n))

end SLEExactGauge.BrownianCalculus

namespace SLEExactGauge.BrownianCalculus

 

lemma expected_shifted_taylor {W : Measure Driver}
    (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W)
    (s h : ℝ≥0) (F : (Iic s → ℝ) → ℝ → ℝ) (B : (Iic s → ℝ) → ℝ)
    (hsm : ∀ p, ContDiff ℝ 3 (F p))
    (hm1 : Measurable (fun p => deriv (F p) (B p)))
    (hm2 : Measurable (fun p => deriv (deriv (F p)) (B p)))
    {C M₁ M₂ : ℝ} (hC : 0 ≤ C)
    (hb1 : ∀ p, |deriv (F p) (B p)| ≤ M₁)
    (hb2 : ∀ p, |deriv (deriv (F p)) (B p)| ≤ M₂)
    (hb3 : ∀ p x, |iteratedDeriv 3 (F p) x| ≤ C)
    (hi : Integrable (fun b => F (history s b) (B (history s b)+increment s h b) -
      F (history s b) (B (history s b))) W) :
    |(∫ b, F (history s b) (B (history s b)+increment s h b) -
      F (history s b) (B (history s b)) ∂W) -
      (h:ℝ)/2 * (∫ b, deriv (deriv (F (history s b))) (B (history s b)) ∂W)| ≤
      C/3 * (h:ℝ) * Real.sqrt h := by
  let c := fun p : Iic s → ℝ => B p-p ⟨s,by simp⟩
  let f := fun p u => F p (u+c p)
  have hbase (p : Iic s → ℝ) : p ⟨s,by simp⟩+c p = B p := by dsimp [c]; ring
  have hd1 (p : Iic s → ℝ) : deriv (f p) = fun u => deriv (F p) (u+c p) := by
    ext u
    exact deriv_comp_add_const (F p) (c p) u
  have hd2 (p : Iic s → ℝ) : deriv (deriv (f p)) = fun u => deriv (deriv (F p)) (u+c p) := by
    rw [hd1]
    ext u
    exact deriv_comp_add_const (deriv (F p)) (c p) u
  have hsmooth (p : Iic s → ℝ) : ContDiff ℝ 3 (f p) :=
    (hsm p).comp (contDiff_id.add contDiff_const)
  have hm1' : Measurable (fun p => deriv (f p) (p ⟨s,by simp⟩)) := by
    simpa only [hd1, hbase] using hm1
  have hm2' : Measurable (fun p => deriv (deriv (f p)) (p ⟨s,by simp⟩)) := by
    simpa only [hd2, hbase] using hm2
  have hf (b : Driver) : f (history s b) (b (s+h))-f (history s b) (b s) =
      F (history s b) (B (history s b)+increment s h b)-F (history s b) (B (history s b)) := by
    dsimp [f,c,history,increment]
    congr 2 <;> ring
  have hi' : Integrable (fun b => f (history s b) (b (s+h))-f (history s b) (b s)) W := by
    simpa only [hf] using hi
  have he := expected_taylor_step hW s h f hsmooth hm1' hm2' hC
    (fun p => by simpa only [hd1,hbase] using hb1 p)
    (fun p => by simpa only [hd2,hbase] using hb2 p)
    (fun p u => by simpa only [f, iteratedDeriv_comp_add_const, Function.comp_apply] using hb3 p (u+c p)) hi'
  simpa only [hf,hd2,show ∀ b : Driver, b s+c (history s b) = B (history s b) from
    fun b => hbase (history s b)] using he

end SLEExactGauge.BrownianCalculus

namespace SLEExactGauge.BrownianCalculus

 

lemma expected_shift_with_drift {W : Measure Driver}
    (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W)
    (s h : ℝ≥0) (f : (Iic s → ℝ) → ℝ → ℝ) (B old : (Iic s → ℝ) → ℝ)
    (mf : Measurable (Function.uncurry f)) (mB : Measurable B) (mOld : Measurable old)
    (hsm : ∀ p, ContDiff ℝ 3 (f p))
    (hm1 : Measurable (fun p => deriv (f p) (B p)))
    (hm2 : Measurable (fun p => deriv (deriv (f p)) (B p)))
    {C₀ C₁ C₂ C₃ R : ℝ} (hC₃ : 0 ≤ C₃)
    (hb0 : ∀ p u, |f p u| ≤ C₀) (hOld : ∀ p, |old p| ≤ C₀)
    (hb1 : ∀ p, |deriv (f p) (B p)| ≤ C₁)
    (hb2 : ∀ p, |deriv (deriv (f p)) (B p)| ≤ C₂)
    (hb3 : ∀ p u, |iteratedDeriv 3 (f p) u| ≤ C₃)
    (hstep : ∀ p, f p (B p)-old p+(h:ℝ)/2*deriv (deriv (f p)) (B p) ≤ R) :
    (∫ b, f (history s b) (B (history s b)+increment s h b)-old (history s b) ∂W) ≤
      R + C₃/3*(h:ℝ)*Real.sqrt h := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  let step := fun b : Driver => f (history s b) (B (history s b))
  let next := fun b : Driver => f (history s b) (B (history s b)+increment s h b)
  let prev := fun b : Driver => old (history s b)
  let Q := fun b : Driver => deriv (deriv (f (history s b))) (B (history s b))
  have ms : Measurable step := mf.comp ((measurable_history s).prodMk (mB.comp (measurable_history s)))
  have mn : Measurable next := mf.comp ((measurable_history s).prodMk
    ((mB.comp (measurable_history s)).add (measurable_increment s h)))
  have mp : Measurable prev := mOld.comp (measurable_history s)
  have mq : Measurable Q := hm2.comp (measurable_history s)
  have is : Integrable step W := (integrable_const C₀).mono' ms.aestronglyMeasurable
    (Filter.Eventually.of_forall fun b => by simpa only [Real.norm_eq_abs] using hb0 _ _)
  have inx : Integrable next W := (integrable_const C₀).mono' mn.aestronglyMeasurable
    (Filter.Eventually.of_forall fun b => by simpa only [Real.norm_eq_abs] using hb0 _ _)
  have ip : Integrable prev W := (integrable_const C₀).mono' mp.aestronglyMeasurable
    (Filter.Eventually.of_forall fun b => by simpa only [Real.norm_eq_abs] using hOld _)
  have iq : Integrable Q W := (integrable_const C₂).mono' mq.aestronglyMeasurable
    (Filter.Eventually.of_forall fun b => by simpa only [Real.norm_eq_abs] using hb2 _)
  have ht := expected_shifted_taylor hW s h f B hsm hm1 hm2 hC₃ hb1 hb2 hb3 (inx.sub is)
  change |(∫ b, next b-step b ∂W)-(h:ℝ)/2*(∫ b, Q b ∂W)| ≤ _ at ht
  have hi := integral_mono_ae ((is.sub ip).add (iq.const_mul ((h:ℝ)/2)))
    (integrable_const R) (Filter.Eventually.of_forall fun b => hstep (history s b))
  have hi' : (∫ b, step b-prev b+(h:ℝ)/2*Q b ∂W) ≤ R := by
    simpa only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul,
      Pi.add_apply, Pi.sub_apply] using hi
  change (∫ b, (step-prev) b+(h:ℝ)/2*Q b ∂W) ≤ R at hi'
  rw [integral_add (is.sub ip) (iq.const_mul ((h:ℝ)/2)), integral_const_mul] at hi'
  change (∫ b, step b-prev b ∂W)+(h:ℝ)/2*(∫ b, Q b ∂W) ≤ R at hi'
  rw [integral_sub is ip] at hi'
  rw [integral_sub inx is] at ht
  change (∫ b, next b-prev b ∂W) ≤ _
  rw [integral_sub inx ip]
  linarith [le_abs_self ((∫ b, next b ∂W)-(∫ b, step b ∂W)-(h:ℝ)/2*(∫ b, Q b ∂W))]

end SLEExactGauge.BrownianCalculus

namespace SLEExactGauge.BrownianCalculus
open Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [BorelSpace E] [SecondCountableTopology E] in
lemma SmoothTest.euler_generator_error (A : SmoothTest E) (x v : E) (b : ℝ)
    {h M : ℝ} (hh : 0 ≤ h) (hv : ‖v‖ ≤ M)
    (hg : A.D x b v+deriv (deriv (A.F x)) b/2 ≤ 0) :
    A.F (x+h • v) b-A.F x b+h/2*deriv (deriv (A.F (x+h • v))) b ≤
      (A.Cx*M^2+A.Ccross*M/2)*h^2 := by
  have hy : ‖x+h • v-x‖ ≤ h*M := by
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    exact mul_le_mul_of_nonneg_left hv hh
  have hd := state_euler_remainder (fun x => A.hD x b) A.hCx
    (fun x y => A.hLipD x y b) x v hh hv
  have hb := (le_abs_self _).trans (A.hLipB2 (x+h • v) x b)
  have hc := hb.trans (mul_le_mul_of_nonneg_left hy A.hCcross)
  have hg' := mul_nonpos_of_nonneg_of_nonpos hh hg
  have hc' := mul_le_mul_of_nonneg_left hc (div_nonneg hh (by norm_num : (0:ℝ) ≤ 2))
  nlinarith

 

lemma expected_active_euler_step {W : Measure Driver}
    (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W)
    (s h : ℝ≥0) (A : SmoothTest E)
    (X V : (Iic s → ℝ) → E) (B : (Iic s → ℝ) → ℝ)
    (mX : Measurable X) (mV : Measurable V) (mB : Measurable B)
    (S : Set (Iic s → ℝ)) (hS : MeasurableSet S)
    {M : ℝ} (hV : ∀ p, ‖V p‖ ≤ M)
    (hgen : ∀ p ∈ S, A.D (X p) (B p) (V p)+deriv (deriv (A.F (X p))) (B p)/2 ≤ 0) :
    (∫ b, (if history s b ∈ S then
      A.F (X (history s b)+(h:ℝ) • V (history s b)) (B (history s b)+increment s h b)
      else A.F (X (history s b)) (B (history s b)))-
      A.F (X (history s b)) (B (history s b)) ∂W) ≤
      (A.Cx*M^2+A.Ccross*M/2)*(h:ℝ)^2+A.C₃/3*(h:ℝ)*Real.sqrt h := by
  classical
  let Y := fun p => X p+(h:ℝ) • V p
  let old := fun p => A.F (X p) (B p)
  let f := fun p u => if p ∈ S then A.F (Y p) u else old p
  have mY : Measurable Y := mX.add (mV.const_smul (h:ℝ))
  have mOld : Measurable old := A.mF.comp (mX.prodMk mB)
  have mf : Measurable (Function.uncurry f) :=
    (A.mF.comp ((mY.comp measurable_fst).prodMk measurable_snd)).ite
      (hS.preimage measurable_fst) (mOld.comp measurable_fst)
  have hd1 (p : Iic s → ℝ) : deriv (f p) = fun u => if p ∈ S then deriv (A.F (Y p)) u else 0 := by
    by_cases hp : p ∈ S <;> simp [f,hp]
  have hd2 (p : Iic s → ℝ) : deriv (deriv (f p)) = fun u =>
      if p ∈ S then deriv (deriv (A.F (Y p))) u else 0 := by
    rw [hd1]
    by_cases hp : p ∈ S <;> simp [hp]
  have hm1 : Measurable (fun p => deriv (f p) (B p)) := by
    simp only [hd1]
    exact (A.mB1.comp (mY.prodMk mB)).ite hS measurable_const
  have hm2 : Measurable (fun p => deriv (deriv (f p)) (B p)) := by
    simp only [hd2]
    exact (A.mB2.comp (mY.prodMk mB)).ite hS measurable_const
  have hC₁ : 0 ≤ A.C₁ := (abs_nonneg _).trans (A.hB1 0 0)
  have hC₂ : 0 ≤ A.C₂ := (abs_nonneg _).trans (A.hB2 0 0)
  have hM : 0 ≤ M := (norm_nonneg _).trans (hV (fun _ => 0))
  refine expected_shift_with_drift (C₀ := A.C₀) (C₁ := A.C₁) (C₂ := A.C₂)
    hW s h f B old mf mB mOld ?_ hm1 hm2 A.hC₃ ?_ ?_ ?_ ?_ ?_ ?_
  · intro p
    by_cases hp : p ∈ S
    · simpa only [f,ite_eq_left hp] using A.hsm (Y p)
    · simpa only [f,ite_eq_right hp] using (contDiff_const (c := old p) : ContDiff ℝ 3 _)
  · intro p u
    by_cases hp : p ∈ S
    · simpa only [f,ite_eq_left hp] using A.hF (Y p) u
    · simpa only [f,ite_eq_right hp,old] using A.hF (X p) (B p)
  · intro p
    exact A.hF _ _
  · intro p
    by_cases hp : p ∈ S
    · simpa only [hd1,ite_eq_left hp] using A.hB1 (Y p) (B p)
    · simpa only [hd1,ite_eq_right hp,abs_zero] using hC₁
  · intro p
    by_cases hp : p ∈ S
    · simpa only [hd2,ite_eq_left hp] using A.hB2 (Y p) (B p)
    · simpa only [hd2,ite_eq_right hp,abs_zero] using hC₂
  · intro p u
    by_cases hp : p ∈ S
    · simpa only [f,ite_eq_left hp] using A.hB3 (Y p) u
    · simpa [f,hp,iteratedDeriv_const] using A.hC₃
  · intro p
    rw [hd2]
    by_cases hp : p ∈ S
    · simpa only [f,ite_eq_left hp,old,Y] using A.euler_generator_error (X p) (V p) (B p)
        h.coe_nonneg (hV p) (hgen p hp)
    · simp only [f,ite_eq_right hp,sub_self,mul_zero,add_zero]
      exact mul_nonneg (add_nonneg (mul_nonneg A.hCx (sq_nonneg M))
        (div_nonneg (mul_nonneg A.hCcross hM) (by norm_num))) (sq_nonneg _)

end SLEExactGauge.BrownianCalculus

namespace SLEExactGauge.BrownianCalculus
open Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

 

def frozenNodes (v : E → ℝ → E) (U : ℕ → Set ((ℝ≥0 → ℝ) × (E × ℝ)))
    (h : ℝ≥0) (q : E × ℝ) : ℕ → (ℝ≥0 → ℝ) → E × ℝ
  | 0, _ => q
  | k+1, b =>
    let qk := frozenNodes v U h q k b
    if (b,qk) ∈ U k then
      (qk.1+(h:ℝ) • v qk.1 qk.2, qk.2+(b (((k:ℝ≥0)+1)*h)-b ((k:ℝ≥0)*h)))
    else qk

lemma measurable_frozenNodes (v : E → ℝ → E) (mv : Measurable (Function.uncurry v))
    (U : ℕ → Set ((ℝ≥0 → ℝ) × (E × ℝ))) (mU : ∀ k, MeasurableSet (U k))
    (h : ℝ≥0) (q : E × ℝ) (k : ℕ) : Measurable (frozenNodes v U h q k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    exact ((ih.fst.add ((mv.comp ih).const_smul (h:ℝ))).prodMk
      (ih.snd.add ((measurable_pi_apply _).sub (measurable_pi_apply _)))).ite
      ((mU k).preimage (measurable_id.prodMk ih)) ih

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma frozenNodes_congr (v : E → ℝ → E) (U : ℕ → Set ((ℝ≥0 → ℝ) × (E × ℝ)))
    (h : ℝ≥0) (q : E × ℝ)
    (hU : ∀ (k : ℕ) b c, (∀ t ≤ (k:ℝ≥0)*h, b t = c t) → ∀ x,
      ((b,x) ∈ U k ↔ (c,x) ∈ U k)) (k : ℕ)
    {b c : ℝ≥0 → ℝ} (he : ∀ t ≤ (k:ℝ≥0)*h, b t = c t) :
    frozenNodes v U h q k b = frozenNodes v U h q k c := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hle : (k:ℝ≥0)*h ≤ ((k+1:ℕ):ℝ≥0)*h :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ k) h.coe_nonneg
    have he' : ∀ t ≤ (k:ℝ≥0)*h, b t = c t := fun t ht => he t (ht.trans hle)
    have hn := ih he'
    have hu := hU k b c he' (frozenNodes v U h q k c)
    have hb := he (((k:ℝ≥0)+1)*h) (by push_cast; exact le_rfl)
    simp only [frozenNodes, hn, hu, hb, he _ hle]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma frozenNodes_history (v : E → ℝ → E) (U : ℕ → Set ((ℝ≥0 → ℝ) × (E × ℝ)))
    (h : ℝ≥0) (q : E × ℝ)
    (hU : ∀ (k : ℕ) b c, (∀ t ≤ (k:ℝ≥0)*h, b t = c t) → ∀ x,
      ((b,x) ∈ U k ↔ (c,x) ∈ U k)) (k : ℕ) (b : Driver) :
    frozenNodes v U h q k (extendHistory ((k:ℝ≥0)*h) (history ((k:ℝ≥0)*h) b)) =
      frozenNodes v U h q k b := by
  apply frozenNodes_congr v U h q hU
  intro t ht
  simp only [extendHistory,dite_eq_left ht,history]

lemma expected_frozen_step {W : Measure Driver}
    (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W)
    (A : SmoothTest E) (v : E → ℝ → E) (mv : Measurable (Function.uncurry v))
    (U : ℕ → Set ((ℝ≥0 → ℝ) × (E × ℝ))) (mU : ∀ k, MeasurableSet (U k))
    (h : ℝ≥0) (q : E × ℝ)
    (hU : ∀ (k : ℕ) b c, (∀ t ≤ (k:ℝ≥0)*h, b t = c t) → ∀ x,
      ((b,x) ∈ U k ↔ (c,x) ∈ U k))
    {M : ℝ} (hv : ∀ x b, ‖v x b‖ ≤ M)
    (hg : ∀ k b x, (b,x) ∈ U k → A.D x.1 x.2 (v x.1 x.2)+deriv (deriv (A.F x.1)) x.2/2 ≤ 0)
    (k : ℕ) :
    (∫ b : Driver, A.F (frozenNodes v U h q (k+1) b).1 (frozenNodes v U h q (k+1) b).2-
      A.F (frozenNodes v U h q k b).1 (frozenNodes v U h q k b).2 ∂W) ≤
      (A.Cx*M^2+A.Ccross*M/2)*(h:ℝ)^2+A.C₃/3*(h:ℝ)*Real.sqrt h := by
  let s := (k:ℝ≥0)*h
  let X := fun p : Iic s → ℝ => frozenNodes v U h q k (extendHistory s p)
  have mX : Measurable X := (measurable_frozenNodes v mv U mU h q k).comp (measurable_extendHistory s)
  let S := {p : Iic s → ℝ | (extendHistory s p,X p) ∈ U k}
  have mS : MeasurableSet S := (mU k).preimage ((measurable_extendHistory s).prodMk mX)
  have he := expected_active_euler_step hW s h A (fun p => (X p).1)
    (fun p => v (X p).1 (X p).2) (fun p => (X p).2) mX.fst (mv.comp mX) mX.snd S mS
    (fun p => hv _ _) (fun p hp => hg k (extendHistory s p) (X p) hp)
  have hx (b : Driver) : X (history s b) = frozenNodes v U h q k b :=
    frozenNodes_history v U h q hU k b
  have hs (b : Driver) : history s b ∈ S ↔ ((b : ℝ≥0 → ℝ),frozenNodes v U h q k b) ∈ U k := by
    change (extendHistory s (history s b),X (history s b)) ∈ U k ↔ _
    rw [hx]
    apply hU k _ _
    intro t ht
    change t ≤ s at ht
    simp only [extendHistory,dite_eq_left ht,history]
  have ht : s+h = ((k:ℝ≥0)+1)*h := by dsimp [s]; ring
  convert! he using 1
  congr 1
  funext b
  rw [hx,hs]
  simp only [frozenNodes,increment,ht,s]
  split_ifs <;> rfl

end SLEExactGauge.BrownianCalculus
end
end
end
end
end
end

end OAI
