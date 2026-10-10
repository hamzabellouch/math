import Mathlib
import OAI.Probability.SKSupport.Diffusion.ProgressiveIntegralMeasurable
import OAI.Probability.SKSupport.Foundations.ElementaryControl

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open WeakIto

structure BoundedLipschitzDrift where
  f : ℝ → ℝ → ℝ
  bound : ℝ≥0
  lip : ℝ≥0
  measurable : Measurable (fun p : ℝ × ℝ => f p.1 p.2)
  bounded : ∀ t x, |f t x| ≤ bound
  lipschitz : ∀ t, LipschitzWith lip (f t)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma progressive_time_measurable (ℱ : Filtration ℝ≥0 mΩ) {α : ℝ≥0 → Ω → ℝ}
    (ha : IsProgressive ℱ α) (ω : Ω) : Measurable (fun t : ℝ => α (Real.toNNReal t) ω) :=
  ((progressive_joint_measurable ℱ ha).comp
    (measurable_id.prodMk measurable_const)).comp measurable_real_toNNReal

lemma progressive_bounded_integrable (ℱ : Filtration ℝ≥0 mΩ) {α : ℝ≥0 → Ω → ℝ}
    (ha : IsProgressive ℱ α) {D : ℝ} (hb : ∀ t ω, |α t ω| ≤ D) (ω : Ω) (a b : ℝ) :
    IntervalIntegrable (fun t => α (Real.toNNReal t) ω) volume a b := by
  apply (intervalIntegrable_const (c := D)).mono_fun
  · exact (progressive_time_measurable ℱ ha ω).aestronglyMeasurable
  · filter_upwards [] with t
    simpa only [Real.norm_eq_abs] using (hb (Real.toNNReal t) ω).trans (le_abs_self D)

def timePrimitive (α : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in (0:ℝ)..(t:ℝ), α (Real.toNNReal s) ω

lemma timePrimitive_continuous (ℱ : Filtration ℝ≥0 mΩ) {α : ℝ≥0 → Ω → ℝ}
    (ha : IsProgressive ℱ α) {D : ℝ} (hb : ∀ t ω, |α t ω| ≤ D) (ω : Ω) :
    Continuous (fun t => timePrimitive α t ω) :=
  (intervalIntegral.continuous_primitive (progressive_bounded_integrable ℱ ha hb ω) 0).comp
    continuous_subtype_val

lemma timePrimitive_progressive (ℱ : Filtration ℝ≥0 mΩ) {α : ℝ≥0 → Ω → ℝ}
    (ha : IsProgressive ℱ α) {D : ℝ} (hb : ∀ t ω, |α t ω| ≤ D) :
    IsProgressive ℱ (timePrimitive α) := by
  have hm : StronglyAdapted ℱ (timePrimitive α) := by
    intro t
    have hh := progressive_integral_measurable ℱ ha t (w := fun _ => 1) measurable_const
    change StronglyMeasurable[ℱ t] (fun ω => ∫ s in (0:ℝ)..(t:ℝ), α (Real.toNNReal s) ω)
    simpa only [one_mul] using hh.stronglyMeasurable
  exact (hm.isStronglyProgressive_of_continuous (timePrimitive_continuous ℱ ha hb)).isProgressive

lemma timePrimitive_bound (ℱ : Filtration ℝ≥0 mΩ) {α : ℝ≥0 → Ω → ℝ}
    (ha : IsProgressive ℱ α) {D : ℝ} (hb : ∀ t ω, |α t ω| ≤ D) (t : ℝ≥0) (ω : Ω) :
    |timePrimitive α t ω| ≤ D*(t:ℝ) := by
  calc
    |timePrimitive α t ω| ≤ ∫ s in (0:ℝ)..(t:ℝ), |α (Real.toNNReal s) ω| :=
      intervalIntegral.abs_integral_le_integral_abs t.coe_nonneg
    _ ≤ ∫ _s in (0:ℝ)..(t:ℝ), D :=
      intervalIntegral.integral_mono t.coe_nonneg
        (progressive_bounded_integrable ℱ ha hb ω 0 t).abs intervalIntegrable_const
        (fun _ => hb _ _)
    _ = D*(t:ℝ) := by simp [mul_comm]

namespace BoundedLipschitzDrift

variable (b : BoundedLipschitzDrift)

def action (B Y : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ := b.f t (B t ω+Y t ω)

lemma action_progressive (ℱ : Filtration ℝ≥0 mΩ) {B Y : ℝ≥0 → Ω → ℝ}
    (hB : IsProgressive ℱ B) (hY : IsProgressive ℱ Y) : IsProgressive ℱ (b.action B Y) := by
  intro t
  exact b.measurable.comp ((measurable_subtype_coe.comp (measurable_subtype_coe.comp
    measurable_fst)).prodMk ((hB t).add (hY t)))

omit mΩ in
lemma action_bound (B Y : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    |b.action B Y t ω| ≤ b.bound := b.bounded _ _

def correctionIter (b : BoundedLipschitzDrift) (B : ℝ≥0 → Ω → ℝ) : ℕ → ℝ≥0 → Ω → ℝ
  | 0 => fun _ _ => 0
  | n+1 => timePrimitive (b.action B (correctionIter b B n))

lemma correctionIter_progressive (ℱ : Filtration ℝ≥0 mΩ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsProgressive ℱ B) (n : ℕ) : IsProgressive ℱ (b.correctionIter B n) := by
  induction n with
  | zero => exact isProgressive_const ℱ 0
  | succ n hn => exact timePrimitive_progressive ℱ (b.action_progressive ℱ hB hn) (b.action_bound _ _)

lemma correctionIter_continuous (ℱ : Filtration ℝ≥0 mΩ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsProgressive ℱ B) (n : ℕ) (ω : Ω) : Continuous (fun t => b.correctionIter B n t ω) := by
  cases n with
  | zero => exact continuous_const
  | succ n =>
    exact timePrimitive_continuous ℱ
      (b.action_progressive ℱ hB (b.correctionIter_progressive ℱ hB n)) (b.action_bound _ _) ω

lemma correctionIter_bound (ℱ : Filtration ℝ≥0 mΩ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsProgressive ℱ B) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    |b.correctionIter B n t ω| ≤ (b.bound:ℝ)*(t:ℝ) := by
  cases n with
  | zero => simpa only [correctionIter,abs_zero] using mul_nonneg b.bound.coe_nonneg t.coe_nonneg
  | succ n =>
    exact timePrimitive_bound ℱ
      (b.action_progressive ℱ hB (b.correctionIter_progressive ℱ hB n)) (b.action_bound _ _) t ω

def rate : ℝ := 2*(b.lip:ℝ)+1

lemma rate_pos : 0 < b.rate := by unfold rate; positivity
lemma one_le_rate : 1 ≤ b.rate := by unfold rate; linarith [b.lip.coe_nonneg]

lemma integral_exp_rate (t : ℝ≥0) :
    (∫ s in (0:ℝ)..(t:ℝ), Real.exp (b.rate*s))*b.rate = Real.exp (b.rate*t)-1 := by
  have hd (s : ℝ) : HasDerivAt (fun r => Real.exp (b.rate*r))
      (Real.exp (b.rate*s)*b.rate) s := by
    convert ((hasDerivAt_id s).const_mul b.rate).exp using 1 <;> simp
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul continuous_const).intervalIntegrable _ _)
    (a := (0:ℝ)) (b := (t:ℝ))
  simpa only [intervalIntegral.integral_mul_const,mul_zero,Real.exp_zero] using hh

lemma integral_exp_contraction {A : ℝ} (hA : 0 ≤ A) (t : ℝ≥0) :
    (∫ s in (0:ℝ)..(t:ℝ), (b.lip:ℝ)*A*Real.exp (b.rate*s)) ≤
      A/2*Real.exp (b.rate*t) := by
  rw [intervalIntegral.integral_const_mul]
  have hi : 0 ≤ ∫ s in (0:ℝ)..(t:ℝ), Real.exp (b.rate*s) :=
    intervalIntegral.integral_nonneg t.coe_nonneg (fun _ _ => (Real.exp_pos _).le)
  have hl : (b.lip:ℝ) ≤ b.rate/2 := by unfold rate; linarith
  calc
    _ ≤ (b.rate/2)*A*(∫ s in (0:ℝ)..(t:ℝ), Real.exp (b.rate*s)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hl hA) hi
    _ = A/2*(Real.exp (b.rate*t)-1) := by rw [← b.integral_exp_rate t]; ring
    _ ≤ A/2*Real.exp (b.rate*t) := by nlinarith

lemma timePrimitive_action_sub_estimate (ℱ : Filtration ℝ≥0 mΩ)
    {B Y Z : ℝ≥0 → Ω → ℝ} (hB : IsProgressive ℱ B) (hY : IsProgressive ℱ Y)
    (hZ : IsProgressive ℱ Z) {A : ℝ} (hA : 0 ≤ A) (t : ℝ≥0) (ω : Ω)
    (he : ∀ s ≤ t, |Y s ω-Z s ω| ≤ A*Real.exp (b.rate*s)) :
    |timePrimitive (b.action B Y) t ω-timePrimitive (b.action B Z) t ω| ≤
      A/2*Real.exp (b.rate*t) := by
  have hiY := progressive_bounded_integrable ℱ (b.action_progressive ℱ hB hY) (b.action_bound B Y) ω 0 t
  have hiZ := progressive_bounded_integrable ℱ (b.action_progressive ℱ hB hZ) (b.action_bound B Z) ω 0 t
  rw [timePrimitive,timePrimitive,← intervalIntegral.integral_sub hiY hiZ]
  apply le_trans _ (b.integral_exp_contraction hA t)
  rw [← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le t.coe_nonneg _
    ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _)
  filter_upwards [] with s hs
  have hst : Real.toNNReal s ≤ t := Real.toNNReal_le_iff_le_coe.mpr hs.2
  have hh := he _ hst
  have hl := (b.lipschitz (Real.toNNReal s)).dist_le_mul
    (B (Real.toNNReal s) ω+Y (Real.toNNReal s) ω)
    (B (Real.toNNReal s) ω+Z (Real.toNNReal s) ω)
  simp only [Real.dist_eq,add_sub_add_left_eq_sub] at hl
  simp only [Real.coe_toNNReal _ hs.1.le] at hh
  change |b.action B Y (Real.toNNReal s) ω-b.action B Z (Real.toNNReal s) ω| ≤ _
  exact hl.trans (by simpa only [mul_assoc,Pi.mul_apply,Function.comp_apply,id_eq] using mul_le_mul_of_nonneg_left hh b.lip.coe_nonneg)

lemma correctionIter_diff_bound (ℱ : Filtration ℝ≥0 mΩ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsProgressive ℱ B) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    |b.correctionIter B (n+1) t ω-b.correctionIter B n t ω| ≤
      (b.bound:ℝ)*(1/2:ℝ)^n*Real.exp (b.rate*t) := by
  induction n generalizing t with
  | zero =>
    simp only [correctionIter,_root_.sub_zero,pow_zero,mul_one]
    apply (timePrimitive_bound ℱ (b.action_progressive ℱ hB (isProgressive_const ℱ 0))
      (b.action_bound _ _) t ω).trans
    apply mul_le_mul_of_nonneg_left _ b.bound.coe_nonneg
    have ht : (t:ℝ) ≤ b.rate*t := by nlinarith [b.one_le_rate,t.coe_nonneg]
    linarith [Real.add_one_le_exp (b.rate*t)]
  | succ n hn =>
    have hh := b.timePrimitive_action_sub_estimate ℱ hB
      (b.correctionIter_progressive ℱ hB (n+1)) (b.correctionIter_progressive ℱ hB n)
      (show 0 ≤ (b.bound:ℝ)*(1/2:ℝ)^n by positivity) t ω (fun s _ => hn s)
    convert hh using 1 <;> simp only [correctionIter,pow_succ]
    ring

def correction (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  atTop.limUnder (fun n => b.correctionIter B n t ω)

lemma correctionIter_tendsto (ℱ : Filtration ℝ≥0 mΩ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsProgressive ℱ B) (t : ℝ≥0) (ω : Ω) :
    Tendsto (fun n => b.correctionIter B n t ω) atTop (𝓝 (b.correction B t ω)) := by
  apply CauchySeq.tendsto_limUnder
  apply cauchySeq_of_le_geometric (1/2:ℝ) ((b.bound:ℝ)*Real.exp (b.rate*t)) (by norm_num)
  intro n
  rw [Real.dist_eq,abs_sub_comm]
  convert b.correctionIter_diff_bound ℱ hB n t ω using 1
  ring

lemma correction_progressive (ℱ : Filtration ℝ≥0 mΩ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsProgressive ℱ B) : IsProgressive ℱ (b.correction B) := by
  intro t
  have hm (n : ℕ) : StronglyMeasurable[(Subtype.instMeasurableSpace).prod (ℱ t)]
      (fun p : Iic t × Ω => b.correctionIter B n p.1 p.2) :=
    (b.correctionIter_progressive ℱ hB n t).stronglyMeasurable
  let : MeasurableSpace Ω := ℱ t
  exact (StronglyMeasurable.limUnder hm).measurable

lemma correction_bound (ℱ : Filtration ℝ≥0 mΩ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsProgressive ℱ B) (t : ℝ≥0) (ω : Ω) :
    |b.correction B t ω| ≤ (b.bound:ℝ)*(t:ℝ) :=
  le_of_tendsto (b.correctionIter_tendsto ℱ hB t ω).abs
    (Eventually.of_forall (fun n => b.correctionIter_bound ℱ hB n t ω))

lemma correction_eq_integral (ℱ : Filtration ℝ≥0 mΩ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsProgressive ℱ B) (t : ℝ≥0) (ω : Ω) :
    b.correction B t ω = timePrimitive (b.action B (b.correction B)) t ω := by
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun s : ℝ => b.action B (b.correctionIter B n) (Real.toNNReal s) ω)
      (volume.restrict (Ioc 0 (t:ℝ))) :=
    (progressive_time_measurable ℱ (b.action_progressive ℱ hB
      (b.correctionIter_progressive ℱ hB n)) ω).aestronglyMeasurable
  have hd (n : ℕ) : ∀ᵐ s ∂volume.restrict (Ioc 0 (t:ℝ)),
      ‖b.action B (b.correctionIter B n) (Real.toNNReal s) ω‖ ≤ (b.bound:ℝ) :=
    Eventually.of_forall (fun s => b.action_bound _ _ _ _)
  have hl : ∀ᵐ s ∂volume.restrict (Ioc 0 (t:ℝ)), Tendsto
      (fun n => b.action B (b.correctionIter B n) (Real.toNNReal s) ω) atTop
      (𝓝 (b.action B (b.correction B) (Real.toNNReal s) ω)) := by
    filter_upwards [] with s
    exact ((b.lipschitz (Real.toNNReal s)).continuous.tendsto _).comp
      (tendsto_const_nhds.add (b.correctionIter_tendsto ℱ hB (Real.toNNReal s) ω))
  have hi : Integrable (fun _ : ℝ => (b.bound:ℝ)) (volume.restrict (Ioc 0 (t:ℝ))) :=
    (intervalIntegrable_const (c := (b.bound:ℝ))).1
  have hh := tendsto_integral_of_dominated_convergence (fun _ => (b.bound:ℝ)) hm hi hd hl
  have hh' : Tendsto (fun n => b.correctionIter B (n+1) t ω) atTop
      (𝓝 (timePrimitive (b.action B (b.correction B)) t ω)) := by
    simpa only [correctionIter,timePrimitive,intervalIntegral.integral_of_le t.coe_nonneg] using hh
  exact tendsto_nhds_unique ((b.correctionIter_tendsto ℱ hB t ω).comp (tendsto_add_atTop_nat 1)) hh'

lemma correction_continuous (ℱ : Filtration ℝ≥0 mΩ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsProgressive ℱ B) (ω : Ω) : Continuous (fun t => b.correction B t ω) := by
  have he : (fun t => b.correction B t ω) =
      (fun t => timePrimitive (b.action B (b.correction B)) t ω) :=
    funext (fun t => b.correction_eq_integral ℱ hB t ω)
  rw [he]
  exact timePrimitive_continuous ℱ (b.action_progressive ℱ hB (b.correction_progressive ℱ hB))
    (b.action_bound _ _) ω

def solution (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ := B t ω+b.correction B t ω

lemma solution_progressive (ℱ : Filtration ℝ≥0 mΩ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsProgressive ℱ B) : IsProgressive ℱ (b.solution B) := hB.add (b.correction_progressive ℱ hB)

lemma solution_eq (ℱ : Filtration ℝ≥0 mΩ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsProgressive ℱ B) (t : ℝ≥0) (ω : Ω) :
    b.solution B t ω = B t ω+∫ s in (0:ℝ)..(t:ℝ),
      b.f (Real.toNNReal s) (b.solution B (Real.toNNReal s) ω) := by
  change B t ω+b.correction B t ω = B t ω+_
  rw [b.correction_eq_integral ℱ hB t ω]
  rfl

lemma solution_continuous (ℱ : Filtration ℝ≥0 mΩ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsProgressive ℱ B) {ω : Ω} (hc : Continuous (fun t => B t ω)) :
    Continuous (fun t => b.solution B t ω) := hc.add (b.correction_continuous ℱ hB ω)

end BoundedLipschitzDrift
end ZeroTemperatureSK

end
end

end OAI
