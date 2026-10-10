import Mathlib
import OAI.Probability.Perceptron.Variational.FocusedShapeProbability

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy

lemma decoratedWeightedTotalE_measurable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) (hstep : Measurable step) (n : ℕ) (F : Fin n → X×S → ℝ)
    (hF : ∀ i, Measurable (F i)) : Measurable (decoratedWeightedTotalE step n F) := by
  have he : decoratedWeightedTotalE step n F = cascadeTotalE n ∘ decoratedCascadeTransform step n F := by
    funext p
    exact (decoratedWeightedTotalE_transform step hstep n F hF p).symm
  rw [he]
  exact (cascadeTotalE_measurable n).comp (decoratedCascadeTransform_measurable step hstep n F hF)

lemma decoratedWeightedTotalE_counting {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S → X)
    (n : ℕ) (z : Fin (n+1) → ℝ) (hz0 : 0 < z 0) (hz1 : z 0 < 1)
    (F : Fin (n+1) → X×S → ℝ) (x : X) :
    ∀ᵐ η ∂(decoratedCascadeLaw ν (n+1) z : Measure (DecoratedCascade S (n+1))),
      decoratedWeightedTotalE step (n+1) F (x,η) =
        ∫⁻ q : ℝ×(S×DecoratedCascade S n), ENNReal.ofReal (Real.exp (q.1+F 0 (x,q.2.1))) *
          decoratedWeightedTotalE step n (fun i => F i.succ) (step (x,q.2.1),q.2.2) ∂η := by
  have hreg := markedStableCountKernel_ae_eq
    ((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ) : Measure (DecoratedCascade S n))) hz0 hz1
  apply hreg.mono
  intro η hη
  conv_lhs => rw [decoratedWeightedTotalE]
  rw [hη]

def decoratedWeightedTotal {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ) (p : X×DecoratedCascade S n) : ℝ :=
      (decoratedWeightedTotalE step n F p).toReal

lemma decoratedWeightedTotal_transform {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) (hstep : Measurable step) (n : ℕ) (F : Fin n → X×S → ℝ)
    (hF : ∀ i, Measurable (F i)) (p : X×DecoratedCascade S n) :
    decoratedWeightedTotal step n F p = cascadeTotal n (decoratedCascadeTransform step n F p) :=
  congrArg ENNReal.toReal (decoratedWeightedTotalE_transform step hstep n F hF p).symm

lemma decoratedWeightedTotal_identDistrib {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S → X) (hstep : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) :
    IdentDistrib (fun η => decoratedWeightedTotal step n F (x,η)) (cascadeTotal n)
      (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)) (cascadeLaw n z) := by
  have hT : Measurable (fun η => decoratedCascadeTransform step n F (x,η)) :=
    (decoratedCascadeTransform_measurable step hstep n F hF).comp (measurable_const.prodMk measurable_id)
  have he : (fun η => decoratedWeightedTotal step n F (x,η)) =
      cascadeTotal n ∘ (fun η => decoratedCascadeTransform step n F (x,η)) := by
    funext η
    exact decoratedWeightedTotal_transform step hstep n F hF (x,η)
  rw [he]
  refine ⟨((cascadeTotal_measurable n).comp hT).aemeasurable,(cascadeTotal_measurable n).aemeasurable,?_⟩
  rw [← Measure.map_map (cascadeTotal_measurable n) hT,decoratedCascadeTransform_law ν step hstep n z hz0 hz1 F hF hI hM]

theorem decoratedCascade_log_identity {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S → X) (hstep : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) (c : ℝ) :
    (∫ η, Real.log (Real.exp c*decoratedWeightedTotal step n F (x,η) /
      decoratedWeightedTotal step n (fun _ _ => 0) (x,η)) ∂(decoratedCascadeLaw ν n z)) = c := by
  have hid := decoratedWeightedTotal_identDistrib ν step hstep n z hz0 hz1 F hF hI hM x
  have hiz := decoratedWeightedTotal_identDistrib ν step hstep n z hz0 hz1 (fun _ _ => 0)
    (fun _ => measurable_const) (by intro i y; simp only [mul_zero,Real.exp_zero]; exact integrable_const 1)
    (by intro i y; simp) x
  have hld := hid.comp Real.measurable_log
  have hlz := hiz.comp Real.measurable_log
  have hL := cascadeTotal_log_memLp_two n z hz hz0 hz1
  have hId := MemLp.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2) (hld.memLp_iff.mpr hL)
  have hIz := MemLp.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2) (hlz.memLp_iff.mpr hL)
  have hp := (cascadeTotal_regular n z hz hz0 hz1).1
  have hdpos := hid.symm.ae_snd measurableSet_Ioi hp
  have hzpos := hiz.symm.ae_snd measurableSet_Ioi hp
  have he : (fun η => Real.log (Real.exp c*decoratedWeightedTotal step n F (x,η) /
      decoratedWeightedTotal step n (fun _ _ => 0) (x,η))) =ᵐ[(decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n))]
      (fun η => c+Real.log (decoratedWeightedTotal step n F (x,η))-
        Real.log (decoratedWeightedTotal step n (fun _ _ => 0) (x,η))) := by
    filter_upwards [hdpos,hzpos] with η hη hg
    rw [Real.log_div (mul_ne_zero (Real.exp_ne_zero _) hη.ne') hg.ne',
      Real.log_mul (Real.exp_ne_zero _) hη.ne',Real.log_exp]
  have hsplit := integral_sub ((integrable_const c).add hId) hIz
  have hadd := integral_add (integrable_const c) hId
  have hdint := hld.integral_eq
  have hzint := hlz.integral_eq
  simp only [Pi.add_apply,Function.comp_apply] at hsplit hadd hdint hzint
  rw [integral_congr_ae he,hsplit,hadd,hdint,hzint]
  simp

lemma decoratedCascade_log_difference_memLp {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S → X) (hstep : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) :
    MemLp (fun η => Real.log (decoratedWeightedTotal step n F (x,η))-
        Real.log (decoratedWeightedTotal step n (fun _ _ => 0) (x,η))) 2
      (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)) := by
  have hid := decoratedWeightedTotal_identDistrib ν step hstep n z hz0 hz1 F hF hI hM x
  have hiz := decoratedWeightedTotal_identDistrib ν step hstep n z hz0 hz1 (fun _ _ => 0)
    (fun _ => measurable_const) (by intro i y; simp only [mul_zero,Real.exp_zero]; exact integrable_const 1)
    (by intro i y; simp) x
  have hld := hid.comp Real.measurable_log
  have hlz := hiz.comp Real.measurable_log
  have hL := cascadeTotal_log_memLp_two n z hz hz0 hz1
  exact (hld.memLp_iff.mpr hL).sub (hlz.memLp_iff.mpr hL)

def fractionalLogMoment {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (b : ℝ) (f : X×S → ℝ) (x : X) : ℝ :=
  Real.log (∫ s, Real.exp (b*f (x,s)) ∂ν)/b

lemma fractionalLogMoment_measurable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (b : ℝ) {f : X×S → ℝ} (hf : Measurable f) :
    Measurable (fractionalLogMoment ν b f) := by
  exact (((hf.const_mul b).exp.stronglyMeasurable.integral_prod_right').measurable.log).div_const b

lemma bounded_fractional_exp_integrable {S : Type} [MeasurableSpace S]
    (ν : ProbabilityMeasure S) {b C : ℝ} (hb : 0 ≤ b) {f : S → ℝ}
    (hf : Measurable f) (hC : ∀ s, |f s| ≤ C) :
    Integrable (fun s => Real.exp (b*f s)) ν := by
  apply (integrable_const (Real.exp (b*C))).mono' ((hf.const_mul b).exp).aestronglyMeasurable
  exact ae_of_all _ fun s => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hC s)) hb)

lemma fractionalLogMoment_abs_le {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) {b C : ℝ} (hb : 0 < b) {f : X×S → ℝ}
    (hf : Measurable f) (hC : ∀ p, |f p| ≤ C) (x : X) :
    |fractionalLogMoment ν b f x| ≤ C := by
  have hI := bounded_fractional_exp_integrable ν hb.le
    (hf.comp (measurable_const.prodMk measurable_id)) (fun s => hC (x,s))
  have hp : 0 < ∫ s, Real.exp (b*f (x,s)) ∂ν := by
    apply integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le) hI |>.mpr
    simp [Function.support,Real.exp_ne_zero]
  have hlo : Real.exp (b*(-C)) ≤ ∫ s, Real.exp (b*f (x,s)) ∂ν := by
    have h := integral_mono (integrable_const (Real.exp (b*(-C)))) hI
      (fun s => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_le.mp (hC (x,s))).1 hb.le))
    simpa using h
  have hup : (∫ s, Real.exp (b*f (x,s)) ∂ν) ≤ Real.exp (b*C) := by
    have h := integral_mono hI (integrable_const (Real.exp (b*C)))
      (fun s => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_le.mp (hC (x,s))).2 hb.le))
    simpa using h
  have hl := Real.log_le_log (Real.exp_pos _) hlo
  have hu := Real.log_le_log hp hup
  rw [Real.log_exp] at hl hu
  apply abs_le.mpr
  change -C ≤ Real.log _/b ∧ Real.log _/b ≤ C
  constructor
  · apply (le_div_iff₀ hb).mpr
    nlinarith
  · apply (div_le_iff₀ hb).mpr
    nlinarith

lemma fractionalLogMoment_centered {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) {b : ℝ} (hb : b ≠ 0) {f : X×S → ℝ} (x : X)
    (hI : Integrable (fun s => Real.exp (b*f (x,s))) ν) :
    Integrable (fun s => Real.exp (b*(f (x,s)-fractionalLogMoment ν b f x))) ν ∧
    (∫ s, Real.exp (b*(f (x,s)-fractionalLogMoment ν b f x)) ∂ν) = 1 := by
  have hp : 0 < ∫ s, Real.exp (b*f (x,s)) ∂ν := by
    apply integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le) hI |>.mpr
    simp [Function.support,Real.exp_ne_zero]
  have hfac (s : S) : Real.exp (b*(f (x,s)-fractionalLogMoment ν b f x)) =
      Real.exp (-(Real.log (∫ t, Real.exp (b*f (x,t)) ∂ν)))*Real.exp (b*f (x,s)) := by
    rw [← Real.exp_add]
    congr 1
    unfold fractionalLogMoment
    field_simp
    ring
  constructor
  · simp_rw [hfac]
    exact hI.const_mul _
  · simp_rw [hfac]
    rw [integral_const_mul,Real.exp_neg,Real.exp_log hp,inv_mul_cancel₀ hp.ne']

def finiteCascadeLogRecursion {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) :
    (n : ℕ) → (Fin n → ℝ) → (X → ℝ) → X → ℝ
  | 0, _, H => H
  | n+1, z, H => fractionalLogMoment ν (z 0)
      (fun p => finiteCascadeLogRecursion ν step n (fun i => z i.succ) H (step p))

lemma finiteCascadeLogRecursion_measurable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) {H : X → ℝ} (hH : Measurable H) :
    Measurable (finiteCascadeLogRecursion ν step n z H) := by
  induction n with
  | zero => exact hH
  | succ n ih => exact fractionalLogMoment_measurable ν (z 0) ((ih (fun i => z i.succ)).comp hs)

lemma finiteCascadeLogRecursion_abs_le {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz : ∀ i, 0 < z i) {H : X → ℝ} (hH : Measurable H)
    {C : ℝ} (hC : ∀ x, |H x| ≤ C) : ∀ x, |finiteCascadeLogRecursion ν step n z H x| ≤ C := by
  induction n with
  | zero => exact hC
  | succ n ih =>
    exact fractionalLogMoment_abs_le ν (hz 0)
      ((finiteCascadeLogRecursion_measurable ν step hs n (fun i => z i.succ) hH).comp hs)
      (fun p => ih (fun i => z i.succ) (fun i => hz i.succ) (step p))

def finiteCascadeShifts {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) :
    (n : ℕ) → (Fin n → ℝ) → (X → ℝ) → Fin n → X×S → ℝ
  | 0, _, _ => Fin.elim0
  | n+1, z, H => Fin.cases
      (fun p => finiteCascadeLogRecursion ν step n (fun i => z i.succ) H (step p) -
        finiteCascadeLogRecursion ν step (n+1) z H p.1)
      (finiteCascadeShifts ν step n (fun i => z i.succ) H)

lemma finiteCascadeShifts_measurable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) {H : X → ℝ} (hH : Measurable H) :
    ∀ i, Measurable (finiteCascadeShifts ν step n z H i) := by
  induction n with
  | zero => intro i; exact i.elim0
  | succ n ih =>
    intro i
    refine Fin.cases ?_ (fun j => ih (fun k => z k.succ) j) i
    exact ((finiteCascadeLogRecursion_measurable ν step hs n (fun j => z j.succ) hH).comp hs).sub
      ((finiteCascadeLogRecursion_measurable ν step hs (n+1) z hH).comp measurable_fst)

lemma finiteCascadeShifts_normalized {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz : ∀ i, 0 < z i) {H : X → ℝ} (hH : Measurable H)
    {C : ℝ} (hC : ∀ x, |H x| ≤ C) : ∀ i x,
    Integrable (fun s => Real.exp (z i*finiteCascadeShifts ν step n z H i (x,s))) ν ∧
    (∫ s, Real.exp (z i*finiteCascadeShifts ν step n z H i (x,s)) ∂ν) = 1 := by
  induction n with
  | zero => intro i; exact i.elim0
  | succ n ih =>
    intro i
    refine Fin.cases ?_ (fun j => ih (fun k => z k.succ) (fun k => hz k.succ) j) i
    intro x
    apply fractionalLogMoment_centered ν (hz 0).ne' (f := fun p => finiteCascadeLogRecursion ν step n (fun j => z j.succ) H (step p)) x
    apply bounded_fractional_exp_integrable ν (hz 0).le
      (((finiteCascadeLogRecursion_measurable ν step hs n (fun j => z j.succ) hH).comp hs).comp
        (measurable_const.prodMk measurable_id))
    exact fun s => finiteCascadeLogRecursion_abs_le ν step hs n (fun j => z j.succ)
      (fun j => hz j.succ) hH hC (step (x,s))

def decoratedTerminalTotalE {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) (H : X → ℝ) : (n : ℕ) → X×DecoratedCascade S n → ℝ≥0∞
  | 0, p => ENNReal.ofReal (Real.exp (H p.1))
  | n+1, p => ∫⁻ q : ℝ×(S×DecoratedCascade S n), ENNReal.ofReal (Real.exp q.1) *
      decoratedTerminalTotalE step H n (step (p.1,q.2.1),q.2.2) ∂markedStableCountKernel p.2

lemma decoratedTerminalTotalE_telescoping {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) (H : X → ℝ)
    (n : ℕ) (z : Fin n → ℝ) (p : X×DecoratedCascade S n) :
    decoratedTerminalTotalE step H n p =
      ENNReal.ofReal (Real.exp (finiteCascadeLogRecursion ν step n z H p.1)) *
        decoratedWeightedTotalE step n (finiteCascadeShifts ν step n z H) p := by
  induction n with
  | zero => simp [decoratedTerminalTotalE,finiteCascadeLogRecursion,decoratedWeightedTotalE]
  | succ n ih =>
    conv_lhs => rw [decoratedTerminalTotalE]
    conv_rhs => arg 2; rw [decoratedWeightedTotalE]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro q
    rw [ih (fun i => z i.succ)]
    simp only [finiteCascadeShifts,Fin.cases_zero,Fin.cases_succ]
    have he : ENNReal.ofReal (Real.exp q.1) *
        ENNReal.ofReal (Real.exp (finiteCascadeLogRecursion ν step n (fun i => z i.succ) H (step (p.1,q.2.1)))) =
        ENNReal.ofReal (Real.exp (finiteCascadeLogRecursion ν step (n+1) z H p.1)) *
        ENNReal.ofReal (Real.exp (q.1 + (finiteCascadeLogRecursion ν step n (fun i => z i.succ) H (step (p.1,q.2.1)) -
          finiteCascadeLogRecursion ν step (n+1) z H p.1))) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_add,← Real.exp_add]
      congr 2
      ring
    rw [← mul_assoc,he,mul_assoc]

lemma decoratedTerminalTotalE_zero {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) (n : ℕ) (p : X×DecoratedCascade S n) :
    decoratedTerminalTotalE step (fun _ => 0) n p = decoratedWeightedTotalE step n (fun _ _ => 0) p := by
  induction n with
  | zero => simp [decoratedTerminalTotalE,decoratedWeightedTotalE]
  | succ n ih =>
    conv_lhs => rw [decoratedTerminalTotalE]
    conv_rhs => rw [decoratedWeightedTotalE]
    apply lintegral_congr
    intro q
    rw [ih]
    simp

def decoratedTerminalTotal {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) (H : X → ℝ) (n : ℕ) (p : X×DecoratedCascade S n) : ℝ :=
  (decoratedTerminalTotalE step H n p).toReal

lemma decoratedTerminalTotal_telescoping {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) (H : X → ℝ)
    (n : ℕ) (z : Fin n → ℝ) (p : X×DecoratedCascade S n) :
    decoratedTerminalTotal step H n p =
      Real.exp (finiteCascadeLogRecursion ν step n z H p.1) *
        decoratedWeightedTotal step n (finiteCascadeShifts ν step n z H) p := by
  exact (congrArg ENNReal.toReal (decoratedTerminalTotalE_telescoping ν step H n z p)).trans
    (by rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_pos _).le]; rfl)

lemma decoratedTerminalTotal_zero {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) (n : ℕ) (p : X×DecoratedCascade S n) :
    decoratedTerminalTotal step (fun _ => 0) n p = decoratedWeightedTotal step n (fun _ _ => 0) p :=
  congrArg ENNReal.toReal (decoratedTerminalTotalE_zero step n p)

theorem finiteCascade_terminal_log_recursion {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    {H : X → ℝ} (hH : Measurable H) {C : ℝ} (hC : ∀ x, |H x| ≤ C) (x : X) :
    (∫ η, Real.log (decoratedTerminalTotal step H n (x,η) /
      decoratedTerminalTotal step (fun _ => 0) n (x,η)) ∂decoratedCascadeLaw ν n z) =
        finiteCascadeLogRecursion ν step n z H x := by
  simp_rw [decoratedTerminalTotal_zero,decoratedTerminalTotal_telescoping ν step H n z]
  exact decoratedCascade_log_identity ν step hs n z hz hz0 hz1 _
    (finiteCascadeShifts_measurable ν step hs n z hH)
    (fun i y => (finiteCascadeShifts_normalized ν step hs n z hz0 hH hC i y).1)
    (fun i y => (finiteCascadeShifts_normalized ν step hs n z hz0 hH hC i y).2) x
    (finiteCascadeLogRecursion ν step n z H x)

def finiteCascadeFractionalIntegrable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) (H : X → ℝ) :
    (n : ℕ) → (Fin n → ℝ) → Prop
  | 0, _ => True
  | n+1, z => (∀ x, Integrable (fun s => Real.exp (z 0*
      finiteCascadeLogRecursion ν step n (fun i => z i.succ) H (step (x,s)))) ν) ∧
        finiteCascadeFractionalIntegrable ν step H n (fun i => z i.succ)

lemma finiteCascadeFractionalIntegrable_of_bounded {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz : ∀ i, 0 < z i) {H : X → ℝ} (hH : Measurable H)
    {C : ℝ} (hC : ∀ x, |H x| ≤ C) : finiteCascadeFractionalIntegrable ν step H n z := by
  induction n with
  | zero => trivial
  | succ n ih =>
    constructor
    · intro x
      apply bounded_fractional_exp_integrable ν (hz 0).le
        (((finiteCascadeLogRecursion_measurable ν step hs n (fun j => z j.succ) hH).comp hs).comp
          (measurable_const.prodMk measurable_id))
      exact fun s => finiteCascadeLogRecursion_abs_le ν step hs n (fun j => z j.succ)
        (fun j => hz j.succ) hH hC (step (x,s))
    · exact ih (fun i => z i.succ) (fun i => hz i.succ)

lemma finiteCascadeShifts_normalized_of_fractional {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X)
    (n : ℕ) (z : Fin n → ℝ) (hz : ∀ i, z i ≠ 0) (H : X → ℝ)
    (hI : finiteCascadeFractionalIntegrable ν step H n z) : ∀ i x,
    Integrable (fun s => Real.exp (z i*finiteCascadeShifts ν step n z H i (x,s))) ν ∧
    (∫ s, Real.exp (z i*finiteCascadeShifts ν step n z H i (x,s)) ∂ν) = 1 := by
  induction n with
  | zero => intro i; exact i.elim0
  | succ n ih =>
    rcases hI with ⟨hroot,htail⟩
    intro i
    refine Fin.cases ?_ (fun j => ih (fun k => z k.succ) (fun k => hz k.succ) htail j) i
    intro x
    exact fractionalLogMoment_centered ν (hz 0)
      (f := fun p => finiteCascadeLogRecursion ν step n (fun j => z j.succ) H (step p)) x (hroot x)

theorem finiteCascade_terminal_log_recursion_of_fractional {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    {H : X → ℝ} (hH : Measurable H) (hI : finiteCascadeFractionalIntegrable ν step H n z) (x : X) :
    (∫ η, Real.log (decoratedTerminalTotal step H n (x,η) /
      decoratedTerminalTotal step (fun _ => 0) n (x,η)) ∂decoratedCascadeLaw ν n z) =
        finiteCascadeLogRecursion ν step n z H x := by
  simp_rw [decoratedTerminalTotal_zero,decoratedTerminalTotal_telescoping ν step H n z]
  exact decoratedCascade_log_identity ν step hs n z hz hz0 hz1 _
    (finiteCascadeShifts_measurable ν step hs n z hH)
    (fun i y => (finiteCascadeShifts_normalized_of_fractional ν step n z (fun j => (hz0 j).ne') H hI i y).1)
    (fun i y => (finiteCascadeShifts_normalized_of_fractional ν step n z (fun j => (hz0 j).ne') H hI i y).2) x
    (finiteCascadeLogRecursion ν step n z H x)

lemma stableIntensity_descendant_transform_marked {S C D : Type*}
    [MeasurableSpace S] [MeasurableSpace C] [MeasurableSpace D]
    (ν : Measure S) (ρ : Measure C) (θ : Measure D)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] [IsProbabilityMeasure θ]
    {b : ℝ} (hb : 0 ≤ b) (T : S×C → D) (hT : Measurable T)
    (hLaw : ∀ s, ρ.map (fun c => T (s,c)) = θ) {F : S → ℝ} (hF : Measurable F) :
    ((stableLogIntensity b).prod (ν.prod ρ)).map
      (fun p : ℝ×(S×C) => (p.1+F p.2.1,(p.2.1,T p.2))) =
      (stableLogIntensity b).prod ((ν.withDensity (fun s => ENNReal.ofReal (Real.exp (b*F s)))).prod θ) := by
  have hmark : MeasurePreserving (fun p : S×C => (p.1,T p)) (ν.prod ρ) (ν.prod θ) :=
    ⟨measurable_fst.prodMk hT,descendant_transform_independent ν ρ θ T hT hLaw⟩
  have hbase := (MeasurePreserving.id (stableLogIntensity b)).prod hmark
  have hshift : MeasurePreserving (logMarkShift (fun p : S×D => F p.1))
      ((stableLogIntensity b).prod (ν.prod θ))
      ((stableLogIntensity b).prod ((ν.withDensity (fun s => ENNReal.ofReal (Real.exp (b*F s)))).prod θ)) := by
    refine ⟨logMarkShift_measurable (hF.comp measurable_fst),?_⟩
    calc
      _ = (stableLogIntensity b).prod ((ν.prod θ).withDensity
          (fun p : S×D => ENNReal.ofReal (Real.exp (b*F p.1)))) := by
        exact stableLogIntensity_mark_shift (ν.prod θ) hb (F := fun p : S×D => F p.1) (by fun_prop)
      _ = _ := by rw [← prod_withDensity_left ((hF.const_mul b).exp.ennreal_ofReal)]
  exact (hshift.comp hbase).map_eq

lemma stablePoisson_descendant_transform_marked {S C D : Type*}
    [MeasurableSpace S] [MeasurableSpace C] [MeasurableSpace D]
    [Nonempty S] [Nonempty C] [Nonempty D]
    (ν : Measure S) (ρ : Measure C) (θ : Measure D)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] [IsProbabilityMeasure θ]
    {b : ℝ} (hb : 0 ≤ b) (T : S×C → D) (hT : Measurable T)
    (hLaw : ∀ s, ρ.map (fun c => T (s,c)) = θ) {F : S → ℝ} (hF : Measurable F) :
    (poissonRandomMeasureLaw ((stableLogIntensity b).prod (ν.prod ρ))).map
      (Measure.map (fun p : ℝ×(S×C) => (p.1+F p.2.1,(p.2.1,T p.2)))) =
      poissonRandomMeasureLaw ((stableLogIntensity b).prod
        ((ν.withDensity (fun s => ENNReal.ofReal (Real.exp (b*F s)))).prod θ)) := by
  rw [poissonRandomMeasureLaw_map _ (by fun_prop)]
  congr 1
  exact stableIntensity_descendant_transform_marked ν ρ θ hb T hT hLaw hF

end SphericalPerceptronFreeEnergy

end

end OAI
