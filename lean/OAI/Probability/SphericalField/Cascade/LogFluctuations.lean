import Mathlib
import OAI.Probability.SphericalField.Cascade.Decorated

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
lemma cascadeTotal_log_memLp_two (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) :
    MemLp (fun η => Real.log (cascadeTotal n η)) 2 (cascadeLaw n z : Measure (StableCascade n)) := by
  cases n with
  | zero => simp [cascadeTotal,cascadeTotalE]
  | succ n =>
    obtain ⟨hp,hI⟩ := cascadeTotal_regular (n+1) z hz hz0 hz1
    let ε : ℝ := z 0/4
    have hε : 0 < ε := div_pos (hz0 0) (by norm_num)
    have hmin : ∀ i, z 0 ≤ z i := fun i => hz.monotone (Fin.zero_le i)
    have hplus : ∀ i, 2*ε < z i := by intro i; dsimp [ε]; linarith [hmin i,hz0 0]
    have hminus : ∀ i, -(2*ε) < z i := by intro i; linarith [hz0 i]
    apply (memLp_two_iff_integrable_sq (cascadeTotal_measurable (n+1)).log.aestronglyMeasurable).mpr
    apply (((hI (2*ε) hplus).add (hI (-(2*ε)) hminus)).div_const (ε^2)).mono'
      ((cascadeTotal_measurable (n+1)).log.pow_const (2:ℕ)).aestronglyMeasurable
    filter_upwards [hp] with η hη
    change |(Real.log (cascadeTotal (n+1) η))^2| ≤ _
    rw [abs_of_nonneg (sq_nonneg _)]
    exact log_sq_le_two_rpow hη hε

def decoratedWeightedTotalE {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) : (n : ℕ) → (Fin n → X×S → ℝ) → X×DecoratedCascade S n → ℝ≥0∞
  | 0, _, _ => 1
  | n+1, F, p => ∫⁻ q : ℝ×(S×DecoratedCascade S n),
      ENNReal.ofReal (Real.exp (q.1+F 0 (p.1,q.2.1))) *
        decoratedWeightedTotalE step n (fun i => F i.succ) (step (p.1,q.2.1),q.2.2)
          ∂markedStableCountKernel p.2

lemma decoratedWeightedTotalE_transform {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) (hstep : Measurable step) (n : ℕ) (F : Fin n → X×S → ℝ)
    (hF : ∀ i, Measurable (F i)) (p : X×DecoratedCascade S n) :
    cascadeTotalE n (decoratedCascadeTransform step n F p) = decoratedWeightedTotalE step n F p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let G : ℝ×(S×DecoratedCascade S n) → ℝ×StableCascade n := fun q =>
      (q.1+F 0 (p.1,q.2.1),decoratedCascadeTransform step n (fun i => F i.succ)
        (step (p.1,q.2.1),q.2.2))
    have hG : Measurable G :=
      (measurable_fst.add ((hF 0).comp (measurable_const.prodMk measurable_snd.fst))).prodMk
        ((decoratedCascadeTransform_measurable step hstep n _ (fun i => hF i.succ)).comp
          ((hstep.comp (measurable_const.prodMk measurable_snd.fst)).prodMk measurable_snd.snd))
    change (∫⁻ q : ℝ×StableCascade n, ENNReal.ofReal (Real.exp q.1)*cascadeTotalE n q.2
      ∂(markedStableCountKernel p.2).map G) = _
    have hw : Measurable (fun q : ℝ×StableCascade n => ENNReal.ofReal (Real.exp q.1)*cascadeTotalE n q.2) :=
      ((Real.measurable_exp.comp measurable_fst).ennreal_ofReal.mul ((cascadeTotalE_measurable n).comp measurable_snd))
    calc
      _ = ∫⁻ q, ENNReal.ofReal (Real.exp (G q).1)*cascadeTotalE n (G q).2 ∂markedStableCountKernel p.2 :=
        lintegral_map hw hG
      _ = _ := by
        apply lintegral_congr
        intro q
        dsimp only [G]
        rw [ih (fun i => F i.succ) (fun i => hF i.succ)]

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

end SphericalPerceptron
end
end
end

end OAI
