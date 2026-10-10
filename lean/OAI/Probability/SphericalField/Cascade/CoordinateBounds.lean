import Mathlib
import OAI.Probability.SphericalField.Gaussian.Fractional

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
def cascadeLogFluctuationConstant (n : ℕ) (z : Fin n → ℝ) : ℝ :=
  4*∫ η, (Real.log (cascadeTotal n η))^2 ∂cascadeLaw n z

lemma cascadeLogFluctuationConstant_nonneg (n : ℕ) (z : Fin n → ℝ) :
    0 ≤ cascadeLogFluctuationConstant n z :=
  mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _)

lemma decoratedCascade_log_second_moment_bound {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S → X) (hstep : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) (c : ℝ) :
    MemLp (fun η => Real.log (Real.exp c*decoratedWeightedTotal step n F (x,η) /
      decoratedWeightedTotal step n (fun _ _ => 0) (x,η))) 2
        (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)) ∧
    (∫ η, (Real.log (Real.exp c*decoratedWeightedTotal step n F (x,η) /
      decoratedWeightedTotal step n (fun _ _ => 0) (x,η))-c)^2 ∂decoratedCascadeLaw ν n z) ≤
        cascadeLogFluctuationConstant n z := by
  have hid := decoratedWeightedTotal_identDistrib ν step hstep n z hz0 hz1 F hF hI hM x
  have hiz := decoratedWeightedTotal_identDistrib ν step hstep n z hz0 hz1 (fun _ _ => 0)
    (fun _ => measurable_const) (by intro i y; simp only [mul_zero,Real.exp_zero]; exact integrable_const 1)
    (by intro i y; simp) x
  have hld := hid.comp Real.measurable_log
  have hlz := hiz.comp Real.measurable_log
  have hL := cascadeTotal_log_memLp_two n z hz hz0 hz1
  have hmD := hld.memLp_iff.mpr hL
  have hmZ := hlz.memLp_iff.mpr hL
  have hp := (cascadeTotal_regular n z hz hz0 hz1).1
  have hdpos := hid.symm.ae_mem_snd measurableSet_Ioi hp
  have hzpos := hiz.symm.ae_mem_snd measurableSet_Ioi hp
  have he : (fun η => Real.log (Real.exp c*decoratedWeightedTotal step n F (x,η) /
      decoratedWeightedTotal step n (fun _ _ => 0) (x,η))) =ᵐ[(decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n))]
      (fun η => c+Real.log (decoratedWeightedTotal step n F (x,η))-
        Real.log (decoratedWeightedTotal step n (fun _ _ => 0) (x,η))) := by
    filter_upwards [hdpos,hzpos] with η hη hg
    rw [Real.log_div (mul_ne_zero (Real.exp_ne_zero _) hη.ne') hg.ne',
      Real.log_mul (Real.exp_ne_zero _) hη.ne',Real.log_exp]
  refine ⟨(memLp_congr_ae he).mpr (((memLp_const c).add hmD).sub hmZ),?_⟩
  have heD := (hld.comp (by fun_prop : Measurable (fun t : ℝ => t^2))).integral_eq
  have heZ := (hlz.comp (by fun_prop : Measurable (fun t : ℝ => t^2))).integral_eq
  simp only [Function.comp_apply] at heD heZ
  calc
    _ = ∫ η, (Real.log (decoratedWeightedTotal step n F (x,η))-
        Real.log (decoratedWeightedTotal step n (fun _ _ => 0) (x,η)))^2 ∂decoratedCascadeLaw ν n z := by
      apply integral_congr_ae
      filter_upwards [he] with η hη
      rw [hη]
      ring
    _ ≤ ∫ η, (2*(Real.log (decoratedWeightedTotal step n F (x,η)))^2+
        2*(Real.log (decoratedWeightedTotal step n (fun _ _ => 0) (x,η)))^2) ∂decoratedCascadeLaw ν n z := by
      apply integral_mono (hmD.sub hmZ).integrable_sq
        ((hmD.integrable_sq.const_mul 2).add (hmZ.integrable_sq.const_mul 2))
      intro η
      dsimp only [Function.comp_apply,Pi.sub_apply,Pi.add_apply]
      nlinarith [sq_nonneg (Real.log (decoratedWeightedTotal step n F (x,η))+
        Real.log (decoratedWeightedTotal step n (fun _ _ => 0) (x,η)))]
    _ = _ := by
      have hsplit := integral_add (hmD.integrable_sq.const_mul 2) (hmZ.integrable_sq.const_mul 2)
      simp only [Function.comp_apply] at hsplit
      rw [hsplit,integral_const_mul,integral_const_mul,heD,heZ]
      unfold cascadeLogFluctuationConstant
      ring

lemma decoratedCascade_log_deviation_le {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S → X) (hstep : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) (c : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n))
      {η | ε ≤ |Real.log (Real.exp c*decoratedWeightedTotal step n F (x,η) /
        decoratedWeightedTotal step n (fun _ _ => 0) (x,η))-c|} ≤
      ENNReal.ofReal (cascadeLogFluctuationConstant n z/ε^2) := by
  obtain ⟨hm,hbound⟩ := decoratedCascade_log_second_moment_bound ν step hstep n z hz hz0 hz1 F hF hI hM x c
  have he := decoratedCascade_log_identity ν step hstep n z hz hz0 hz1 F hF hI hM x c
  have hvar : variance (fun η => Real.log (Real.exp c*decoratedWeightedTotal step n F (x,η) /
      decoratedWeightedTotal step n (fun _ _ => 0) (x,η)))
        (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)) ≤ cascadeLogFluctuationConstant n z := by
    rw [variance_eq_integral hm.aemeasurable,he]
    exact hbound
  have hc := meas_ge_le_variance_div_sq hm hε
  rw [he] at hc
  exact hc.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hvar (sq_nonneg ε)))

lemma finiteCascade_terminal_log_deviation_le {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    {H : X → ℝ} (hH : Measurable H) (hI : finiteCascadeFractionalIntegrable ν step H n z) (x : X)
    {ε : ℝ} (hε : 0 < ε) :
    (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n))
      {η | ε ≤ |Real.log (decoratedTerminalTotal step H n (x,η) /
        decoratedTerminalTotal step (fun _ => 0) n (x,η))-finiteCascadeLogRecursion ν step n z H x|} ≤
      ENNReal.ofReal (cascadeLogFluctuationConstant n z/ε^2) := by
  simp_rw [decoratedTerminalTotal_zero,decoratedTerminalTotal_telescoping ν step H n z]
  exact decoratedCascade_log_deviation_le ν step hs n z hz hz0 hz1 _
    (finiteCascadeShifts_measurable ν step hs n z hH)
    (fun i y => (finiteCascadeShifts_normalized_of_fractional ν step n z (fun j => (hz0 j).ne') H hI i y).1)
    (fun i y => (finiteCascadeShifts_normalized_of_fractional ν step n z (fun j => (hz0 j).ne') H hI i y).2) x
    (finiteCascadeLogRecursion ν step n z H x) hε

lemma fractional_log_moment_sum_pi {ι S : Type} [Fintype ι] [MeasurableSpace S]
    (ν : ι → ProbabilityMeasure S) (b : ℝ) (f : ι → S → ℝ)
    (hI : ∀ i, Integrable (fun s => Real.exp (b*f i s)) (ν i)) :
    (Integrable (fun s : ι → S => Real.exp (b*∑ i, f i (s i))) (piMarkLaw ν)) ∧
    Real.log (∫ s, Real.exp (b*∑ i, f i (s i)) ∂(piMarkLaw ν : Measure (ι → S)))/b =
      ∑ i, Real.log (∫ s, Real.exp (b*f i s) ∂(ν i : Measure S))/b := by
  simp_rw [Finset.mul_sum,Real.exp_sum]
  constructor
  · exact Integrable.fintype_prod hI
  · change Real.log (∫ s, ∏ i, Real.exp (b*f i (s i)) ∂Measure.pi (fun i => (ν i : Measure S)))/b = _
    rw [integral_fintype_prod_eq_prod (fun i s => Real.exp (b*f i s)),Real.log_prod (fun i _ => (integral_exp_pos (hI i)).ne'),Finset.sum_div]

theorem finiteCascade_sum_pi {ι X S : Type} [Fintype ι]
    [MeasurableSpace X] [MeasurableSpace S]
    (ν : ι → ProbabilityMeasure S) (step : ι → X×S → X)
    (n : ℕ) (z : Fin n → ℝ) (H : ι → X → ℝ)
    (hI : ∀ i, finiteCascadeFractionalIntegrable (ν i) (step i) (H i) n z) :
    (∀ x, finiteCascadeLogRecursion (piMarkLaw ν)
      (fun p : (ι → X)×(ι → S) => fun i => step i (p.1 i,p.2 i)) n z
        (fun x => ∑ i, H i (x i)) x =
      ∑ i, finiteCascadeLogRecursion (ν i) (step i) n z (H i) (x i)) ∧
    finiteCascadeFractionalIntegrable (piMarkLaw ν)
      (fun p : (ι → X)×(ι → S) => fun i => step i (p.1 i,p.2 i))
        (fun x => ∑ i, H i (x i)) n z := by
  induction n with
  | zero => exact ⟨fun _ => rfl,trivial⟩
  | succ n ih =>
    obtain ⟨heq,htail⟩ := ih (fun j => z j.succ) (fun i => (hI i).2)
    constructor
    · intro x
      conv_lhs => rw [finiteCascadeLogRecursion]
      unfold fractionalLogMoment
      simp_rw [heq]
      exact (fractional_log_moment_sum_pi ν (z 0)
        (fun i s => finiteCascadeLogRecursion (ν i) (step i) n (fun j => z j.succ) (H i) (step i (x i,s)))
        (fun i => (hI i).1 (x i))).2
    · refine ⟨?_,htail⟩
      intro x
      simp_rw [heq]
      exact (fractional_log_moment_sum_pi ν (z 0)
        (fun i s => finiteCascadeLogRecursion (ν i) (step i) n (fun j => z j.succ) (H i) (step i (x i,s)))
        (fun i => (hI i).1 (x i))).1

theorem finiteCascade_quadratic_coordinates (d : ℕ) (σ : ℕ → ℝ) (b : ℝ) (c : Fin d → ℝ)
    (n : ℕ) (z : Fin n → ℝ) (hz : ∀ i, 0 < z i)
    (hp : 0 < quadraticCascadePrecision σ b n z) :
    (∀ x, finiteCascadeLogRecursion (piMarkLaw (fun _ : Fin d => standardGaussianMark))
      (fun p : (Fin d → ℕ → ℝ)×(Fin d → ℝ) => fun i => gaussianShiftStep σ (p.1 i,p.2 i)) n z
        (fun x => ∑ i, (c i+(x i 0)^2/(2*b))) x =
      (∑ i, c i) + d*quadraticCascadeOffset σ b n z+
        (∑ i, (x i n)^2)/(2*quadraticCascadePrecision σ b n z)) ∧
    finiteCascadeFractionalIntegrable (piMarkLaw (fun _ : Fin d => standardGaussianMark))
      (fun p : (Fin d → ℕ → ℝ)×(Fin d → ℝ) => fun i => gaussianShiftStep σ (p.1 i,p.2 i))
        (fun x => ∑ i, (c i+(x i 0)^2/(2*b))) n z := by
  have hq := finiteCascade_sum_pi (fun _ : Fin d => standardGaussianMark)
    (fun _ => gaussianShiftStep σ) n z (fun i x => c i+(x 0)^2/(2*b))
    (fun i => (finiteCascade_quadratic_recursion σ b (c i) n z hz hp).2)
  refine ⟨?_,hq.2⟩
  intro x
  rw [hq.1]
  simp_rw [(finiteCascade_quadratic_recursion σ b _ n z hz hp).1]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Finset.sum_div]

end SphericalPerceptron
end
end
end

end OAI
