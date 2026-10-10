import Mathlib
import OAI.Probability.Perceptron.Variational.ProductMarkLaw

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

lemma decoratedTerminalTotal_pos_ae {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i)
    (hz1 : ∀ i, z i < 1) {H : X → ℝ} (hH : Measurable H)
    (hI : finiteCascadeFractionalIntegrable ν step H n z) (x : X) :
    ∀ᵐ η ∂(decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)),
      0 < decoratedTerminalTotal step H n (x,η) := by
  have hid := decoratedWeightedTotal_identDistrib ν step hs n z hz0 hz1
    (finiteCascadeShifts ν step n z H)
    (finiteCascadeShifts_measurable ν step hs n z hH)
    (fun i y => (finiteCascadeShifts_normalized_of_fractional ν step n z
      (fun j => (hz0 j).ne') H hI i y).1)
    (fun i y => (finiteCascadeShifts_normalized_of_fractional ν step n z
      (fun j => (hz0 j).ne') H hI i y).2) x
  have hp := hid.symm.ae_snd measurableSet_Ioi (cascadeTotal_regular n z hz hz0 hz1).1
  filter_upwards [hp] with η hη
  rw [decoratedTerminalTotal_telescoping ν step H n z]
  exact mul_pos (Real.exp_pos _) hη

lemma decoratedTerminalLogRatio_integrable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i)
    (hz1 : ∀ i, z i < 1) {H : X → ℝ} (hH : Measurable H)
    (hI : finiteCascadeFractionalIntegrable ν step H n z) (x : X) :
    Integrable (fun η => Real.log (decoratedTerminalTotal step H n (x,η) /
      decoratedTerminalTotal step (fun _ => 0) n (x,η)))
      (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)) := by
  simp_rw [decoratedTerminalTotal_zero,decoratedTerminalTotal_telescoping ν step H n z]
  exact (decoratedCascade_log_second_moment_bound ν step hs n z hz hz0 hz1
    (finiteCascadeShifts ν step n z H)
    (finiteCascadeShifts_measurable ν step hs n z hH)
    (fun i y => (finiteCascadeShifts_normalized_of_fractional ν step n z
      (fun j => (hz0 j).ne') H hI i y).1)
    (fun i y => (finiteCascadeShifts_normalized_of_fractional ν step n z
      (fun j => (hz0 j).ne') H hI i y).2) x
    (finiteCascadeLogRecursion ν step n z H x)).1.integrable (by norm_num)

theorem finiteCascade_terminal_log_ratio {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i)
    (hz1 : ∀ i, z i < 1) {H G : X → ℝ} (hH : Measurable H) (hG : Measurable G)
    (hIH : finiteCascadeFractionalIntegrable ν step H n z)
    (hIG : finiteCascadeFractionalIntegrable ν step G n z) (x : X) :
    (∫ η, Real.log (decoratedTerminalTotal step H n (x,η) /
      decoratedTerminalTotal step G n (x,η)) ∂decoratedCascadeLaw ν n z) =
      finiteCascadeLogRecursion ν step n z H x-finiteCascadeLogRecursion ν step n z G x := by
  have h0 := finiteCascadeFractionalIntegrable_of_bounded ν step hs n z hz0
    (measurable_const : Measurable (fun _ : X => (0:ℝ))) (C := 0) (by simp)
  have he : (fun η => Real.log (decoratedTerminalTotal step H n (x,η) /
      decoratedTerminalTotal step G n (x,η))) =ᵐ[(decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n))]
      (fun η => Real.log (decoratedTerminalTotal step H n (x,η) /
        decoratedTerminalTotal step (fun _ => 0) n (x,η)) -
        Real.log (decoratedTerminalTotal step G n (x,η) /
          decoratedTerminalTotal step (fun _ => 0) n (x,η))) := by
    filter_upwards [decoratedTerminalTotal_pos_ae ν step hs n z hz hz0 hz1 hH hIH x,
      decoratedTerminalTotal_pos_ae ν step hs n z hz hz0 hz1 hG hIG x,
      decoratedTerminalTotal_pos_ae ν step hs n z hz hz0 hz1 measurable_const h0 x]
      with η hηH hηG hη0
    rw [Real.log_div hηH.ne' hηG.ne',Real.log_div hηH.ne' hη0.ne',
      Real.log_div hηG.ne' hη0.ne']
    ring
  rw [integral_congr_ae he,integral_sub
    (decoratedTerminalLogRatio_integrable ν step hs n z hz hz0 hz1 hH hIH x)
    (decoratedTerminalLogRatio_integrable ν step hs n z hz hz0 hz1 hG hIG x),
    finiteCascade_terminal_log_recursion_of_fractional ν step hs n z hz hz0 hz1 hH hIH x,
    finiteCascade_terminal_log_recursion_of_fractional ν step hs n z hz hz0 hz1 hG hIG x]

lemma finiteCascadeFractionalIntegrable_add_product {X Y S T : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace S] [MeasurableSpace T]
    (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S → X) (step₂ : Y×T → Y)
    (n : ℕ) (z : Fin n → ℝ) (hz : ∀ i, 0 < z i) {H : X → ℝ} {G : Y → ℝ}
    (hIH : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hIG : finiteCascadeFractionalIntegrable ρ step₂ G n z) :
    finiteCascadeFractionalIntegrable (productMarkLaw ν ρ)
      (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2)))
      (fun q => H q.1+G q.2) n z := by
  induction n with
  | zero => trivial
  | succ n ih =>
    rcases hIH with ⟨hHroot,hHtail⟩
    rcases hIG with ⟨hGroot,hGtail⟩
    constructor
    · intro x
      simp_rw [finiteCascadeLogRecursion_add_product ν ρ step₁ step₂ n
        (fun i => z i.succ) (fun i => hz i.succ) hHtail hGtail,mul_add,Real.exp_add]
      exact (hHroot x.1).mul_prod (hGroot x.2)
    · exact ih (fun i => z i.succ) (fun i => hz i.succ) hHtail hGtail

theorem finiteCascade_independent_tilt_log {X Y S T : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace S] [MeasurableSpace T]
    [Nonempty S] [Nonempty T]
    (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S → X) (step₂ : Y×T → Y) (hs₁ : Measurable step₁) (hs₂ : Measurable step₂)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i)
    (hz1 : ∀ i, z i < 1) {H : X → ℝ} {G : Y → ℝ} (hH : Measurable H) (hG : Measurable G)
    (hIH : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hIG : finiteCascadeFractionalIntegrable ρ step₂ G n z) (x : X) (y : Y) :
    (∫ η, Real.log (decoratedTerminalTotal
      (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2)))
      (fun q => H q.1+G q.2) n ((x,y),η) /
      decoratedTerminalTotal
      (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2)))
      (fun q => G q.2) n ((x,y),η)) ∂decoratedCascadeLaw (productMarkLaw ν ρ) n z) =
      finiteCascadeLogRecursion ν step₁ n z H x := by
  have h0 := finiteCascadeFractionalIntegrable_of_bounded ν step₁ hs₁ n z hz0
    (measurable_const : Measurable (fun _ : X => (0:ℝ))) (C := 0) (by simp)
  have hprod0 := finiteCascadeFractionalIntegrable_add_product ν ρ step₁ step₂ n z hz0 h0 hIG
  simp only [zero_add] at hprod0
  refine (finiteCascade_terminal_log_ratio (productMarkLaw ν ρ) _ (by fun_prop) n z hz hz0 hz1
    ((hH.comp measurable_fst).add (hG.comp measurable_snd)) (hG.comp measurable_snd)
    (finiteCascadeFractionalIntegrable_add_product ν ρ step₁ step₂ n z hz0 hIH hIG) hprod0 (x,y)).trans ?_
  change finiteCascadeLogRecursion (productMarkLaw ν ρ)
    (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) n z
    (fun q => H q.1+G q.2) (x,y) -
    finiteCascadeLogRecursion (productMarkLaw ν ρ)
    (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) n z
    (fun q => G q.2) (x,y) = _
  rw [finiteCascadeLogRecursion_add_product ν ρ step₁ step₂ n z hz0 hIH hIG]
  have hzero := finiteCascadeLogRecursion_add_product ν ρ step₁ step₂ n z hz0 h0 hIG x y
  simp only [zero_add] at hzero
  rw [hzero]
  have hzrec : finiteCascadeLogRecursion ν step₁ n z (fun _ => 0) x=0 := by
    have hb := finiteCascadeLogRecursion_abs_le ν step₁ hs₁ n z hz0
      (measurable_const : Measurable (fun _ : X => (0:ℝ))) (C := 0) (by simp) x
    exact abs_nonpos_iff.mp hb
  rw [hzrec]
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
