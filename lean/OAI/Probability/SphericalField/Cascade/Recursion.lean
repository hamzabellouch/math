import Mathlib
import OAI.Probability.SphericalField.Cascade.LogFluctuations

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

end SphericalPerceptron
end
end
end

end OAI
