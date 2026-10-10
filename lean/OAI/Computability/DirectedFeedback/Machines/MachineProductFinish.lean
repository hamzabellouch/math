import Mathlib
import OAI.Computability.DirectedFeedback.Machines.MachineProductProgram

namespace OAI


namespace DFVSGames.Explicit.MachineProductFinish

open Turing
open DFVSGames.Foundations
open Complexity Hastad
open MachineComposition
open MachineProductProgram

variable {q t : Nat}

noncomputable section

theorem base_ready (H : Target.Instance q) (t : Nat) :
    MachineProductLoop.BaseReady H (MachineProductHeaders.baseTapes H t) := by
  constructor
  · intro bit
    exact ⟨rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rfl
  · simp [MachineProductHeaders.baseTapes, MachineProductHeaders.frame, auxiliary]
  · simp [MachineProductHeaders.baseTapes, MachineProductHeaders.frame, auxiliary]

def afterRows (H : Target.Instance q) (t : Nat) :
    TM2.Cfg (fun _ : Tape t => Bool) (Label q t) State :=
  SourceOdometerSchedule.finalConfiguration (nextCheck q t t) ((), ())
    (Sum.inl (6 : Fin 10)) (MachineProductHeaders.baseTapes H t) (MachineProductLoop.rowBits (t := t) H)

theorem afterRows_output (H : Target.Instance q) (t : Nat) :
    (afterRows H t).stk (output t) = [] := by
  simp [afterRows, SourceOdometerSchedule.finalConfiguration, SourceOdometerSchedule.configuration,
    SourceOdometerSchedule.setDigits, SourceOdometerSchedule.setAcc, output, auxiliary,
    MachineProductHeaders.baseTapes, MachineProductHeaders.frame]

theorem allRows_eq (H : Target.Instance q) (t : Nat) :
    (MachineTupleOdometer.tupleOrder H.constraints.length t).flatMap (MachineProductLoop.rowBits (t := t) H) =
      ProductMachineSemantics.allRowsBits H t := by
  simp only [MachineTupleOdometer.tupleOrder, ProductMachineSemantics.allRowsBits,
    List.ofFn_eq_map, List.flatMap_map, MachineProductLoop.rowBits]

theorem afterRows_accumulator (H : Target.Instance q)
    (presentation : MachineOutputContract.SimpleBipartite H) (t : Nat) (ht : 0 < t) :
    ((afterRows H t).stk (accumulator t)).reverse =
      gameBits (ProductPaddedOutput.output H presentation t ht) := by
  change ((SourceOdometerSchedule.allBits (MachineProductLoop.rowBits (t := t) H)).reverse ++
    MachineProductHeaders.baseTapes H t (accumulator t)).reverse = _
  rw [MachineProductHeaders.baseTapes, MachineProductHeaders.frame_accumulator,
    List.reverse_append, List.reverse_reverse, List.reverse_reverse]
  rw [SourceOdometerSchedule.allBits, allRows_eq]
  exact ProductMachineSemantics.gameBits_eq H presentation t ht

def finishInTime (base : Tape t → List Bool) (emptyOutput : base (output t) = []) :
    StateTransition.EvalsToInTime (TM2.step (program q t))
      ⟨some .finishStart, (((), ()), none), base⟩
      (some ⟨none, (((), ()), none),
        SourceRuntimeFinish.canonicalTapes (output t) (base (accumulator t)).reverse⟩)
      (1 + SourceRuntimeFinish.finishCost (clearKeys t) (accumulator t) base) := by
  have enter : StateTransition.EvalsToInTime (TM2.step (program q t))
      ⟨some .finishStart, (((), ()), none), base⟩
      (some ⟨SourceRuntimeFinish.entry (clearKeys t) Label.finish, (((), ()), none), base⟩) 1 := by
    refine ⟨⟨1, ?_⟩, Nat.le_refl _⟩
    change some (TM2.stepAux (program q t .finishStart) _ _) = _
    simp only [program, DFVSGames.Reduction.MachineTransfer.exitAt]
    split <;> simp_all [TM2.stepAux]
  have finish := SourceRuntimeFinish.finishInTime (clearKeys t) (accumulator t) (output t)
    (by simp [accumulator, output, auxiliary])
    (by simp) (by simp) (by intro k h1 h2; simp [h1, h2])
    ((), ()) Label.finish none (program q t) (fun _ => rfl) base emptyOutput ((), ()) none
  have joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ enter finish
  exact { toEvalsTo := joined.toEvalsTo
          steps_le_m := by simpa only [Nat.add_comm] using joined.steps_le_m }

theorem finishCost_le_uniform (base : Tape t → List Bool) (bound : Nat)
    (bounded : ∀ k, (base k).length ≤ bound) :
    SourceRuntimeFinish.finishCost (clearKeys t) (accumulator t) base ≤
      ((clearKeys t).length + 1) * bound + (clearKeys t).length + 2 := by
  have clear := MachineDrainMany.steps_le_uniform (clearKeys t) base bound bounded
  have acc := bounded (accumulator t)
  unfold SourceRuntimeFinish.finishCost
  rw [Nat.add_mul, Nat.one_mul]
  rw [Nat.mul_add, Nat.mul_one] at clear
  omega

theorem finish_afterRows (H : Target.Instance q)
    (presentation : MachineOutputContract.SimpleBipartite H) (t : Nat) (ht : 0 < t) :
    Nonempty (StateTransition.EvalsToInTime (machine q t).step (afterRows H t)
      (some (haltList (machine q t) (gameBits (ProductPaddedOutput.output H presentation t ht))))
      (1 + SourceRuntimeFinish.finishCost (clearKeys t) (accumulator t) (afterRows H t).stk)) := by
  have run := finishInTime (q := q) (afterRows H t).stk (afterRows_output H t)
  rw [afterRows_accumulator H presentation t ht] at run
  have hstart : (afterRows H t).l = some .finishStart := by simp [afterRows,
    SourceOdometerSchedule.finalConfiguration, SourceOdometerSchedule.configuration, nextCheck]
  have hstate : (afterRows H t).var = (((), ()), none) := rfl
  have halt : (⟨none, (((), ()), none), SourceRuntimeFinish.canonicalTapes (output t)
      (gameBits (ProductPaddedOutput.output H presentation t ht))⟩ :
      TM2.Cfg (fun _ : Tape t => Bool) (Label q t) State) =
      haltList (machine q t) (gameBits (ProductPaddedOutput.output H presentation t ht)) := by
    unfold haltList SourceRuntimeFinish.canonicalTapes
    congr 1
    funext k
    by_cases hk : k = output t <;> simp [machine, hk]
    rfl
  rw [halt] at run
  have hcfg : (⟨some .finishStart, (((), ()), none), (afterRows H t).stk⟩ :
      TM2.Cfg (fun _ : Tape t => Bool) (Label q t) State) =
      afterRows H t := by cases h : afterRows H t; simp_all
  rw [hcfg] at run
  exact ⟨run⟩

end

end DFVSGames.Explicit.MachineProductFinish


namespace DFVSGames.Explicit.MachineProductRuntime

open Turing
open DFVSGames.Foundations Target Complexity Hastad
open MachineProductProgram

noncomputable section

def loopPolynomial (q t : Nat) : Polynomial Nat :=
  (Polynomial.C (q ^ t + 2) * MachineProductBounds.fieldPolynomial t +
    Polynomial.C (2 * t)) * Polynomial.X ^ t

theorem loop_budget {q : Nat} (H : Instance q) (t : Nat) :
    (MachineProductLoop.bodyBound H t + 2 * t) * H.constraints.length ^ t ≤
      (loopPolynomial q t).eval (gameBits H).length := by
  have hlen := MachineProductLoop.input_length H
  have hm : H.constraints.length ≤ (gameBits H).length := by omega
  simp only [loopPolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm t)

def prefixPolynomial (q t : Nat) : Polynomial Nat :=
  MachineProductHeaders.timePolynomial t + loopPolynomial q t

def prefixInTime {q : Nat} (H : Instance q) (t : Nat) :
    StateTransition.EvalsToInTime (machine q t).step
      (initList (machine q t) (gameBits H))
      (some (MachineProductFinish.afterRows H t))
      ((prefixPolynomial q t).eval (gameBits H).length) := by
  let first := MachineProductHeaders.inPolynomialTime H t
  let loop := Classical.choice (MachineProductLoop.traversalInTime H
    (MachineProductHeaders.baseTapes H t) (MachineProductFinish.base_ready H t))
  let second : StateTransition.EvalsToInTime (machine q t).step
      (SourceOdometerSchedule.initialConfiguration (m := H.constraints.length)
        t (rowMain q t) ((), ()) (MachineProductHeaders.baseTapes H t))
      (some (MachineProductFinish.afterRows H t))
      ((loopPolynomial q t).eval (gameBits H).length) := {
    toEvalsTo := loop.toEvalsTo
    steps_le_m := loop.steps_le_m.trans (loop_budget H t) }
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  exact {
    toEvalsTo := joined.toEvalsTo
    steps_le_m := by
      simpa only [prefixPolynomial, Polynomial.eval_add, Nat.add_comm]
        using joined.steps_le_m }

def timePolynomial (q t : Nat) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (machine q t) (clearKeys t).length
    (prefixPolynomial q t) + 1

def outputInTime {q : Nat} (H : Instance q)
    (presentation : MachineOutputContract.SimpleBipartite H) (t : Nat) (ht : 0 < t) :
    TM2OutputsInTime (machine q t) (gameBits H)
      (some (gameBits (ProductPaddedOutput.output H presentation t ht)))
      ((timePolynomial q t).eval (gameBits H).length) := by
  let initialRun := prefixInTime H t
  let finish := Classical.choice (MachineProductFinish.finish_afterRows H presentation t ht)
  let whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ initialRun finish
  have keepAccumulator : accumulator t ∉ clearKeys t := by simp
  have keepOutput : output t ∉ clearKeys t := by simp
  have covers (k : Tape t) (ha : k ≠ accumulator t) (ho : k ≠ output t) :
      k ∈ clearKeys t := (mem_clearKeys t k).mpr ⟨ha, ho⟩
  have bound := SourceRuntimeSpace.finishCost_le_of_prefix (machine q t) (gameBits H)
    initialRun (clearKeys t) (accumulator t) (output t)
    keepAccumulator keepOutput covers
    (MachineProductFinish.afterRows H t).stk (MachineProductFinish.afterRows_output H t)
    (fun _ => rfl)
  change StateTransition.EvalsToInTime (machine q t).step _
    (some (haltList (machine q t) _)) _
  refine { toEvalsTo := whole.toEvalsTo, steps_le_m := whole.steps_le_m.trans ?_ }
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_one,
    SourceRuntimeSpace.completedTime_eval]
  simp only [machine] at bound ⊢
  change SourceRuntimeFinish.finishCost (clearKeys t) (accumulator t)
    (MachineProductFinish.afterRows H t).stk ≤ _ at bound
  omega

abbrev Input (q : Nat) := Σ H : Instance q, MachineOutputContract.SimpleBipartite H

def construct {q : Nat} (t : Nat) (ht : 0 < t) (H : Input q) : Instance (q ^ t) :=
  ProductPaddedOutput.output H.1 H.2 t ht

def computation (q t : Nat) (ht : 0 < t) :
    TM2ComputableInPolyTime (fun H : Input q => gameBits H.1) gameBits
      (construct t ht) where
  tm := machine q t
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial q t
  outputsFun H := by
    change TM2OutputsInTime (machine q t) ((gameBits H.1).map id)
      (some ((gameBits (construct t ht H)).map id)) _
    convert outputInTime H.1 H.2 t ht using 1
    simp only [machine, List.map_id, construct]

theorem finiteAlphabet (q t : Nat) (ht : 0 < t) :
    MachineFiniteAlphabet.FiniteAlphabet (computation q t ht).tm :=
  MachineFiniteAlphabet.of_bool _ (fun _ => rfl)

variable {A : Type} {q : Nat} {encode : A → List Bool} {f : A → Instance q}

def certify (upstream : TM2ComputableInPolyTime encode gameBits f)
    (presentation : ∀ a, MachineOutputContract.SimpleBipartite (f a)) :
    TM2ComputableInPolyTime encode (fun H : Input q => gameBits H.1)
      (fun a => ⟨f a, presentation a⟩) where
  tm := upstream.tm
  inputAlphabet := upstream.inputAlphabet
  outputAlphabet := upstream.outputAlphabet
  time := upstream.time
  outputsFun := upstream.outputsFun

def compose (upstream : TM2ComputableInPolyTime encode gameBits f)
    (presentation : ∀ a, MachineOutputContract.SimpleBipartite (f a))
    (t : Nat) (ht : 0 < t) :
    TM2ComputableInPolyTime encode gameBits
      (fun a => ProductPaddedOutput.output (f a) (presentation a) t ht) :=
  MachineSequential.composeBits (certify upstream presentation) (computation q t ht)

theorem compose_finiteAlphabet (upstream : TM2ComputableInPolyTime encode gameBits f)
    (presentation : ∀ a, MachineOutputContract.SimpleBipartite (f a))
    (t : Nat) (ht : 0 < t) (finite : MachineFiniteAlphabet.FiniteAlphabet upstream.tm) :
    MachineFiniteAlphabet.FiniteAlphabet (compose upstream presentation t ht).tm :=
  MachineFiniteAlphabet.composeBits (certify upstream presentation) (computation q t ht)
    finite (finiteAlphabet q t ht)

end

end DFVSGames.Explicit.MachineProductRuntime


namespace DFVSGames.Repetition.Analytic

open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι]

def quadraticMass (w f g : ι → ℝ) : ℝ :=
  ∑ i, w i * ((f i) ^ 2 + (g i) ^ 2) / 2

def gatedCorrelation (w f g : ι → ℝ) (gate : ι → Bool) : ℝ :=
  ∑ i, if gate i then w i * f i * g i else 0

def gatedMinimum (w f g : ι → ℝ) (gate : ι → Bool) : ℝ :=
  ∑ i, if gate i then w i * min ((f i) ^ 2) ((g i) ^ 2) else 0

def gatedMaximum (w f g : ι → ℝ) (gate : ι → Bool) : ℝ :=
  ∑ i, if gate i then w i * max ((f i) ^ 2) ((g i) ^ 2) else 0

theorem quadraticMass_nonnegative (w f g : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    0 ≤ quadraticMass w f g := by
  apply Finset.sum_nonneg
  intro i _
  exact div_nonneg (mul_nonneg (hw i) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
    (by norm_num)

theorem gatedCorrelation_nonnegative (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    0 ≤ gatedCorrelation w f g gate := by
  apply Finset.sum_nonneg
  intro i _
  split
  · exact mul_nonneg (mul_nonneg (hw i) (hf i)) (hg i)
  · exact le_rfl

theorem gatedCorrelation_le_mass (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) : gatedCorrelation w f g gate ≤ quadraticMass w f g := by
  apply Finset.sum_le_sum
  intro i _
  split
  · have hfg : f i * g i ≤ ((f i) ^ 2 + (g i) ^ 2) / 2 := by
      nlinarith [sq_nonneg (f i - g i)]
    simpa only [← mul_assoc, mul_div_assoc] using mul_le_mul_of_nonneg_left hfg (hw i)
  · exact div_nonneg (mul_nonneg (hw i) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
      (by norm_num)

theorem gatedMinimum_nonnegative (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) : 0 ≤ gatedMinimum w f g gate := by
  apply Finset.sum_nonneg
  intro i _
  split
  · exact mul_nonneg (hw i) (le_min (sq_nonneg _) (sq_nonneg _))
  · exact le_rfl

theorem gatedMinimum_le_mass (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) : gatedMinimum w f g gate ≤ quadraticMass w f g := by
  apply Finset.sum_le_sum
  intro i _
  split
  · have hmin : min ((f i) ^ 2) ((g i) ^ 2) ≤ ((f i) ^ 2 + (g i) ^ 2) / 2 := by
      have h₁ := min_le_left ((f i) ^ 2) ((g i) ^ 2)
      have h₂ := min_le_right ((f i) ^ 2) ((g i) ^ 2)
      linarith
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hmin (hw i)
  · exact div_nonneg (mul_nonneg (hw i) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
      (by norm_num)

theorem gatedMinimum_add_maximum_le (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) :
    gatedMinimum w f g gate + gatedMaximum w f g gate ≤ 2 * quadraticMass w f g := by
  unfold gatedMinimum gatedMaximum quadraticMass
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : gate i = true
  · simp only [hi, ↓reduceIte]
    have h := min_add_max ((f i) ^ 2) ((g i) ^ 2)
    rw [← mul_add, h]
    ring_nf ; exact le_rfl
  · simp only [hi, Bool.false_eq_true, ↓reduceIte, zero_add]
    have := hw i
    positivity

theorem gatedCorrelation_sq_le_min_mul_max (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) :
    gatedCorrelation w f g gate ^ 2 ≤
      gatedMinimum w f g gate * gatedMaximum w f g gate := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i _
    split
    · exact mul_nonneg (hw i) (le_min (sq_nonneg _) (sq_nonneg _))
    · exact le_rfl
  · intro i _
    split
    · exact mul_nonneg (hw i) ((sq_nonneg (f i)).trans (le_max_left _ _))
    · exact le_rfl
  · intro i _
    by_cases hi : gate i = true
    · simp only [hi, ↓reduceIte]
      rcases le_total ((f i) ^ 2) ((g i) ^ 2) with h | h
      · rw [min_eq_left h, max_eq_right h]
        ring_nf ; exact le_rfl
      · rw [min_eq_right h, max_eq_left h]
        ring_nf ; exact le_rfl
    · simp [hi]

theorem gatedCorrelation_sq_le_min_quadratic (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) :
    gatedCorrelation w f g gate ^ 2 ≤
      gatedMinimum w f g gate *
        (2 * quadraticMass w f g - gatedMinimum w f g gate) := by
  have hmax := gatedMinimum_add_maximum_le w f g gate hw
  have hmin := gatedMinimum_nonnegative w f g gate hw
  exact (gatedCorrelation_sq_le_min_mul_max w f g gate hw).trans
    (mul_le_mul_of_nonneg_left (by linarith) hmin)

theorem gatedMinimum_cheeger (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) :
    quadraticMass w f g -
        Real.sqrt (quadraticMass w f g ^ 2 - gatedCorrelation w f g gate ^ 2) ≤
      gatedMinimum w f g gate := by
  have h := gatedCorrelation_sq_le_min_quadratic w f g gate hw
  have hsq : (quadraticMass w f g - gatedMinimum w f g gate) ^ 2 ≤
      quadraticMass w f g ^ 2 - gatedCorrelation w f g gate ^ 2 := by
    nlinarith
  have hsqrt := Real.le_sqrt_of_sq_le hsq
  linarith

theorem gatedMinimum_near_one (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) {η : ℝ} (_hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (hmass : quadraticMass w f g ≤ 1)
    (hcorrelation : 1 - η ≤ gatedCorrelation w f g gate) :
    1 - Real.sqrt (2 * η) ≤ gatedMinimum w f g gate := by
  have hmin := gatedMinimum_nonnegative w f g gate hw
  have h := gatedCorrelation_sq_le_min_quadratic w f g gate hw
  have hcorr : 0 ≤ gatedCorrelation w f g gate := by linarith
  have hsqcorr : (1 - η) ^ 2 ≤ gatedCorrelation w f g gate ^ 2 := by
    nlinarith
  have hupper : gatedMinimum w f g gate *
      (2 * quadraticMass w f g - gatedMinimum w f g gate) ≤
      gatedMinimum w f g gate * (2 - gatedMinimum w f g gate) := by
    apply mul_le_mul_of_nonneg_left _ hmin
    linarith
  have hsq : (1 - gatedMinimum w f g gate) ^ 2 ≤ 2 * η := by
    nlinarith [sq_nonneg η]
  have hsqrt := Real.le_sqrt_of_sq_le hsq
  linarith

theorem gatedMinimum_unit_mass (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hmass : quadraticMass w f g = 1) :
    1 - Real.sqrt (2 * (1 - gatedCorrelation w f g gate)) ≤
      gatedMinimum w f g gate := by
  have hc₀ := gatedCorrelation_nonnegative w f g gate hw hf hg
  have hc₁ := gatedCorrelation_le_mass w f g gate hw
  rw [hmass] at hc₁
  apply gatedMinimum_near_one w f g gate hw
  · linarith
  · linarith
  · exact hmass.le
  · linarith

end
end DFVSGames.Repetition.Analytic


namespace DFVSGames.Repetition

open scoped BigOperators
open Foundations.Games

noncomputable section

variable {V A Ω E : Type*} [Fintype V] [Fintype Ω] [Fintype E]

def rowSquareMass (f : V → Ω → ℝ) (v : V) : ℝ := ∑ ω, (f v ω) ^ 2

def paddedAmplitude [DecidableEq V] (f : V → Ω → ℝ) (v : V) : Ω ⊕ V → ℝ
  | Sum.inl ω => f v ω
  | Sum.inr w => if v = w then Real.sqrt (1 - rowSquareMass f v) else 0

def paddedLabel (a : V → Ω → A) (fallback : A) (v : V) : Ω ⊕ V → A
  | Sum.inl ω => a v ω
  | Sum.inr _ => fallback

omit [Fintype V] in
theorem paddedAmplitude_nonnegative [DecidableEq V] (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) (v : V) (ω : Ω ⊕ V) :
    0 ≤ paddedAmplitude f v ω := by
  cases ω with
  | inl ω => exact hf v ω
  | inr w =>
      simp only [paddedAmplitude]
      split
      · exact Real.sqrt_nonneg _
      · exact le_rfl

theorem paddedAmplitude_row [DecidableEq V] (f : V → Ω → ℝ)
    (hrow : ∀ v, rowSquareMass f v ≤ 1) (v : V) :
    rowSquareMass (paddedAmplitude f) v = 1 := by
  have hs : Real.sqrt (1 - rowSquareMass f v) ^ 2 = 1 - rowSquareMass f v :=
    Real.sq_sqrt (sub_nonneg.mpr (hrow v))
  simp only [rowSquareMass] at hs
  simp only [rowSquareMass, Fintype.sum_sum_type, paddedAmplitude]
  simp only [ite_pow, zero_pow (by decide : 2 ≠ 0)]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ v), hs]
  ring

def pairEnergy (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ) : ℝ :=
  ν.expectation fun e => ∑ ω,
    if R e (a (left e) ω) (a (right e) ω)
      then f (left e) ω * f (right e) ω else 0

def pairOverlap (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ) : ℝ :=
  ν.expectation fun e => ∑ ω,
    if R e (a (left e) ω) (a (right e) ω)
      then min ((f (left e) ω) ^ 2) ((f (right e) ω) ^ 2) else 0

omit [Fintype V] in
theorem pairEnergy_nonnegative (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) : 0 ≤ pairEnergy ν left right R a f := by
  apply Finset.sum_nonneg
  intro e _
  apply mul_nonneg (ν.nonnegative e)
  apply Finset.sum_nonneg
  intro ω _
  split
  · exact mul_nonneg (hf (left e) ω) (hf (right e) ω)
  · exact le_rfl

theorem pairEnergy_le_padded [DecidableEq V] (ν : FiniteDistribution E)
    (left right : E → V) (R : E → A → A → Bool)
    (a : V → Ω → A) (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) (fallback : A) :
    pairEnergy ν left right R a f ≤
      pairEnergy ν left right R (paddedLabel a fallback) (paddedAmplitude f) := by
  unfold pairEnergy FiniteDistribution.expectation
  apply Finset.sum_le_sum
  intro e _
  apply mul_le_mul_of_nonneg_left _ (ν.nonnegative e)
  dsimp only
  rw [Fintype.sum_sum_type]
  simp only [paddedLabel, paddedAmplitude]
  have hnonneg : 0 ≤ ∑ w : V,
      if R e fallback fallback then
        (if left e = w then Real.sqrt (1 - rowSquareMass f (left e)) else 0) *
          (if right e = w then Real.sqrt (1 - rowSquareMass f (right e)) else 0)
      else 0 := by
    apply Finset.sum_nonneg
    intro w _
    split
    · exact mul_nonneg (paddedAmplitude_nonnegative f hf (left e) (Sum.inr w))
        (paddedAmplitude_nonnegative f hf (right e) (Sum.inr w))
    · exact le_rfl
  exact le_add_of_nonneg_right hnonneg

end
end DFVSGames.Repetition


namespace DFVSGames.Repetition

open scoped BigOperators
open Foundations.Games

noncomputable section

variable {V A Ω E : Type*} [Fintype V] [Fintype Ω] [Fintype E]

omit [Fintype V] in
theorem pairQuadraticMass_eq_one (ν : FiniteDistribution E) (left right : E → V)
    (f : V → Ω → ℝ) (hrow : ∀ v, rowSquareMass f v = 1) :
    Analytic.quadraticMass (fun p : E × Ω => ν.weight p.1)
      (fun p => f (left p.1) p.2) (fun p => f (right p.1) p.2) = 1 := by
  unfold Analytic.quadraticMass
  rw [Fintype.sum_prod_type]
  have he (e : E) :
      (∑ ω, ν.weight e * ((f (left e) ω) ^ 2 + (f (right e) ω) ^ 2) / 2) =
        ν.weight e := by
    calc
      _ = ν.weight e *
          ((∑ ω, (f (left e) ω) ^ 2) + (∑ ω, (f (right e) ω) ^ 2)) / 2 := by
        simp only [div_eq_mul_inv, mul_add, add_mul, Finset.sum_add_distrib,
          Finset.mul_sum, Finset.sum_mul]
      _ = ν.weight e := by
        change ν.weight e * (rowSquareMass f (left e) + rowSquareMass f (right e)) / 2 = _
        rw [hrow, hrow]
        ring
  simp_rw [he]
  exact ν.normalized

omit [Fintype V] in
theorem pairGatedCorrelation_eq_energy (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ) :
    Analytic.gatedCorrelation (fun p : E × Ω => ν.weight p.1)
      (fun p => f (left p.1) p.2) (fun p => f (right p.1) p.2)
      (fun p => R p.1 (a (left p.1) p.2) (a (right p.1) p.2)) =
      pairEnergy ν left right R a f := by
  simp only [Analytic.gatedCorrelation, pairEnergy, FiniteDistribution.expectation,
    Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero, mul_assoc]

omit [Fintype V] in
theorem pairGatedMinimum_eq_overlap (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ) :
    Analytic.gatedMinimum (fun p : E × Ω => ν.weight p.1)
      (fun p => f (left p.1) p.2) (fun p => f (right p.1) p.2)
      (fun p => R p.1 (a (left p.1) p.2) (a (right p.1) p.2)) =
      pairOverlap ν left right R a f := by
  simp only [Analytic.gatedMinimum, pairOverlap, FiniteDistribution.expectation,
    Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero]

omit [Fintype V] in
theorem pairEnergy_le_one_of_unit_rows (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ)
    (hrow : ∀ v, rowSquareMass f v = 1) : pairEnergy ν left right R a f ≤ 1 := by
  have h := Analytic.gatedCorrelation_le_mass (fun p : E × Ω => ν.weight p.1)
    (fun p => f (left p.1) p.2) (fun p => f (right p.1) p.2)
    (fun p => R p.1 (a (left p.1) p.2) (a (right p.1) p.2))
    (fun p => ν.nonnegative p.1)
  rw [pairGatedCorrelation_eq_energy, pairQuadraticMass_eq_one ν left right f hrow] at h
  exact h

omit [Fintype V] in

theorem pairOverlap_ge_energy (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) (hrow : ∀ v, rowSquareMass f v = 1) :
    1 - Real.sqrt (2 * (1 - pairEnergy ν left right R a f)) ≤
      pairOverlap ν left right R a f := by
  have h := Analytic.gatedMinimum_unit_mass (fun p : E × Ω => ν.weight p.1)
    (fun p => f (left p.1) p.2) (fun p => f (right p.1) p.2)
    (fun p => R p.1 (a (left p.1) p.2) (a (right p.1) p.2))
    (fun p => ν.nonnegative p.1) (fun p => hf (left p.1) p.2)
    (fun p => hf (right p.1) p.2) (pairQuadraticMass_eq_one ν left right f hrow)
  rw [pairGatedCorrelation_eq_energy, pairGatedMinimum_eq_overlap] at h
  exact h

end
end DFVSGames.Repetition


namespace DFVSGames.Foundations.CorrelatedSampling

def firstAccepted {σ : Type*} (accept : σ → Bool) : List σ → Option σ
  | [] => none
  | proposal :: rest =>
      if accept proposal then some proposal else firstAccepted accept rest

theorem first_union_common {σ : Type*} (left right : σ → Bool)
    (proposals : List σ) (proposal : σ)
    (hfirst : firstAccepted (fun s => left s || right s) proposals = some proposal)
    (hleft : left proposal = true) (hright : right proposal = true) :
    firstAccepted left proposals = some proposal ∧
      firstAccepted right proposals = some proposal := by
  induction proposals with
  | nil => simp [firstAccepted] at hfirst
  | cons head tail ih =>
      by_cases hl : left head = true
      · have heq : head = proposal := by
          simpa [firstAccepted, hl] using hfirst
        subst head
        simp [firstAccepted, hleft, hright]
      · by_cases hr : right head = true
        · have heq : head = proposal := by
            simpa [firstAccepted, hl, hr] using hfirst
          subst head
          exact False.elim (hl hleft)
        · have htail : firstAccepted (fun s => left s || right s) tail = some proposal := by
            simpa [firstAccepted, hl, hr] using hfirst
          simpa [firstAccepted, hl, hr] using ih htail

def thresholdSample {α : Type*} (mass : α → Nat) (proposals : List (α × Nat)) :
    Option α :=
  (firstAccepted (fun s => decide (s.2 < mass s.1)) proposals).map Prod.fst

theorem thresholdSample_agreement {α : Type*} (left right : α → Nat)
    (proposals : List (α × Nat)) (a : α) (height : Nat)
    (hfirst : firstAccepted
      (fun s => decide (s.2 < left s.1) || decide (s.2 < right s.1)) proposals =
      some (a, height))
    (hcommon : height < min (left a) (right a)) :
    thresholdSample left proposals = some a ∧
      thresholdSample right proposals = some a := by
  have h := first_union_common
    (fun s : α × Nat => decide (s.2 < left s.1))
    (fun s : α × Nat => decide (s.2 < right s.1)) proposals (a, height) hfirst
    (by simpa using (lt_min_iff.mp hcommon).1)
    (by simpa using (lt_min_iff.mp hcommon).2)
  simp [thresholdSample, h.1, h.2]

noncomputable section FiniteWeights

variable {α : Type*} [Fintype α]

def totalVariation (p q : α → ℝ) : ℝ := (∑ a, |p a - q a|) / 2

def overlapMass (p q : α → ℝ) : ℝ := ∑ a, min (p a) (q a)

def unionMass (p q : α → ℝ) : ℝ := ∑ a, max (p a) (q a)

theorem totalVariation_nonneg (p q : α → ℝ) : 0 ≤ totalVariation p q := by
  unfold totalVariation
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by norm_num)

theorem overlapMass_nonneg (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hq : ∀ a, 0 ≤ q a) : 0 ≤ overlapMass p q := by
  exact Finset.sum_nonneg (fun a _ => le_min (hp a) (hq a))

private theorem min_abs_identity_inline_Basic (x y : ℝ) : 2 * min x y + |x - y| = x + y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

private theorem max_abs_identity_inline_Basic (x y : ℝ) : 2 * max x y - |x - y| = x + y := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem overlapMass_eq (p q : α → ℝ) (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
    overlapMass p q = 1 - totalVariation p q := by
  have h := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun a _ => min_abs_identity_inline_Basic (p a) (q a))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hp, hq] at h
  unfold overlapMass totalVariation
  linarith

theorem unionMass_eq (p q : α → ℝ) (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
    unionMass p q = 1 + totalVariation p q := by
  have h := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun a _ => max_abs_identity_inline_Basic (p a) (q a))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hp, hq] at h
  unfold unionMass totalVariation
  linarith

theorem totalVariation_le_one (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hq : ∀ a, 0 ≤ q a) (hpsum : ∑ a, p a = 1) (hqsum : ∑ a, q a = 1) :
    totalVariation p q ≤ 1 := by
  have h := overlapMass_nonneg p q hp hq
  rw [overlapMass_eq p q hpsum hqsum] at h
  linarith

theorem overlap_union_ratio (p q : α → ℝ)
    (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
    overlapMass p q / unionMass p q =
      (1 - totalVariation p q) / (1 + totalVariation p q) := by
  rw [overlapMass_eq p q hp hq, unionMass_eq p q hp hq]

theorem overlap_union_ratio_lower_bound (p q : α → ℝ)
    (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
    1 - 2 * totalVariation p q ≤ overlapMass p q / unionMass p q := by
  rw [overlap_union_ratio p q hp hq]
  have htv := totalVariation_nonneg p q
  have hden : 0 < 1 + totalVariation p q := by linarith
  apply (le_div_iff₀ hden).2
  nlinarith [sq_nonneg (totalVariation p q)]

theorem first_union_disagreement_upper_bound (p q : α → ℝ)
    (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
    1 - overlapMass p q / unionMass p q ≤ 2 * totalVariation p q := by
  linarith [overlap_union_ratio_lower_bound p q hp hq]

end FiniteWeights


noncomputable section

variable {σ : Type*} [Fintype σ]

def eventMass (w : σ → ℝ) (event : σ → Bool) : ℝ :=
  ∑ s, if event s then w s else 0

theorem eventMass_nonneg (w : σ → ℝ) (event : σ → Bool) (hw : ∀ s, 0 ≤ w s) :
    0 ≤ eventMass w event := by
  apply Finset.sum_nonneg
  intro s _
  split <;> simp_all

theorem eventMass_complement (w : σ → ℝ) (event : σ → Bool)
    (hw : ∑ s, w s = 1) :
    eventMass w event + eventMass w (fun s => !(event s)) = 1 := by
  unfold eventMass
  rw [← Finset.sum_add_distrib]
  calc
    ∑ s, ((if event s then w s else 0) + (if !event s then w s else 0)) = ∑ s, w s := by
      apply Finset.sum_congr rfl
      intro s _
      cases event s <;> simp
    _ = 1 := hw

def geometricMass (r : ℝ) : Nat → ℝ
  | 0 => 0
  | n + 1 => 1 + r * geometricMass r n

theorem geometricMass_nonneg (r : ℝ) (hr : 0 ≤ r) (n : Nat) :
    0 ≤ geometricMass r n := by
  induction n with
  | zero => simp [geometricMass]
  | succ n ih => exact add_nonneg (by norm_num) (mul_nonneg hr ih)

theorem geometricMass_identity (r : ℝ) (n : Nat) :
    (1 - r) * geometricMass r n = 1 - r ^ n := by
  induction n with
  | zero => simp [geometricMass]
  | succ n ih =>
      simp only [geometricMass, pow_succ]
      calc
        (1 - r) * (1 + r * geometricMass r n) =
            (1 - r) + r * ((1 - r) * geometricMass r n) := by ring
        _ = 1 - r ^ n * r := by rw [ih]; ring

def firstHitWeight (w : σ → ℝ) (accept : σ → Bool) : Nat → Option σ → ℝ
  | 0, none => 1
  | 0, some _ => 0
  | n + 1, none => eventMass w (fun s => !(accept s)) * firstHitWeight w accept n none
  | n + 1, some s =>
      (if accept s then w s else 0) +
        eventMass w (fun s => !(accept s)) * firstHitWeight w accept n (some s)

theorem firstHitWeight_nonneg (w : σ → ℝ) (accept : σ → Bool)
    (hw : ∀ s, 0 ≤ w s) (n : Nat) (output : Option σ) :
    0 ≤ firstHitWeight w accept n output := by
  induction n generalizing output with
  | zero => cases output <;> simp [firstHitWeight]
  | succ n ih =>
      have hr := eventMass_nonneg w (fun s => !(accept s)) hw
      cases output with
      | none => exact mul_nonneg hr (ih none)
      | some s =>
          apply add_nonneg
          · split <;> simp_all
          · exact mul_nonneg hr (ih (some s))

theorem firstHitWeight_none (w : σ → ℝ) (accept : σ → Bool) (n : Nat) :
    firstHitWeight w accept n none = eventMass w (fun s => !(accept s)) ^ n := by
  induction n with
  | zero => simp [firstHitWeight]
  | succ n ih => simp [firstHitWeight, ih, pow_succ, mul_comm]

theorem firstHitWeight_some (w : σ → ℝ) (accept : σ → Bool) (n : Nat) (s : σ) :
    firstHitWeight w accept n (some s) =
      (if accept s then w s else 0) *
        geometricMass (eventMass w (fun s => !(accept s))) n := by
  induction n with
  | zero => simp [firstHitWeight, geometricMass]
  | succ n ih =>
      rw [firstHitWeight, geometricMass, ih]
      ring

theorem firstHitWeight_normalized (w : σ → ℝ) (accept : σ → Bool)
    (hw : ∑ s, w s = 1) (n : Nat) : ∑ output, firstHitWeight w accept n output = 1 := by
  rw [Fintype.sum_option, firstHitWeight_none]
  simp_rw [firstHitWeight_some]
  rw [← Finset.sum_mul]
  change eventMass w (fun s => !(accept s)) ^ n +
    eventMass w accept * geometricMass (eventMass w (fun s => !(accept s))) n = 1
  have hc := eventMass_complement w accept hw
  have hg := geometricMass_identity (eventMass w (fun s => !(accept s))) n
  have ha : eventMass w accept = 1 - eventMass w (fun s => !(accept s)) := by linarith
  rw [ha, hg]
  ring

def goodFirstMass (w : σ → ℝ) (accept good : σ → Bool) (n : Nat) : ℝ :=
  ∑ s, if good s then firstHitWeight w accept n (some s) else 0

theorem goodFirstMass_eq (w : σ → ℝ) (accept good : σ → Bool) (n : Nat) :
    goodFirstMass w accept good n =
      eventMass w (fun s => accept s && good s) *
        geometricMass (eventMass w (fun s => !(accept s))) n := by
  unfold goodFirstMass eventMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [firstHitWeight_some]
  cases ha : accept s <;> cases hg : good s <;> simp [ha, hg, eventMass]

theorem goodFirstMass_exact (w : σ → ℝ) (accept good : σ → Bool)
    (hw : ∑ s, w s = 1) (ha : eventMass w accept ≠ 0) (n : Nat) :
    goodFirstMass w accept good n =
      eventMass w (fun s => accept s && good s) / eventMass w accept *
        (1 - eventMass w (fun s => !(accept s)) ^ n) := by
  rw [goodFirstMass_eq]
  have hc := eventMass_complement w accept hw
  have hg := geometricMass_identity (eventMass w (fun s => !(accept s))) n
  have hgeom : eventMass w accept *
      geometricMass (eventMass w (fun s => !(accept s))) n =
      1 - eventMass w (fun s => !(accept s)) ^ n := by
    have heq : eventMass w accept = 1 - eventMass w (fun s => !(accept s)) := by linarith
    rw [heq, hg]
  rw [← hgeom]
  field_simp

theorem commonMass_le_acceptMass (w : σ → ℝ) (accept good : σ → Bool)
    (hw : ∀ s, 0 ≤ w s) :
    eventMass w (fun s => accept s && good s) ≤ eventMass w accept := by
  apply Finset.sum_le_sum
  intro s _
  cases ha : accept s <;> cases hg : good s <;> simp [ha, hg, hw s]

theorem goodFirstMass_lower_bound (w : σ → ℝ) (accept good : σ → Bool)
    (hw : ∀ s, 0 ≤ w s) (hw_sum : ∑ s, w s = 1)
    (ha : 0 < eventMass w accept) (n : Nat) :
    eventMass w (fun s => accept s && good s) / eventMass w accept -
        eventMass w (fun s => !(accept s)) ^ n ≤ goodFirstMass w accept good n := by
  rw [goodFirstMass_exact w accept good hw_sum (ne_of_gt ha) n]
  have hratio : eventMass w (fun s => accept s && good s) / eventMass w accept ≤ 1 := by
    apply (div_le_one ha).2
    exact commonMass_le_acceptMass w accept good hw
  have htail : 0 ≤ eventMass w (fun s => !(accept s)) ^ n :=
    pow_nonneg (eventMass_nonneg w (fun s => !(accept s)) hw) n
  nlinarith

end

end DFVSGames.Foundations.CorrelatedSampling

end OAI
