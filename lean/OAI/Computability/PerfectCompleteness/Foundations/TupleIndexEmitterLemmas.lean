import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import OAI.Computability.PerfectCompleteness.Foundations.DualQuotientRowsLemmas
import OAI.Computability.UniqueGames.Foundations.Conditioning
import OAI.Computability.UniqueGames.Foundations.MixtureLemmas
import OAI.Computability.UniqueGames.Foundations.ValueLemmas
import OAI.Computability.UniqueGames.Machines.MachineCopy
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas

namespace OAI


namespace PerfectCompleteness.TupleIndexEmitter

open Turing UniqueGamesTheorem.Foundations.Complexity

inductive Tape (width : Nat) (Extra : Type)
  | current (coordinate : Fin width)
  | scratch
  | output
  | extra (value : Extra)
  deriving DecidableEq, Fintype

inductive Label (width : Nat)
  | copyOut (coordinate : Fin width)
  | copyBack (coordinate : Fin width)
  | done
  deriving DecidableEq, Fintype

variable {width : Nat} {Extra σ : Type}

def labelAt : Nat → Label width
  | 0 => .done
  | r + 1 => if h : r < width then .copyOut ⟨r, h⟩ else .done

def program : Label width →
    TM2.Stmt (fun _ : Tape width Extra => Bool) (Label width) (σ × Option Bool)
  | .copyOut j => UniqueGamesTheorem.Reduction.MachineTransfer.loopAt
      (.current j) .scratch id false (.copyOut j) (some (.copyBack j))
  | .copyBack j => MachineCopy.forkLoop
      .scratch (.current j) .output false (.copyBack j) (some (labelAt j.val))
  | .done => .halt

def prefixWords (d : Fin width → Nat) (r : Nat) (hr : r ≤ width) : List Nat :=
  List.ofFn (fun i : Fin r => d ⟨i.val, Nat.lt_of_lt_of_le i.isLt hr⟩)

@[simp] theorem prefixWords_zero (d : Fin width → Nat) :
    prefixWords d 0 (Nat.zero_le _) = [] := rfl

theorem prefixWords_succ (d : Fin width → Nat) (r : Nat) (hr : r + 1 ≤ width) :
    prefixWords d (r + 1) hr =
      prefixWords d r (by omega) ++ [d ⟨r, by omega⟩] := by
  rw [prefixWords, List.ofFn_succ', List.concat_eq_append]
  rfl

@[simp] theorem prefixWords_all (d : Fin width → Nat) :
    prefixWords d width (Nat.le_refl _) = List.ofFn d := by
  rfl

def prefixBudget (d : Fin width → Nat) (r : Nat) (hr : r ≤ width) : Nat :=
  ((prefixWords d r hr).map (fun n => 2 * (n + 2))).sum

@[simp] theorem prefixBudget_zero (d : Fin width → Nat) :
    prefixBudget d 0 (Nat.zero_le _) = 0 := rfl

theorem prefixBudget_succ (d : Fin width → Nat) (r : Nat) (hr : r + 1 ≤ width) :
    prefixBudget d (r + 1) hr =
      prefixBudget d r (by omega) + 2 * (d ⟨r, by omega⟩ + 2) := by
  simp only [prefixBudget, prefixWords_succ, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

@[simp] theorem prefixBudget_all (d : Fin width → Nat) :
    prefixBudget d width (Nat.le_refl _) = ∑ j, 2 * (d j + 2) := by
  simp only [prefixBudget, prefixWords_all, List.map_ofFn, Function.comp_def,
    List.sum_ofFn]

variable [DecidableEq Extra]

def outputTapes (base : Tape width Extra → List Bool) (bits : List Bool) :
    Tape width Extra → List Bool :=
  Function.update base .output (bits ++ base .output)

@[simp] theorem outputTapes_output (base : Tape width Extra → List Bool) (bits : List Bool) :
    outputTapes base bits .output = bits ++ base .output := by
  simp [outputTapes]

@[simp] theorem outputTapes_current (base : Tape width Extra → List Bool)
    (bits : List Bool) (j : Fin width) :
    outputTapes base bits (.current j) = base (.current j) := by
  simp [outputTapes]

@[simp] theorem outputTapes_scratch (base : Tape width Extra → List Bool) (bits : List Bool) :
    outputTapes base bits .scratch = base .scratch := by
  simp [outputTapes]

@[simp] theorem outputTapes_extra (base : Tape width Extra → List Bool)
    (bits : List Bool) (x : Extra) :
    outputTapes base bits (.extra x) = base (.extra x) := by
  simp [outputTapes]

@[simp] theorem outputTapes_nil (base : Tape width Extra → List Bool) :
    outputTapes base [] = base := by
  simp [outputTapes]

theorem outputTapes_outputTapes (base : Tape width Extra → List Bool)
    (first second : List Bool) :
    outputTapes (outputTapes base first) second = outputTapes base (second ++ first) := by
  simp [outputTapes, Function.update_idem, List.append_assoc]

noncomputable def prefixInTimeFor {Λ : Type}
    (labels : Label width → Λ)
    (target : Λ → TM2.Stmt (fun _ : Tape width Extra => Bool) Λ (σ × Option Bool))
    (atCopyOut : ∀ j, target (labels (.copyOut j)) =
      UniqueGamesTheorem.Reduction.MachineTransfer.loopAt (.current j) .scratch id false
        (labels (.copyOut j)) (some (labels (.copyBack j))))
    (atCopyBack : ∀ j, target (labels (.copyBack j)) =
      MachineCopy.forkLoop .scratch (.current j) .output false
        (labels (.copyBack j)) (some (labels (labelAt j.val))))
    (d : Fin width → Nat) (r : Nat) (hr : r ≤ width)
    (base : Tape width Extra → List Bool)
    (hsaved : ∀ j, base (.current j) = encodeWord (d j))
    (hscratch : base .scratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (labelAt r)), (ambient, none), base⟩
      (some ⟨some (labels .done), (ambient, none),
        outputTapes base (encodeWords (prefixWords d r hr))⟩)
      (prefixBudget d r hr) := by
  induction r generalizing base with
  | zero =>
    exact {
      steps := 0
      evals_in_steps := by simp [labelAt, encodeWords]
      steps_le_m := Nat.le_refl _
    }
  | succ r ih =>
    have hlt : r < width := by omega
    let j : Fin width := ⟨r, hlt⟩
    let after := outputTapes base (encodeWord (d j))
    have copied := MachineCopy.copyInTime (.current j) .output .scratch
      (by simp) (by simp) (by simp) false (labels (.copyOut j)) (labels (.copyBack j))
      (some (labels (labelAt j.val))) target (atCopyOut j) (atCopyBack j) base hscratch ambient none
    have first : StateTransition.EvalsToInTime (TM2.step target)
        ⟨some (labels (labelAt (r + 1))), (ambient, none), base⟩
        (some ⟨some (labels (labelAt r)), (ambient, none), after⟩)
        (2 * (d j + 2)) := by
      simpa only [labelAt, dite_eq_left hlt, hsaved j, encodeWord_length,
        Nat.add_assoc, after, outputTapes, j] using copied
    have rest := ih (by omega) after
      (by intro i; simpa only [after, outputTapes_current] using hsaved i)
      (by simpa only [after, outputTapes_scratch] using hscratch)
    have joined := StateTransition.EvalsToInTime.trans (TM2.step target) _ _ _ _ _ first rest
    have output_eq :
        outputTapes after (encodeWords (prefixWords d r (by omega))) =
          outputTapes base (encodeWords (prefixWords d (r + 1) hr)) := by
      dsimp only [after]
      rw [outputTapes_outputTapes, prefixWords_succ, encodeWords_append]
      simp only [encodeWords, List.append_nil, j]
    rw [output_eq] at joined
    simpa only [prefixBudget_succ, j] using joined

noncomputable def prefixInTime (d : Fin width → Nat) (r : Nat) (hr : r ≤ width)
    (base : Tape width Extra → List Bool)
    (hsaved : ∀ j, base (.current j) = encodeWord (d j))
    (hscratch : base .scratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt r), (ambient, none), base⟩
      (some ⟨some .done, (ambient, none),
        outputTapes base (encodeWords (prefixWords d r hr))⟩)
      (prefixBudget d r hr) :=
  prefixInTimeFor id program (fun _ => rfl) (fun _ => rfl)
    d r hr base hsaved hscratch ambient

noncomputable def emitInTimeFor {Λ : Type}
    (labels : Label width → Λ)
    (target : Λ → TM2.Stmt (fun _ : Tape width Extra => Bool) Λ (σ × Option Bool))
    (atCopyOut : ∀ j, target (labels (.copyOut j)) =
      UniqueGamesTheorem.Reduction.MachineTransfer.loopAt (.current j) .scratch id false
        (labels (.copyOut j)) (some (labels (.copyBack j))))
    (atCopyBack : ∀ j, target (labels (.copyBack j)) =
      MachineCopy.forkLoop .scratch (.current j) .output false
        (labels (.copyBack j)) (some (labels (labelAt j.val))))
    (d : Fin width → Nat) (base : Tape width Extra → List Bool)
    (hsaved : ∀ j, base (.current j) = encodeWord (d j))
    (hscratch : base .scratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (labelAt width)), (ambient, none), base⟩
      (some ⟨some (labels .done), (ambient, none),
        outputTapes base (encodeWords (List.ofFn d))⟩)
      (∑ j, 2 * (d j + 2)) := by
  simpa only [prefixWords_all, prefixBudget_all] using
    prefixInTimeFor labels target atCopyOut atCopyBack d width (Nat.le_refl _)
      base hsaved hscratch ambient

noncomputable def emitInTime (d : Fin width → Nat)
    (base : Tape width Extra → List Bool)
    (hsaved : ∀ j, base (.current j) = encodeWord (d j))
    (hscratch : base .scratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt width), (ambient, none), base⟩
      (some ⟨some .done, (ambient, none),
        outputTapes base (encodeWords (List.ofFn d))⟩)
      (∑ j, 2 * (d j + 2)) := by
  simpa only [prefixWords_all, prefixBudget_all] using
    prefixInTime d width (Nat.le_refl _) base hsaved hscratch ambient

theorem budget_eq (d : Fin width → Nat) :
    (∑ j, 2 * (d j + 2)) = 2 * (∑ j : Fin width, (d j + 1)) + 2 * width := by
  calc
    (∑ j, 2 * (d j + 2)) = ∑ j : Fin width, (2 * (d j + 1) + 2) := by
      apply Finset.sum_congr rfl
      intro j _
      omega
    _ = 2 * (∑ j : Fin width, (d j + 1)) + 2 * width := by
      have hconst : (∑ _j : Fin width, (2 : Nat)) = 2 * width := by
        simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          Nat.nsmul_eq_mul] using (Nat.mul_comm width 2)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hconst]

noncomputable def placedEmitInTime {Λ : Type}
    (labels : Label width → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : Tape width Extra => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ l, target (labels l) = MachineSubroutine.statement labels exit (program l))
    (d : Fin width → Nat) (base : Tape width Extra → List Bool)
    (hsaved : ∀ j, base (.current j) = encodeWord (d j))
    (hscratch : base .scratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (labelAt width)), (ambient, none), base⟩
      (some ⟨some (labels .done), (ambient, none),
        outputTapes base (encodeWords (List.ofFn d))⟩)
      (∑ j, 2 * (d j + 2)) :=
  MachineSubroutine.execution labels exit program target atLabels
    (emitInTime d base hsaved hscratch ambient)

noncomputable def haltInTime (d : Fin width → Nat)
    (base : Tape width Extra → List Bool)
    (hsaved : ∀ j, base (.current j) = encodeWord (d j))
    (hscratch : base .scratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt width), (ambient, none), base⟩
      (some ⟨none, (ambient, none),
        outputTapes base (encodeWords (List.ofFn d))⟩)
      ((∑ j, 2 * (d j + 2)) + 1) := by
  have body := emitInTime d base hsaved hscratch ambient
  have finish : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .done, (ambient, none), outputTapes base (encodeWords (List.ofFn d))⟩
      (some ⟨none, (ambient, none), outputTapes base (encodeWords (List.ofFn d))⟩) 1 :=
    { steps := 1, evals_in_steps := rfl, steps_le_m := Nat.le_refl _ }
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ body finish
  simpa only [Nat.add_comm] using joined

def machine (width : Nat) (Extra : Type) [DecidableEq Extra] [Fintype Extra] : FinTM2 where
  K := Tape width Extra
  k₀ := .output
  k₁ := .output
  Γ _ := Bool
  Λ := Label width
  main := labelAt width
  σ := Unit × Option Bool
  initialState := ((), none)
  m := program

end PerfectCompleteness.TupleIndexEmitter



namespace PerfectCompleteness.UsefulMark

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {Ω P : Type*} [Fintype Ω] [Fintype P]

def marginalMass (μ : FiniteDistribution Ω) (p : Ω → P) (z : P) : ℝ :=
  μ.probability (fun x => decide (p x = z))

def lowerFiberMass (μ : FiniteDistribution Ω) (p : Ω → P) (L : Ω → Bool)
    (z : P) : ℝ :=
  μ.probability (fun x => L x && decide (p x = z))

def conditionalLower (μ : FiniteDistribution Ω) (p : Ω → P) (L : Ω → Bool)
    (z : P) : ℝ :=
  lowerFiberMass μ p L z / marginalMass μ p z

def useful (μ : FiniteDistribution Ω) (p : Ω → P) (L : Ω → Bool)
    (κ : ℝ) (z : P) : Bool :=
  decide (0 < marginalMass μ p z ∧ κ ≤ conditionalLower μ p L z)

omit [Fintype P] in
theorem useful_iff (μ : FiniteDistribution Ω) (p : Ω → P) (L : Ω → Bool)
    (κ : ℝ) (z : P) :
    useful μ p L κ z = true ↔
      0 < marginalMass μ p z ∧ κ ≤ conditionalLower μ p L z := by
  simp only [useful, decide_eq_true_eq]

omit [Fintype P] in
theorem marginalMass_nonneg (μ : FiniteDistribution Ω) (p : Ω → P) (z : P) :
    0 ≤ marginalMass μ p z := μ.probability_nonnegative _

omit [Fintype P] in
theorem lowerFiberMass_nonneg (μ : FiniteDistribution Ω) (p : Ω → P)
    (L : Ω → Bool) (z : P) : 0 ≤ lowerFiberMass μ p L z :=
  μ.probability_nonnegative _

omit [Fintype P] in
theorem lowerFiberMass_le_marginalMass (μ : FiniteDistribution Ω) (p : Ω → P)
    (L : Ω → Bool) (z : P) : lowerFiberMass μ p L z ≤ marginalMass μ p z :=
  μ.probability_and_le_right L (fun x => decide (p x = z))

omit [Fintype P] in
theorem lowerFiberMass_eq_zero (μ : FiniteDistribution Ω) (p : Ω → P)
    (L : Ω → Bool) (z : P) (hzero : marginalMass μ p z = 0) :
    lowerFiberMass μ p L z = 0 :=
  le_antisymm ((lowerFiberMass_le_marginalMass μ p L z).trans_eq hzero)
    (lowerFiberMass_nonneg μ p L z)

omit [Fintype P] in
theorem conditionalLower_eq_zero (μ : FiniteDistribution Ω) (p : Ω → P)
    (L : Ω → Bool) (z : P) (hzero : marginalMass μ p z = 0) :
    conditionalLower μ p L z = 0 := by
  simp [conditionalLower, hzero]

theorem marginalMass_eq_pushforward_weight (μ : FiniteDistribution Ω)
    (p : Ω → P) (z : P) : marginalMass μ p z = (μ.pushforward p).weight z := by
  simp [marginalMass, FiniteDistribution.probability, FiniteDistribution.pushforward]

theorem sum_marginalMass (μ : FiniteDistribution Ω) (p : Ω → P) :
    (∑ z, marginalMass μ p z) = 1 := by
  simp_rw [marginalMass_eq_pushforward_weight]
  exact (μ.pushforward p).normalized

theorem probability_eq_sum_fibers (μ : FiniteDistribution Ω) (p : Ω → P)
    (event : Ω → Bool) : μ.probability event = ∑ z, lowerFiberMass μ p event z := by
  unfold lowerFiberMass FiniteDistribution.probability
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  cases he : event x <;> simp [he, eq_comm]

theorem probability_mark_eq_sum (μ : FiniteDistribution Ω) (p : Ω → P)
    (L : Ω → Bool) (mark : P → Bool) :
    μ.probability (fun x => L x && mark (p x)) =
      ∑ z, if mark z then lowerFiberMass μ p L z else 0 := by
  rw [probability_eq_sum_fibers μ p]
  apply Finset.sum_congr rfl
  intro z _
  unfold lowerFiberMass FiniteDistribution.probability
  by_cases hz : mark z = true
  · rw [ite_eq_left hz]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : p x = z <;> simp [hx, hz]
  · rw [ite_eq_right hz]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : p x = z <;> simp [hx, hz]

omit [Fintype P] in
theorem lowerFiberMass_le_of_not_useful (μ : FiniteDistribution Ω) (p : Ω → P)
    (L : Ω → Bool) (κ : ℝ) (z : P) (h : useful μ p L κ z ≠ true) :
    lowerFiberMass μ p L z ≤ κ * marginalMass μ p z := by
  by_cases hpos : 0 < marginalMass μ p z
  · have hlt : conditionalLower μ p L z < κ := by
      apply lt_of_not_ge
      intro hκ
      exact h ((useful_iff μ p L κ z).mpr ⟨hpos, hκ⟩)
    change lowerFiberMass μ p L z / marginalMass μ p z < κ at hlt
    exact ((div_lt_iff₀ hpos).mp hlt).le
  · have hzero : marginalMass μ p z = 0 :=
      le_antisymm (le_of_not_gt hpos) (marginalMass_nonneg μ p z)
    simp [lowerFiberMass_eq_zero μ p L z hzero, hzero]

theorem discarded_lower_le (μ : FiniteDistribution Ω) (p : Ω → P)
    (L : Ω → Bool) (κ : ℝ) (hκ : 0 ≤ κ) :
    μ.probability (fun x => L x && !useful μ p L κ (p x)) ≤ κ := by
  rw [probability_mark_eq_sum μ p L (fun z => !useful μ p L κ z)]
  calc
    _ ≤ ∑ z, κ * marginalMass μ p z := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hz : useful μ p L κ z = true
      · simpa [hz] using mul_nonneg hκ (marginalMass_nonneg μ p z)
      · simpa [hz] using
          lowerFiberMass_le_of_not_useful μ p L κ z hz
    _ = κ := by rw [← Finset.mul_sum, sum_marginalMass, mul_one]

omit [Fintype P] in
theorem joint_le_discarded_add_marked (μ : FiniteDistribution Ω) (p : Ω → P)
    (L upper : Ω → Bool) (mark : P → Bool) :
    μ.probability (fun x => L x && upper x) ≤
      μ.probability (fun x => L x && !mark (p x)) +
        μ.probability (fun x => upper x && mark (p x)) := by
  unfold FiniteDistribution.probability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  cases hL : L x <;> cases hU : upper x <;> cases hmark : mark (p x) <;>
    simp [hL, hU, hmark, μ.nonnegative x]

theorem useful_upper_ge_sub (μ : FiniteDistribution Ω) (p : Ω → P)
    (L upper : Ω → Bool) (κ c : ℝ) (hκ : 0 ≤ κ)
    (hjoint : c ≤ μ.probability (fun x => L x && upper x)) :
    c - κ ≤ μ.probability (fun x => upper x && useful μ p L κ (p x)) := by
  have hsplit := joint_le_discarded_add_marked μ p L upper (useful μ p L κ)
  have hdiscard := discarded_lower_le μ p L κ hκ
  linarith

theorem useful_upper_ge_half (μ : FiniteDistribution Ω) (p : Ω → P)
    (L upper : Ω → Bool) (c : ℝ) (hc : 0 ≤ c)
    (hjoint : c ≤ μ.probability (fun x => L x && upper x)) :
    c / 2 ≤ μ.probability (fun x => upper x && useful μ p L (c / 2) (p x)) := by
  have h := useful_upper_ge_sub μ p L upper (c / 2) c
    (div_nonneg hc (by norm_num)) hjoint
  linarith

end
end PerfectCompleteness.UsefulMark



namespace PerfectCompleteness.PositiveFiberMass

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {Ω R : Type*} [Fintype Ω] [Fintype R]

def jMass (μ : FiniteDistribution Ω) (record : Ω → R) (J : Ω → Bool) (r : R) : ℝ :=
  UsefulMark.lowerFiberMass μ record J r

def matchMass (μ : FiniteDistribution Ω) (record : Ω → R)
    (J prediction : Ω → Bool) (r : R) : ℝ :=
  UsefulMark.lowerFiberMass μ record (fun x => J x && prediction x) r

def conditionalMatch (μ : FiniteDistribution Ω) (record : Ω → R)
    (J prediction : Ω → Bool) (r : R) : ℝ :=
  matchMass μ record J prediction r / jMass μ record J r

def goodRecord (μ : FiniteDistribution Ω) (record : Ω → R)
    (J prediction : Ω → Bool) (ρ : ℝ) (r : R) : Bool :=
  decide (0 < jMass μ record J r ∧ ρ ≤ conditionalMatch μ record J prediction r)

omit [Fintype R] in
theorem goodRecord_iff (μ : FiniteDistribution Ω) (record : Ω → R)
    (J prediction : Ω → Bool) (ρ : ℝ) (r : R) :
    goodRecord μ record J prediction ρ r = true ↔
      0 < jMass μ record J r ∧ ρ ≤ conditionalMatch μ record J prediction r := by
  simp only [goodRecord, decide_eq_true_eq]

omit [Fintype R] in
theorem jMass_nonneg (μ : FiniteDistribution Ω) (record : Ω → R)
    (J : Ω → Bool) (r : R) : 0 ≤ jMass μ record J r :=
  μ.probability_nonnegative _

omit [Fintype R] in
theorem matchMass_nonneg (μ : FiniteDistribution Ω) (record : Ω → R)
    (J prediction : Ω → Bool) (r : R) : 0 ≤ matchMass μ record J prediction r :=
  μ.probability_nonnegative _

omit [Fintype R] in
theorem matchMass_le_jMass (μ : FiniteDistribution Ω) (record : Ω → R)
    (J prediction : Ω → Bool) (r : R) :
    matchMass μ record J prediction r ≤ jMass μ record J r := by
  apply μ.probability_mono
  intro x hx
  simp only [Bool.and_eq_true] at hx ⊢
  exact ⟨hx.1.1, hx.2⟩

omit [Fintype R] in
theorem matchMass_eq_zero (μ : FiniteDistribution Ω) (record : Ω → R)
    (J prediction : Ω → Bool) (r : R) (hzero : jMass μ record J r = 0) :
    matchMass μ record J prediction r = 0 :=
  le_antisymm ((matchMass_le_jMass μ record J prediction r).trans_eq hzero)
    (matchMass_nonneg μ record J prediction r)

omit [Fintype R] in
theorem matchMass_le_of_not_goodRecord (μ : FiniteDistribution Ω) (record : Ω → R)
    (J prediction : Ω → Bool) (ρ : ℝ) (r : R)
    (hbad : goodRecord μ record J prediction ρ r ≠ true) :
    matchMass μ record J prediction r ≤ ρ * jMass μ record J r := by
  by_cases hpos : 0 < jMass μ record J r
  · have hlt : conditionalMatch μ record J prediction r < ρ := by
      apply lt_of_not_ge
      intro hρ
      exact hbad ((goodRecord_iff μ record J prediction ρ r).mpr ⟨hpos, hρ⟩)
    change matchMass μ record J prediction r / jMass μ record J r < ρ at hlt
    exact ((div_lt_iff₀ hpos).mp hlt).le
  · have hzero : jMass μ record J r = 0 :=
      le_antisymm (le_of_not_gt hpos) (jMass_nonneg μ record J r)
    rw [matchMass_eq_zero μ record J prediction r hzero, hzero, mul_zero]

omit [Fintype R] in
theorem fiber_difference_le_good_mass (μ : FiniteDistribution Ω) (record : Ω → R)
    (J prediction : Ω → Bool) (ρ : ℝ) (hρ : 0 ≤ ρ) (r : R) :
    matchMass μ record J prediction r - ρ * jMass μ record J r ≤
      if goodRecord μ record J prediction ρ r then jMass μ record J r else 0 := by
  by_cases hgood : goodRecord μ record J prediction ρ r = true
  · rw [ite_eq_left hgood]
    have hmatch := matchMass_le_jMass μ record J prediction r
    have hproduct := mul_nonneg hρ (jMass_nonneg μ record J r)
    linarith
  · rw [ite_eq_right hgood]
    exact sub_nonpos.mpr (matchMass_le_of_not_goodRecord μ record J prediction ρ r hgood)

theorem sum_jMass (μ : FiniteDistribution Ω) (record : Ω → R) (J : Ω → Bool) :
    (∑ r, jMass μ record J r) = μ.probability J :=
  (UsefulMark.probability_eq_sum_fibers μ record J).symm

theorem sum_matchMass (μ : FiniteDistribution Ω) (record : Ω → R)
    (J prediction : Ω → Bool) :
    (∑ r, matchMass μ record J prediction r) =
      μ.probability (fun x => J x && prediction x) :=
  (UsefulMark.probability_eq_sum_fibers μ record (fun x => J x && prediction x)).symm

theorem difference_eq_sum (μ : FiniteDistribution Ω) (record : Ω → R)
    (J prediction : Ω → Bool) (ρ : ℝ) :
    μ.probability (fun x => J x && prediction x) - ρ * μ.probability J =
      ∑ r, (matchMass μ record J prediction r - ρ * jMass μ record J r) := by
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_matchMass, sum_jMass]

theorem difference_le_good_mass (μ : FiniteDistribution Ω) (record : Ω → R)
    (J prediction : Ω → Bool) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    μ.probability (fun x => J x && prediction x) - ρ * μ.probability J ≤
      μ.probability (fun x => J x && goodRecord μ record J prediction ρ (record x)) := by
  rw [difference_eq_sum μ record J prediction ρ,
    UsefulMark.probability_mark_eq_sum μ record J (goodRecord μ record J prediction ρ)]
  apply Finset.sum_le_sum
  intro r _
  exact fiber_difference_le_good_mass μ record J prediction ρ hρ r

theorem good_mass_ge_difference_lower_bound
    (μ : FiniteDistribution Ω) (record : Ω → R) (J prediction : Ω → Bool)
    (ρ b : ℝ) (hρ : 0 ≤ ρ)
    (hdifference : b ≤ μ.probability (fun x => J x && prediction x) - ρ * μ.probability J) :
    b ≤ μ.probability (fun x => J x && goodRecord μ record J prediction ρ (record x)) :=
  hdifference.trans (difference_le_good_mass μ record J prediction ρ hρ)

omit [Fintype R] in
theorem conditional_probability_ge_of_goodRecord
    (μ : FiniteDistribution Ω) (record : Ω → R) (J prediction : Ω → Bool)
    (ρ : ℝ) (r : R) (hgood : goodRecord μ record J prediction ρ r = true) :
    ρ ≤ (μ.condition (fun x => J x && decide (record x = r))
      ((goodRecord_iff μ record J prediction ρ r).mp hgood).1).probability prediction := by
  have hp : 0 < μ.probability (fun x => J x && decide (record x = r)) :=
    ((goodRecord_iff μ record J prediction ρ r).mp hgood).1
  change ρ ≤ (μ.condition (fun x => J x && decide (record x = r)) hp).probability prediction
  rw [FiniteDistribution.probability_condition]
  have hevent : (fun x => (J x && decide (record x = r)) && prediction x) =
      (fun x => (J x && prediction x) && decide (record x = r)) := by
    funext x
    cases J x <;> cases prediction x <;> cases decide (record x = r) <;> rfl
  rw [hevent]
  exact ((goodRecord_iff μ record J prediction ρ r).mp hgood).2

end
end PerfectCompleteness.PositiveFiberMass



namespace PerfectCompleteness.UsefulAdvice

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open UsefulMark

noncomputable section

variable {Ω P : Type*} [Fintype Ω] [Fintype P]

theorem marked_probability_eq_sum (μ : FiniteDistribution Ω) (p : Ω → P)
    (event : P → Bool) :
    μ.probability (fun x => event (p x)) =
      ∑ z, if event z then marginalMass μ p z else 0 := by
  simpa only [lowerFiberMass, marginalMass, Bool.true_and] using
    probability_mark_eq_sum μ p (fun _ => true) event

omit [Fintype P] in
theorem useful_fiber_lower (μ : FiniteDistribution Ω) (p : Ω → P)
    (L : Ω → Bool) (κ : ℝ) (z : P) (hz : useful μ p L κ z = true) :
    κ * marginalMass μ p z ≤ lowerFiberMass μ p L z := by
  obtain ⟨hpos, hratio⟩ := (useful_iff μ p L κ z).mp hz
  exact (le_div_iff₀ hpos).mp hratio

theorem marked_lower_bound (μ : FiniteDistribution Ω) (p : Ω → P)
    (L : Ω → Bool) (κ : ℝ) (event : P → Bool)
    (hmarked : ∀ z, event z = true → useful μ p L κ z = true) :
    κ * μ.probability (fun x => event (p x)) ≤
      μ.probability (fun x => L x && event (p x)) := by
  rw [marked_probability_eq_sum μ p event,
    probability_mark_eq_sum μ p L event, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  by_cases hz : event z = true
  · simpa only [ite_eq_left hz] using useful_fiber_lower μ p L κ z (hmarked z hz)
  · simp only [ite_eq_right hz, mul_zero, le_refl]

variable {A : Type*} [Fintype A]

theorem product_probability_advice_first (μ : FiniteDistribution Ω)
    (ν : FiniteDistribution A) (event : Ω × A → Bool) :
    (μ.product ν).probability event =
      ν.expectation (fun a => μ.probability (fun x => event (x, a))) := by
  calc
    _ = ∑ x, ∑ a, if event (x, a) then μ.weight x * ν.weight a else 0 := by
      simp only [FiniteDistribution.probability, FiniteDistribution.product,
        Fintype.sum_prod_type]
    _ = ∑ a, ∑ x, if event (x, a) then μ.weight x * ν.weight a else 0 :=
      Finset.sum_comm
    _ = _ := by
      simp only [FiniteDistribution.expectation, FiniteDistribution.probability,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro x _
      by_cases he : event (x, a) = true <;> simp [he, mul_comm]

theorem independent_advice_lower_bound (μ : FiniteDistribution Ω)
    (ν : FiniteDistribution A) (p : Ω → P) (L : Ω → Bool) (κ : ℝ)
    (event : P × A → Bool)
    (hmarked : ∀ z a, event (z, a) = true → useful μ p L κ z = true) :
    κ * (μ.product ν).probability (fun x => event (p x.1, x.2)) ≤
      (μ.product ν).probability (fun x => L x.1 && event (p x.1, x.2)) := by
  rw [product_probability_advice_first, product_probability_advice_first,
    ← SmallBiasSlice.expectation_const_mul]
  apply PerfectCompleteness.SmallBias.expectation_mono
  intro a
  exact marked_lower_bound μ p L κ (fun z => event (z, a)) (fun z => hmarked z a)

theorem independent_advice_predicts (μ : FiniteDistribution Ω)
    (ν : FiniteDistribution A) (p : Ω → P) (L : Ω → Bool) (κ : ℝ)
    (event : P × A → Bool) (prediction : Ω × A → Bool)
    (hmarked : ∀ z a, event (z, a) = true → useful μ p L κ z = true)
    (hpredict : ∀ x a, L x = true → event (p x, a) = true →
      prediction (x, a) = true) :
    κ * (μ.product ν).probability (fun x => event (p x.1, x.2)) ≤
      (μ.product ν).probability prediction := by
  apply (independent_advice_lower_bound μ ν p L κ event hmarked).trans
  apply FiniteDistribution.probability_mono
  rintro ⟨x, a⟩ h
  have hh := Bool.and_eq_true_iff.mp h
  exact hpredict x a hh.1 hh.2

end
end PerfectCompleteness.UsefulAdvice



namespace PerfectCompleteness.PredictionDifference

open scoped Classical
open UniqueGamesTheorem.Foundations.Games

noncomputable section

theorem scalar_bound (κ α q₀ v h pI pJ pMatch : ℝ)
    (hκ : 0 ≤ κ) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hq₀ : 0 ≤ q₀)
    (hv : 0 ≤ v) (hsmall : v ≤ α * q₀ / 16) (hmass : q₀ ≤ h)
    (hI : α * h - v ≤ pI) (hJ : pJ ≤ h + v)
    (hpredict : κ * pI ≤ pMatch) :
    κ * α * q₀ / 4 ≤ pMatch - (κ * α / 4) * pJ := by
  have hκα : 0 ≤ κ * α := mul_nonneg hκ hα
  have hρ : 0 ≤ κ * α / 4 := div_nonneg hκα (by norm_num)
  have hρκ : κ * α / 4 ≤ κ := by
    have h := mul_le_mul_of_nonneg_left hα1 hκ
    nlinarith
  have hp := (mul_le_mul_of_nonneg_left hI hκ).trans hpredict
  have hj := mul_le_mul_of_nonneg_left hJ hρ
  have hc : 0 ≤ κ * α - κ * α / 4 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hmass hc
  have he := mul_le_mul_of_nonneg_left hsmall hκ
  have he' := mul_le_mul_of_nonneg_right hρκ hv
  have hmain := mul_nonneg hκα hq₀
  nlinarith

variable {Ω Γ O : Type*} [Fintype Ω] [Fintype Γ] [Fintype O]

theorem of_observed_variation
    (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (observe : Ω → O) (referenceObserve : Γ → O)
    (I J : O → Bool) (prediction : Ω → Bool)
    (κ α q₀ v : ℝ) (hκ : 0 ≤ κ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hq₀ : 0 ≤ q₀) (hv : 0 ≤ v) (hsmall : v ≤ α * q₀ / 16)
    (hvariation : (μ.pushforward observe).totalVariation
      (ν.pushforward referenceObserve) ≤ v)
    (hmass : q₀ ≤ ν.probability (fun x => J (referenceObserve x)))
    (hdensity : α * ν.probability (fun x => J (referenceObserve x)) ≤
      ν.probability (fun x => I (referenceObserve x)))
    (hpredict : κ * μ.probability (fun x => I (observe x)) ≤ μ.probability prediction) :
    κ * α * q₀ / 4 ≤ μ.probability prediction -
      (κ * α / 4) * μ.probability (fun x => J (observe x)) := by
  have hi := (μ.pushforward observe).probability_abs_sub_le_totalVariation
    (ν.pushforward referenceObserve) I
  have hj := (μ.pushforward observe).probability_abs_sub_le_totalVariation
    (ν.pushforward referenceObserve) J
  rw [FiniteDistribution.probability_pushforward,
    FiniteDistribution.probability_pushforward] at hi hj
  have hi' := (abs_le.mp (hi.trans hvariation)).1
  have hj' := (abs_le.mp (hj.trans hvariation)).2
  apply scalar_bound κ α q₀ v (ν.probability (fun x => J (referenceObserve x)))
    (μ.probability (fun x => I (observe x)))
    (μ.probability (fun x => J (observe x))) (μ.probability prediction)
    hκ hα hα1 hq₀ hv hsmall hmass
  · linarith
  · linarith
  · exact hpredict

variable {P A : Type*} [Fintype P] [Fintype A]

theorem of_original_usefulness
    (μ : FiniteDistribution Ω) (advice : FiniteDistribution A)
    (reference : FiniteDistribution Γ) (p : Ω → P)
    (referenceObserve : Γ → P × A) (L : Ω → Bool)
    (I J : P × A → Bool) (prediction : Ω × A → Bool)
    (κ α q₀ v : ℝ) (hκ : 0 ≤ κ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hq₀ : 0 ≤ q₀) (hv : 0 ≤ v) (hsmall : v ≤ α * q₀ / 16)
    (hmarked : ∀ z a, I (z, a) = true → UsefulMark.useful μ p L κ z = true)
    (hprediction : ∀ x a, L x = true → I (p x, a) = true →
      prediction (x, a) = true)
    (hvariation : ((μ.product advice).pushforward (fun x => (p x.1, x.2))).totalVariation
      (reference.pushforward referenceObserve) ≤ v)
    (hmass : q₀ ≤ reference.probability (fun x => J (referenceObserve x)))
    (hdensity : α * reference.probability (fun x => J (referenceObserve x)) ≤
      reference.probability (fun x => I (referenceObserve x))) :
    κ * α * q₀ / 4 ≤ (μ.product advice).probability prediction -
      (κ * α / 4) * (μ.product advice).probability (fun x => J (p x.1, x.2)) := by
  apply of_observed_variation (μ.product advice) reference (fun x => (p x.1, x.2))
    referenceObserve I J prediction κ α q₀ v hκ hα hα1 hq₀ hv hsmall
    hvariation hmass hdensity
  exact UsefulAdvice.independent_advice_predicts μ advice p L κ I prediction hmarked hprediction

end
end PerfectCompleteness.PredictionDifference

end OAI
