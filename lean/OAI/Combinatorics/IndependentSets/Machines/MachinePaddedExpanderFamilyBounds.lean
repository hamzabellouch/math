import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachinePaddedExpanderFamilyFrames

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachinePaddedExpanderFamilyBounds

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

def timeCoefficient : Nat :=
  MachineExpanderFamilyBounds.inputCoefficient + PCP.ExpanderFamily.growth + 29

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C timeCoefficient * Polynomial.X^5

theorem timePolynomial_encoding (k : Nat) :
    timePolynomial.eval (encodeWord k).length = timeCoefficient * (k + 1)^5 := by
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, encodeWord_length]

theorem ceilingCost_le (g k : Nat) :
    (MachineCeilingPower.timePolynomial g).eval (encodeWord k).length ≤
      (g + 29) * (k + 1)^5 := by
  rw [MachineCeilingPower.timePolynomial_encoding]
  have squareBound : (k + 1)^2 ≤ (k + 1)^5 :=
    Nat.pow_le_pow_right (Nat.succ_pos k) (by decide)
  have linearBound : k + 1 ≤ (k + 1)^5 := by
    simpa only [pow_one] using Nat.pow_le_pow_right
      (Nat.succ_pos k) (show 1 ≤ 5 by decide)
  have constantBound : 1 ≤ (k + 1)^5 := by omega
  have squareCost := Nat.mul_le_mul_left (g + 8) squareBound
  have linearCost := Nat.mul_le_mul_left 18 linearBound
  have constantCost := Nat.mul_le_mul_left 3 constantBound
  unfold MachineCeilingPower.timeBound
  nlinarith only [squareCost, linearCost, constantCost]

theorem combinedCost_le (k : Nat) :
    (MachineCeilingPower.timePolynomial PCP.ExpanderFamily.growth).eval
        (encodeWord k).length +
      MachineExpanderFamilyBounds.inputCoefficient * (k + 1)^5 ≤
        timePolynomial.eval (encodeWord k).length := by
  rw [timePolynomial_encoding]
  have h := ceilingCost_le PCP.ExpanderFamily.growth k
  unfold timeCoefficient
  nlinarith only [h]

theorem familyCost_le
    (H : Table (cloudSize PCP.Expanders.baseDegree) PCP.Expanders.baseDegree) (k : Nat) :
    (MachineCeilingPower.timePolynomial PCP.ExpanderFamily.growth).eval
        (encodeWord k).length +
      MachineExpanderFamilyBounds.familyBudget H (PCP.PreprocessingLevels.boundedLevel k) ≤
        timePolynomial.eval (encodeWord k).length := by
  exact (Nat.add_le_add_left
    (MachineExpanderFamilyBounds.familyBudget_at_boundedLevel_le H k) _).trans
      (combinedCost_le k)

def outputWord
    (H : Table (cloudSize PCP.Expanders.baseDegree) PCP.Expanders.baseDegree) (k : Nat) :
    List Bool :=
  encodeWords (rotationWords (family H (PCP.PreprocessingLevels.boundedLevel k)))

def outputCoefficient : Nat :=
  (PCP.ExpanderFamily.growth * degree PCP.Expanders.baseDegree + 1)^2

theorem outputWord_length_le
    (H : Table (cloudSize PCP.Expanders.baseDegree) PCP.Expanders.baseDegree) (k : Nat) :
    (outputWord H k).length ≤ outputCoefficient * (k + 1)^2 := by
  let q := degree PCP.Expanders.baseDegree
  let N := vertexCount q (PCP.PreprocessingLevels.boundedLevel k)
  have sizeBound : N ≤ PCP.ExpanderFamily.growth * (k + 1) := by
    change vertexCount (PCP.Expanders.baseDegree * PCP.Expanders.baseDegree)
      (PCP.PreprocessingLevels.boundedLevel k) ≤ _
    rw [PCP.PreprocessingLevels.table_vertexCount_eq_paddedSize]
    exact MachineExpanderFamilyBounds.paddedSize_le_succ_input k
  have rowBound := Nat.mul_le_mul_right q sizeBound
  have rowSuccBound : N * q + 1 ≤ (PCP.ExpanderFamily.growth * q + 1) * (k + 1) := by
    nlinarith only [rowBound, Nat.zero_le k]
  have lengthBound : (outputWord H k).length ≤ (N * q) * (N * q + 1) :=
    encode_rotationWords_length_le (family H (PCP.PreprocessingLevels.boundedLevel k))
  calc
    _ ≤ (N * q + 1)^2 := by nlinarith only [lengthBound, Nat.zero_le (N * q)]
    _ ≤ ((PCP.ExpanderFamily.growth * q + 1) * (k + 1))^2 :=
      Nat.pow_le_pow_left rowSuccBound 2
    _ = _ := by unfold outputCoefficient; dsimp [q]; ring

end IndependentSetsGames.Foundations.Complexity.MachinePaddedExpanderFamilyBounds

namespace IndependentSetsGames.Foundations.Complexity.MachinePaddedExpanderFamily

open Turing
open MachineCloudPadding
open MachineComposition

variable {ρ : Type} [Fintype ρ]

noncomputable def ceilingInTime (H : SmallTable) (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some main, initialState state register, initialTapes requested⟩
      (some ⟨some familyEntry, (state, (false, none)), handoffTapes requested⟩)
      ((MachineCeilingPower.timePolynomial PCP.ExpanderFamily.growth).eval
        (encodeWord requested).length) := by
  let original := MachineCeilingPower.paddingInTime requested state register
  let renamed := MachineStateEquiv.execution (ceilingStates ρ)
    (MachineCeilingPower.program PCP.ExpanderFamily.growth) original
  let placed := liftExecutionInTime (TM2.step (ceilingSource (ρ := ρ)))
    (TM2.step (program H))
    (Placement.configuration ceilingView ceilingLabel (some familyEntry) (fun _ => []))
    (Placement.step_simulation ceilingTape ceilingView ceilingView_left ceilingView_right
      ceilingLabel (some familyEntry) (fun _ => []) (ceilingSource (ρ := ρ))
      (program H) (program_ceiling H)) renamed
  have initialEq := ceiling_initial_configuration requested state register
  have finalEq := ceiling_handoff_configuration requested state
  unfold ceilingInput at initialEq
  unfold ceilingOutput at finalEq
  simpa only [initialEq, finalEq] using placed

noncomputable def materializeInTime (H : SmallTable) (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some familyEntry, (state, (false, none)), handoffTapes requested⟩
      (some ⟨none, finalState H state, finalTapes H requested⟩)
      (MachineExpanderFamilyBounds.inputCoefficient * (requested + 1)^5) := by
  let original := MachineExpanderFamily.paddedFamilyInTime H requested state []
  let boolean := MachineAlphabetTransport.executionInTime MachineExpanderFamily.alphabet_eq
    (MachineExpanderFamily.program MachineExpanderFamily.baseDegree_positive H
      MachineExpanderFamily.baseDegree_cloud_gt_one) original
  let framed := MachineStateFrame.frameExecution
    (MachineExpanderFamily.boolView MachineExpanderFamily.baseDegree_positive H
      MachineExpanderFamily.baseDegree_cloud_gt_one) (false, (none : Option Bool)) boolean
  let placed := liftExecutionInTime (TM2.step (familySource H)) (TM2.step (program H))
    (Placement.configuration familyView familyLabel none (retainedFrame requested))
    (Placement.step_simulation familyTape familyView familyView_left familyView_right
      familyLabel none (retainedFrame requested) (familySource H) (program H)
      (program_family H)) framed
  simpa only [family_initial_configuration, family_final_configuration] using placed

noncomputable def paddedInTime (H : SmallTable) (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some main, initialState state register, initialTapes requested⟩
      (some ⟨none, finalState H state, finalTapes H requested⟩)
      (MachinePaddedExpanderFamilyBounds.timePolynomial.eval (encodeWord requested).length) := by
  let first := ceilingInTime H requested state register
  let second := materializeInTime H requested state
  let all := StateTransition.EvalsToInTime.trans (TM2.step (program H))
    _ _ _ _ _ first second
  exact
    { toEvalsTo := all.toEvalsTo
      steps_le_m := all.steps_le_m.trans
        (by simpa only [Nat.add_comm] using
          MachinePaddedExpanderFamilyBounds.combinedCost_le requested) }

noncomputable def placedInTime {K Λ : Type} [DecidableEq K]
    (tape : Tape → K) (view : K → Option Tape)
    (left : ∀ t, view (tape t) = some t)
    (right : ∀ j t, view j = some t → tape t = j)
    (labels : Label → Λ) (exit : Option Λ) (extra : K → List Bool)
    (H : SmallTable) (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ))
    (code : ∀ l, target (labels l) = Placement.statement tape labels exit (program H l))
    (requested : Nat) (state : MachineExpanderFamily.State ρ fixedDegree)
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step target)
      (Placement.configuration view labels exit extra
        ⟨some main, initialState state register, initialTapes requested⟩)
      (some (Placement.configuration view labels exit extra
        ⟨none, finalState H state, finalTapes H requested⟩))
      (MachinePaddedExpanderFamilyBounds.timePolynomial.eval (encodeWord requested).length) :=
  liftExecutionInTime (TM2.step (program H)) (TM2.step target)
    (Placement.configuration view labels exit extra)
    (Placement.step_simulation tape view left right labels exit extra (program H) target code)
    (paddedInTime H requested state register)

end IndependentSetsGames.Foundations.Complexity.MachinePaddedExpanderFamily

end OAI
