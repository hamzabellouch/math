import Mathlib
import OAI.Combinatorics.UniformKServer.Basic

namespace OAI

noncomputable section

namespace UniformKServer

def BitTape.cells (T : BitTape) : ℕ := T.left.length + 1 + T.right.length

namespace ClockSchedule

def capped (P : BitMachine) (input : List Bool) (B : ℕ) : MachineState P :=
  P.run (P.initial input) (List.replicate B false)

def budget (t : ℕ) : ℕ := Nat.log 2 (t+1)

def scheduled (P : BitMachine) (input : List Bool) (t : ℕ) : MachineState P :=
  capped P input (budget t)

theorem shift_cells (v : BitTape) (m : HeadMove) : (v.shift m).cells ≤ v.cells+1 := by
  cases v with
  | mk l h r =>
    cases m with
    | stay => simp [BitTape.shift,BitTape.cells]
    | left => cases l <;> simp [BitTape.shift,BitTape.cells] <;> omega
    | right => cases r <;> simp [BitTape.shift,BitTape.cells]; omega

theorem ofWord_cells (w : List Bool) : (BitTape.ofWord w).cells ≤ w.length+1 := by
  cases w <;> simp [BitTape.ofWord,BitTape.blank,BitTape.cells]; omega

theorem step_bounds (P : BitMachine) (s : MachineState P) (b : Bool) :
    (P.step s b).outputRev.length ≤ s.outputRev.length+1 ∧
    (P.step s b).input.cells ≤ s.input.cells+1 ∧
    ∀ i, ((P.step s b).work i).cells ≤ (s.work i).cells+1 := by
  cases hs : s.yielded with
  | true => simp [BitMachine.step,hs]
  | false =>
    simp only [BitMachine.step,hs,Bool.false_eq_true,↓reduceIte]
    refine ⟨?_, shift_cells _ _, ?_⟩
    · cases (P.transition s.control s.input.head (fun i => (s.work i).head) b).emit <;>
        simp
    · intro i
      exact shift_cells {s.work i with head :=
        (P.transition s.control s.input.head (fun i => (s.work i).head) b).write i} _

theorem run_cons (P : BitMachine) (s : MachineState P) (b : Bool) (bs : List Bool) :
    P.run s (b::bs) = P.run (P.step s b) bs := rfl

theorem run_bounds (P : BitMachine) (s : MachineState P) (bs : List Bool) :
    (P.run s bs).outputRev.length ≤ s.outputRev.length+bs.length ∧
    (P.run s bs).input.cells ≤ s.input.cells+bs.length ∧
    ∀ i, ((P.run s bs).work i).cells ≤ (s.work i).cells+bs.length := by
  induction bs generalizing s with
  | nil => simp [BitMachine.run]
  | cons b bs ih =>
    rw [run_cons]
    rcases ih (P.step s b) with ⟨ho,hi,hw⟩
    rcases step_bounds P s b with ⟨ho',hi',hw'⟩
    refine ⟨by simp only [List.length_cons]; omega,
      by simp only [List.length_cons]; omega, ?_⟩
    intro i
    have := hw i
    have := hw' i
    simp only [List.length_cons]
    omega

theorem run_append (P : BitMachine) (s : MachineState P) (bs cs : List Bool) :
    P.run s (bs++cs) = P.run (P.run s bs) cs := List.foldl_append

theorem run_halted (P : BitMachine) (s : MachineState P) (hs : s.yielded = true)
    (bs : List Bool) : P.run s bs = s := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa [run_cons,BitMachine.step,hs] using ih

theorem capped_eq_after (P : BitMachine) (input : List Bool) {T B : ℕ}
    (halted : (capped P input T).yielded = true) (hTB : T ≤ B) :
    capped P input B = capped P input T := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hTB
  simp only [capped,List.replicate_add,run_append]
  exact run_halted P (capped P input T) halted _

/-- A literal capped bit-machine simulation cannot write a compressed output
claiming more bits or touch more than linearly many cells. -/
theorem capped_bounds (P : BitMachine) (input : List Bool) (B : ℕ) :
    (capped P input B).outputRev.length ≤ B ∧
    (capped P input B).input.cells ≤ input.length + 1 + B ∧
    ∀ i, ((capped P input B).work i).cells ≤ 1+B := by
  rcases run_bounds P (P.initial input) (List.replicate B false) with ⟨ho,hi,hw⟩
  simp only [List.length_replicate,BitMachine.initial,List.length_nil,zero_add] at ho hi hw
  refine ⟨ho, ?_, hw⟩
  exact hi.trans (Nat.add_le_add_right (ofWord_cells input) B)

/-- The exact activation threshold and output/space bounds for the source
restart-from-scratch schedule. The premise is only termination of the
supplied literal constructor, not a complexity or competitive assumption. -/
theorem deterministic_activation (P : BitMachine) (input : List Bool)
    (halts : ∃ B, (capped P input B).yielded = true) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, 1 ≤ t →
      ((scheduled P input t).yielded = true ↔ 2^T-1 ≤ t) ∧
      (scheduled P input t).outputRev.length ≤ Nat.clog 2 (t+1) ∧
      (scheduled P input t).input.cells ≤ input.length+1+Nat.clog 2 (t+1) ∧
      (∀ i, ((scheduled P input t).work i).cells ≤ 1+Nat.clog 2 (t+1)) := by
  let T := Nat.find halts
  have hT : (capped P input T).yielded = true := Nat.find_spec halts
  have hTp : 1 ≤ T := by
    by_contra h
    have hz : T = 0 := by omega
    simp [hz,capped,BitMachine.run,BitMachine.initial] at hT
  have hsuccess : ∀ B, (capped P input B).yielded = true ↔ T ≤ B := by
    intro B
    constructor
    · exact Nat.find_min' halts
    · intro hTB
      rw [capped_eq_after P input hT hTB]
      exact hT
  refine ⟨T,hTp,?_⟩
  intro t ht
  have hg : budget t ≤ Nat.clog 2 (t+1) := Nat.log_le_clog _ _
  rcases capped_bounds P input (budget t) with ⟨ho,hi,hw⟩
  have he : (scheduled P input t).yielded = true ↔ 2^T-1 ≤ t := by
    change (capped P input (budget t)).yielded = true ↔ _
    rw [hsuccess]
    dsimp [budget]
    rw [Nat.le_log_iff_pow_le (by decide : 1<2) (by omega : t+1 ≠ 0)]
    have hp : 0 < 2^T := pow_pos (by decide) _
    omega
  refine ⟨he,ho.trans hg,hi.trans (Nat.add_le_add_left hg _),?_⟩
  intro i
  exact (hw i).trans (Nat.add_le_add_left hg 1)

end ClockSchedule
end UniformKServer

end

end OAI
