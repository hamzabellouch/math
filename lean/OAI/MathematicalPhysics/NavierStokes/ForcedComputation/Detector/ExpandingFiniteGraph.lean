import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingRecorderRun
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingAddresses

namespace OAI

/-! A finite, decidable graph for one expanding-array stage. Its lookup
examines the guarded local table and bounded integer stacks only. The
injectivity theorem applies to every defined address, including addresses
outside the initialized computation. -/

namespace ForcedComputation.ExpandingDetector
open Recorder

def localDisplacement (m : Fin 3) : ℤ := (m.val : ℤ) - 1

theorem moveCode_localDisplacement (m : Fin 3) :
    moveCode (localDisplacement m) = m := by
  fin_cases m <;> decide

def BoundedIntegerStep (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M))
    (q : Control (State M) (Alphabet M)) (L R : ℕ)
    (q' : Control (State M) (Alphabet M)) (L' R' : ℕ) : Prop :=
  ∃ (a b : Recorder.Symbol (State M) (Alphabet M)) (m : Fin 3),
    evalLocal (finiteMachine M hM) q a = some (q', b, localDisplacement m) ∧
    symbolCode M blank a = R % alphabetBase M blank ∧
    Lattice.nextLeft (alphabetBase M blank) L (symbolCode M blank b) m = L' ∧
    Lattice.nextRight (alphabetBase M blank) L R (symbolCode M blank b) m = R'

instance (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M))
    (q : Control (State M) (Alphabet M)) (L R : ℕ)
    (q' : Control (State M) (Alphabet M)) (L' R' : ℕ) :
    Decidable (BoundedIntegerStep M hM blank q L R q' L' R') :=
by
  let P (a b : Recorder.Symbol (State M) (Alphabet M)) (m : Fin 3) : Prop :=
    evalLocal (finiteMachine M hM) q a = some (q', b, localDisplacement m) ∧
    symbolCode M blank a = R % alphabetBase M blank ∧
    Lattice.nextLeft (alphabetBase M blank) L (symbolCode M blank b) m = L' ∧
    Lattice.nextRight (alphabetBase M blank) L R (symbolCode M blank b) m = R'
  letI (a b : Recorder.Symbol (State M) (Alphabet M)) (m : Fin 3) : Decidable (P a b m) := by
    dsimp only [P]
    infer_instance
  letI (a b : Recorder.Symbol (State M) (Alphabet M)) : Decidable (∃ m, P a b m) :=
    Fintype.decidableExistsFintype
  letI (a : Recorder.Symbol (State M) (Alphabet M)) : Decidable (∃ b m, P a b m) :=
    Fintype.decidableExistsFintype
  exact Fintype.decidableExistsFintype

theorem boundedIntegerStep_iff (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M))
    (q : Control (State M) (Alphabet M)) (L R : ℕ)
    (q' : Control (State M) (Alphabet M)) (L' R' : ℕ) :
    BoundedIntegerStep M hM blank q L R q' L' R' ↔
      IntegerStep M hM blank q L R q' L' R' := by
  constructor
  · rintro ⟨a, b, m, he, ha, hL, hR⟩
    refine ⟨a, b, localDisplacement m, evalLocal_sound he, ha, ?_, ?_⟩
    · simpa only [moveCode_localDisplacement] using hL
    · simpa only [moveCode_localDisplacement] using hR
  · rintro ⟨a, b, d, hs, ha, hL, hR⟩
    have hd := hs.displacement_bounds
    let m : Fin 3 := ⟨(d + 1).toNat, by omega⟩
    have hm : localDisplacement m = d := by dsimp [localDisplacement, m]; omega
    have hc : moveCode d = m := by rw [← hm, moveCode_localDisplacement]
    exact ⟨a, b, m, by simpa only [hm] using hs.eval, ha, by simpa only [hc] using hL,
      by simpa only [hc] using hR⟩

@[ext] structure RecorderAddress (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ) where
  control : Control (State M) (Alphabet M)
  left : Fin (alphabetBase M blank ^ d)
  right : Fin (alphabetBase M blank ^ d)
  deriving DecidableEq, Fintype

def RecorderAddress.toAddress {M : Alternating.Machine}
    {blank : Recorder.Symbol (State M) (Alphabet M)} {d : ℕ}
    (a : RecorderAddress M blank d) :
    Address (allControls M).length (alphabetBase M blank ^ d) :=
  ⟨⟨controlCode M a.control, controlCode_lt M a.control⟩, a.left, a.right⟩

def RecorderAddress.number {M : Alternating.Machine}
    {blank : Recorder.Symbol (State M) (Alphabet M)} {d : ℕ}
    (a : RecorderAddress M blank d) : ℕ := a.toAddress.index

theorem RecorderAddress.number_bounds {M : Alternating.Machine}
    {blank : Recorder.Symbol (State M) (Alphabet M)} {d : ℕ}
    (a : RecorderAddress M blank d) :
    0 < a.number ∧ a.number ≤ (allControls M).length * (alphabetBase M blank ^ d) ^ 2 :=
  ⟨a.toAddress.index_positive, a.toAddress.index_le⟩

theorem RecorderAddress.number_injective (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ) :
    Function.Injective (@RecorderAddress.number M blank d) := by
  intro a b hab
  have h := Address.index_injective _ _ hab
  apply RecorderAddress.ext
  · exact controlCode_injective M (congrArg (fun c => c.state.val) h)
  · exact congrArg Address.left h
  · exact congrArg Address.right h

def stageEdge (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ)
    (a : RecorderAddress M blank d) (b : RecorderAddress M blank (d + 1)) : Prop :=
  BoundedIntegerStep M hM blank a.control a.left a.right b.control b.left b.right

instance (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ)
    (a : RecorderAddress M blank d) (b : RecorderAddress M blank (d + 1)) :
    Decidable (stageEdge M hM blank d a b) := inferInstanceAs
      (Decidable (BoundedIntegerStep M hM blank a.control a.left a.right
        b.control b.left b.right))

theorem stageEdge_integer (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ)
    {a : RecorderAddress M blank d} {b : RecorderAddress M blank (d + 1)}
    (h : stageEdge M hM blank d a b) :
    IntegerStep M hM blank a.control a.left a.right b.control b.left b.right :=
  (boundedIntegerStep_iff M hM blank _ _ _ _ _ _).mp h

theorem stageEdge_source_unique (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ)
    {a c : RecorderAddress M blank d} {b : RecorderAddress M blank (d + 1)}
    (ha : stageEdge M hM blank d a b) (hc : stageEdge M hM blank d c b) : a = c := by
  obtain ⟨hq, hL, hR⟩ := IntegerStep.predecessor_unique M hM blank
    (stageEdge_integer M hM blank d ha) (stageEdge_integer M hM blank d hc)
  exact RecorderAddress.ext hq (Fin.ext hL) (Fin.ext hR)

theorem stageEdge_target_unique (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ)
    {a : RecorderAddress M blank d} {b c : RecorderAddress M blank (d + 1)}
    (hb : stageEdge M hM blank d a b) (hc : stageEdge M hM blank d a c) : b = c := by
  obtain ⟨hq, hL, hR⟩ := IntegerStep.successor_unique M hM blank
    (stageEdge_integer M hM blank d hb) (stageEdge_integer M hM blank d hc)
  exact RecorderAddress.ext hq (Fin.ext hL) (Fin.ext hR)

def recorderAddresses (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ) :
    List (RecorderAddress M blank d) :=
  (allControls M).flatMap fun q => (List.finRange (alphabetBase M blank ^ d)).flatMap
    fun L => (List.finRange (alphabetBase M blank ^ d)).map fun R => ⟨q, L, R⟩

theorem mem_recorderAddresses (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ)
    (a : RecorderAddress M blank d) : a ∈ recorderAddresses M blank d := by
  rcases a with ⟨q, L, R⟩
  simp only [recorderAddresses, List.mem_flatMap, List.mem_map]
  exact ⟨q, mem_allControls M q, L, by simp, R, by simp, rfl⟩

def lookupTarget (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ)
    (a : RecorderAddress M blank d) : Option (RecorderAddress M blank (d + 1)) :=
  (recorderAddresses M blank (d + 1)).find? (fun b => decide (stageEdge M hM blank d a b))

theorem lookupTarget_eq_some_iff (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ)
    (a : RecorderAddress M blank d) (b : RecorderAddress M blank (d + 1)) :
    lookupTarget M hM blank d a = some b ↔ stageEdge M hM blank d a b := by
  constructor
  · intro h
    exact of_decide_eq_true (List.find?_some (p := fun b => decide (stageEdge M hM blank d a b)) h)
  · intro hb
    cases he : lookupTarget M hM blank d a with
    | none =>
      have hnone := List.find?_eq_none.mp he b (mem_recorderAddresses M blank (d + 1) b)
      exact False.elim (hnone (by simpa only [decide_eq_true_eq] using hb))
    | some c =>
      have hc : stageEdge M hM blank d a c :=
        of_decide_eq_true (List.find?_some (p := fun b => decide (stageEdge M hM blank d a b)) he)
      have hcb := stageEdge_target_unique M hM blank d hc hb
      simp only [hcb]

theorem lookupTarget_injective (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ)
    {a c : RecorderAddress M blank d} {b : RecorderAddress M blank (d + 1)}
    (ha : lookupTarget M hM blank d a = some b)
    (hc : lookupTarget M hM blank d c = some b) : a = c :=
  stageEdge_source_unique M hM blank d
    ((lookupTarget_eq_some_iff M hM blank d a b).mp ha)
    ((lookupTarget_eq_some_iff M hM blank d c b).mp hc)

end ForcedComputation.ExpandingDetector

end OAI
