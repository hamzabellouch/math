import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingGateExpressions
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingDrift
import Mathlib.Data.Finset.Sort

namespace OAI

/-! A terminating finite compiler for every prefix of the full address
array. It enumerates all guarded wires, independently of the chosen run. -/

namespace ForcedComputation.ExpandingDetector
open ShearFlows Recorder
open scoped BigOperators

private theorem list_sum_range_eq {A : Type*} [AddCommMonoid A] (f : ℕ → A) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]

def rationalRadius (σ D K : ℚ) (n : ℕ) : ℚ :=
  (1024 * 3000 * (1 + σ) * (4 * D) * (K * D + 2)) * (4 * D) ^ n

def rationalDuration (σ D K : ℚ) (n : ℕ) : ℚ :=
  16 * rationalRadius σ D K (n + 1) * (K * D ^ (n + 1) + 2)

def rationalStageStart (σ D K : ℚ) (n : ℕ) : ℚ :=
  2 + (List.range n).foldr (fun i q => rationalDuration σ D K i + q) 0

theorem rationalRadius_val (σ D K : ℚ) (n : ℕ) :
    (rationalRadius σ D K n : ℝ) = radius σ D K n := by
  simp [rationalRadius, radius, initialRadius, expansion]

theorem rationalDuration_val (σ D K : ℚ) (n : ℕ) :
    (rationalDuration σ D K n : ℝ) = duration σ D K n := by
  simp [rationalDuration, rationalRadius_val, duration]

theorem rationalStageStart_val (σ D K : ℚ) (n : ℕ) :
    (rationalStageStart σ D K n : ℝ) = stageStart σ D K n := by
  unfold rationalStageStart stageStart
  have he : (List.range n).foldr (fun i q => rationalDuration σ D K i + q) 0 =
      ((List.range n).map (rationalDuration σ D K)).sum := by
    induction List.range n with
    | nil => rfl
    | cons i l ih => simp only [List.foldr_cons, List.map_cons, List.sum_cons, ih]
  rw [he, list_sum_range_eq]
  simp only [Rat.cast_add, Rat.cast_ofNat, Rat.cast_sum, rationalDuration_val]

@[instance_reducible]
def stageWireOrder (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ) :
    LinearOrder (StageWire M hM blank d) :=
  LinearOrder.lift' (fun w => w.val.1.number) (by
    intro w z h
    apply StageWire.source_injective M hM blank d
    exact RecorderAddress.number_injective M blank d h)

def orderedStageWires (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ) : List (StageWire M hM blank d) :=
  letI := stageWireOrder M hM blank d
  Finset.univ.sort (· ≤ ·)

theorem sum_orderedStageWires {A : Type*} [AddCommMonoid A]
    (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ)
    (f : StageWire M hM blank d → A) :
    ((orderedStageWires M hM blank d).map f).sum = ∑ w, f w := by
  let := stageWireOrder M hM blank d
  change ((Finset.univ.sort (· ≤ ·)).map f).sum = _
  rw [← List.sum_toFinset f (Finset.sort_nodup _ _), Finset.sort_toFinset]

def stageCode (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    (σ D K : ℚ) (n : ℕ) : NonperiodicVector := fun j =>
  NonperiodicExpr.sum ((orderedStageWires M hM blank (m+n)).map
    (fun w => movingGateCode (rationalStageStart σ D K n) (rationalDuration σ D K n)
      (16 * rationalRadius σ D K n) (16 * rationalRadius σ D K (n + 1))
      (rationalRadius σ D K n) w.val.1.number w.val.2.number
      (haltingControl (finiteMachine M hM) w.val.2.control) j))

theorem stageCode_val (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    (σ D K : ℚ) (n : ℕ) (y : SpaceTime) :
    (stageCode M hM blank m σ D K n).val y =
      planeInclusion (stageDrift M hM blank m σ D K n y.1 (horizontalLinear y.2)) := by
  funext j
  simp only [NonperiodicVector.val, stageCode, NonperiodicExpr.sum_val,
    List.map_map, Function.comp_def, sum_orderedStageWires]
  change (∑ w : StageWire M hM blank (m+n),
    (movingGateCode _ _ _ _ _ w.val.1.number w.val.2.number
      (haltingControl (finiteMachine M hM) w.val.2.control)).val y j) = _
  simp only [movingGateCode_val, rationalStageStart_val, rationalDuration_val,
    Rat.cast_mul, Rat.cast_ofNat, rationalRadius_val]
  rw [← Finset.sum_apply, ← map_sum]
  rfl

def prefixCode (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    (σ D K : ℚ) (N : ℕ) : NonperiodicVector := fun j =>
  NonperiodicExpr.sum ((List.range N).map (fun n => stageCode M hM blank m σ D K n j))

theorem prefixCode_val (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    (σ D K : ℚ) (N : ℕ) (y : SpaceTime) :
    (prefixCode M hM blank m σ D K N).val y =
      planeInclusion (∑ n ∈ Finset.range N,
        stageDrift M hM blank m σ D K n y.1 (horizontalLinear y.2)) := by
  funext j
  simp only [NonperiodicVector.val, prefixCode, NonperiodicExpr.sum_val,
    List.map_map, Function.comp_def, list_sum_range_eq]
  change (∑ n ∈ Finset.range N, (stageCode M hM blank m σ D K n).val y j) = _
  simp only [stageCode_val]
  rw [← Finset.sum_apply, ← map_sum]

end ForcedComputation.ExpandingDetector

end OAI
