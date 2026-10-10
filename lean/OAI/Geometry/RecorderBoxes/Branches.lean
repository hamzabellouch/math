import Mathlib
import OAI.Geometry.RecorderBoxes.Boxes
import OAI.Computability.SolenoidalRecorder.Rules

namespace OAI

/-! Finite recorder branches and disjoint source and target rectangles. -/

namespace Solenoidal
namespace Bridge
@[ext] structure Branch (M : Machine) where
  src : Recorder.Control M
  read : Recorder.Letter M
  left : Recorder.Letter M
  dst : Recorder.Control M
  written : Recorder.Letter M
  move : Move
  allowed : Recorder.Rule M src read dst written move

variable {M : Machine}

 
theorem branch_source_key {i j : Branch M} (hs : i.src = j.src)
    (ha : i.read = j.read) (hl : i.left = j.left) : i = j := by
  have hh := Recorder.rule_deterministic i.allowed j.allowed hs ha
  exact Branch.ext hs ha hl hh.1 hh.2.1 hh.2.2

 
theorem branch_target_key {i j : Branch M} (hs : i.dst = j.dst)
    (hb : i.written = j.written) (hl : i.left = j.left) : i = j := by
  have hj : Recorder.Rule M j.src j.read i.dst i.written j.move := by
    simpa only [hs, hb] using j.allowed
  have hh := Recorder.local_predecessor_unique i.allowed hj
  exact Branch.ext hh.1 hh.2.1 hl hs hb hh.2.2

 
instance : Finite (Branch M) := by
  let key : Branch M → Recorder.Control M × Recorder.Letter M × Recorder.Letter M :=
    fun i => (i.src, i.read, i.left)
  apply Finite.of_injective key
  intro i j h
  exact branch_source_key (congrArg Prod.fst h)
    (congrArg (fun x => x.2.1) h) (congrArg (fun x => x.2.2) h)

 
noncomputable def branchSource {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1))
    (i : Branch M) : Rectangle := sourceBox (e i.read) (e i.left)

noncomputable def branchTarget {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1))
    (i : Branch M) : Rectangle := targetBox (e i.written) (e i.left) i.move

theorem branch_source_gap {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1))
    {i j : Branch M} (hij : i ≠ j) (hs : i.src = j.src) :
    (branchSource e i).SeparatedBy (1 / Radix.base m) (branchSource e j) := by
  apply normalized_source_gap
  intro he
  exact hij (branch_source_key hs (e.injective (congrArg Prod.fst he))
    (e.injective (congrArg Prod.snd he)))

theorem branch_target_gap {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1))
    {i j : Branch M} (hij : i ≠ j) (hs : i.dst = j.dst) :
    (branchTarget e i).SeparatedBy (1 / Radix.base m ^ 2) (branchTarget e j) := by
  have hd : i.move = j.move := (Recorder.fixed_incoming i.allowed).trans
    ((congrArg (Recorder.incoming M) hs).trans (Recorder.fixed_incoming j.allowed).symm)
  dsimp only [branchTarget]
  rw [hd]
  apply normalized_target_gap
  intro he
  exact hij (branch_target_key hs (e.injective (congrArg Prod.fst he))
    (e.injective (congrArg Prod.snd he)))
end Bridge
end Solenoidal

end OAI
