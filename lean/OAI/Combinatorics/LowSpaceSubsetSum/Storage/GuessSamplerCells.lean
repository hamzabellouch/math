import OAI.Combinatorics.LowSpaceSubsetSum.Storage.SamplerPiCells
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.GuessArrayExecution

namespace OAI

/-! # Three actual interval draws and their stored guess array -/

noncomputable section
namespace LowSpaceSubsetSum.GuessSamplerCells

def one (n : ℕ) (s : (CanonicalGuesses.coupling n).Seed) :
    SamplerExecution.Trace ↥(RepresentationSetup.guessRange n) × ℕ :=
  let r := SamplerFinCells.run n (CanonicalGuesses.width n) s
  (⟨r.1.value.map (CanonicalGuesses.encoding n), r.1.reads, r.1.tests⟩, r.2+8)

theorem one_value (n : ℕ) (s : (CanonicalGuesses.coupling n).Seed) :
    (one n s).1 = (CanonicalGuesses.execution n).run s := by
  have h := SamplerFinCells.run_value n (CanonicalGuesses.width n) s
  simp only [one, CanonicalGuesses.execution, SamplerExecution.map]
  rw [h]

theorem one_cells (n : ℕ) (s : (CanonicalGuesses.coupling n).Seed) :
    (one n s).2 ≤ 3*n^3+88 := by
  have h := SamplerFinCells.run_cells n (CanonicalGuesses.width n) s
  change _+8 ≤ _
  omega

def trace (n : ℕ) (s : (GuessArrayExecution.coupling n).Seed) :=
  SamplerPiCells.run 3 (fun _ => ↥(RepresentationSetup.guessRange n))
    (fun _ => CanonicalGuesses.coupling n) (fun _ => one n) (fun _ => 3*n^3+88) s

theorem trace_value (n : ℕ) (s : (GuessArrayExecution.coupling n).Seed) :
    (trace n s).1 = (GuessArrayExecution.execution n).run s :=
  SamplerPiCells.value 3 _ _ _ _ (fun _ => CanonicalGuesses.execution n) (fun _ => one_value n) s

theorem trace_cells (n : ℕ) (s : (GuessArrayExecution.coupling n).Seed) :
    (trace n s).2 ≤ 9*n^3+344 := by
  have h := SamplerPiCells.cells 3 (fun _ => ↥(RepresentationSetup.guessRange n))
    (fun _ => CanonicalGuesses.coupling n) (fun _ => one n) (fun _ => 3*n^3+88)
    (fun _ => one_cells n) s
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  dsimp only [trace]
  omega

def run (n : ℕ) (s : (GuessArrayExecution.coupling n).Seed) :
    (Option (Vector ℕ 3) × ℕ) × ℕ :=
  let r := trace n s
  ((r.1.value.map (fun g => Vector.ofFn (fun i => (g i).val)), r.1.reads+r.1.tests+7), r.2+16)

theorem run_value (n : ℕ) (s : (GuessArrayExecution.coupling n).Seed) :
    (run n s).1 = GuessArrayExecution.run n s := by
  simp only [run, trace_value, GuessArrayExecution.run]

theorem run_cells (n : ℕ) (s : (GuessArrayExecution.coupling n).Seed) :
    (run n s).2 ≤ 9*n^3+360 := by
  have h := trace_cells n s
  change _+16 ≤ _
  omega

end LowSpaceSubsetSum.GuessSamplerCells

end

end OAI
