import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.Expression

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.SeedCompiler
open OracleCompiler OracleCompiler.Expression

lemma terminalMean_equivariant {d : ℕ} (r σ : ℝ) (Δ : Point d) :
    (terminalMean d r σ).Equivariant
      (moveSeed (fun x => x+r • Δ) (terminalShift 1) Δ) id := by
  apply Program.oneQuery_equivariant
  · intro z
    exact terminalQuery_invariant _ _ _ _
  · intro z a
    simp [moveSeed,shiftSlots,terminalShift]

lemma terminalSample_equivariant {d : ℕ} (r η : ℝ) (Δ : Point d) :
    (terminalSample d r η).Equivariant
      (moveSeed (fun x => x+r • Δ) (terminalShift 2) Δ) (fun y => y-Δ) := by
  apply Program.oneQuery_equivariant
  · intro z
    exact terminalQuery_invariant _ _ _ _
  · intro z a
    simp [moveSeed,shiftSlots,terminalShift]
    module

lemma terminalSample_reserved {d : ℕ} (r η : ℝ) (Δ : Point d) :
    (terminalSample d r η).Equivariant
      (moveSeed id (fun i => if i=2 then 1 else 0) Δ) (fun y => y+(η/2) • Δ) := by
  apply Program.oneQuery_equivariant
  · intro z
    simp [moveSeed,shiftSlots]
  · intro z a
    simp [moveSeed,shiftSlots,smul_add]
    abel

end LogConcaveSampling.SeedCompiler

end

end

end

end OAI
