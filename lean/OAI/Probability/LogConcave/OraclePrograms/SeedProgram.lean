import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.Program

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeasureTheory
open scoped Classical BigOperators

structure SeedProgram (d : ℕ) where
  slots : ℕ
  calls : ℕ
  program : Program (Point d × (Fin slots → Point d)) d calls (Point d)
  shift : Fin slots → ℝ

namespace SeedProgram
variable {d : ℕ}
def damping (M : SeedProgram d) (D : ℝ) :
    (Fin M.slots → Point d) → (Fin M.slots → Point d) :=
  SeedCompiler.slotTransform (SeedCompiler.sqrtCoefficient (fun i => M.shift i/(2*D)))
    (fun i => M.shift i/(2*D))
lemma measurable_damping (M : SeedProgram d) (D : ℝ) : Measurable (M.damping D) := by
  unfold damping SeedCompiler.slotTransform SeedCompiler.slotSum
  fun_prop
end SeedProgram
end LogConcaveSampling.OracleCompiler

end
end

end OAI
