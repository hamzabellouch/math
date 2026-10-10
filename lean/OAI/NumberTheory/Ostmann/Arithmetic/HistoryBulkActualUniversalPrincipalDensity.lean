import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationRootTestDensity

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal
open Construction Conclusion HistoryBulkFibreGiantApproximation
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
    {C : InitialSourceChoice d Bs BD Bz k L E}

def assignmentDensity (x : SourceAssignment C.sources
    (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) (mixed : Bool) : ℝ :=
  if mixed then (Frame.extractedDensity (C:=C) x).re else 1

theorem assignmentDensity_mem (x : SourceAssignment C.sources
    (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) (mixed : Bool) :
    0 ≤ assignmentDensity x mixed ∧ assignmentDensity x mixed ≤ 1 := by
  have hn : 0 ≤ assignmentDensity x mixed := by
    cases mixed
    · exact zero_le_one
    · simp only [assignmentDensity,ite_true,Frame.extractedDensity,Complex.ofReal_re]
      positivity
  refine ⟨hn,?_⟩
  cases mixed
  · exact le_rfl
  · have h := Frame.norm_extractedDensity_le (C:=C) x
    change (Frame.extractedDensity (C:=C) x).re ≤ 1
    exact (Complex.re_le_norm _).trans h

@[simp] theorem assignmentDensity_cast (x : SourceAssignment C.sources
    (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) (mixed : Bool) :
    (assignmentDensity x mixed : ℂ) =
      if mixed then Frame.extractedDensity (C:=C) x else 1 := by
  cases mixed <;> simp only [assignmentDensity,Bool.false_eq_true,ite_false,ite_true,
    Frame.extractedDensity,Complex.ofReal_re,Complex.ofReal_one]

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
