import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Graphs.SuffixDescendants

namespace OAI

/-! Graph energies and pair estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open scoped ContDiff Classical Topology ComplexConjugate
variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin (n+1))
lemma assembly_pair_mass (ρ ν : Measure V) [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]
    (X Y : Set V) : ((ρ.restrict X).prod (ν.restrict Y)).real univ ≤ 1 := by
  rw [←Set.univ_prod_univ,measureReal_prod_prod]
  simpa only [Measure.restrict_apply_univ,measureReal_def,one_mul] using
    mul_le_mul (measureReal_le_one (μ:=ρ) (s:=X)) (measureReal_le_one (μ:=ν) (s:=Y))
      (measureReal_nonneg) (by norm_num : (0:ℝ)≤1)
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
