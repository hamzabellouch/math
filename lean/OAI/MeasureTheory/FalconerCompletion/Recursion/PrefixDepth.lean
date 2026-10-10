import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.InteriorPolicy
import OAI.MeasureTheory.Falconer.Recursion.Ledger
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphCapScaleInvCrude
import OAI.MeasureTheory.FalconerCompletion.Shells.TransportedAngularField

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory PlanarFalconer
open scoped ContDiff
variable {n : ℕ}
namespace PositiveDistanceState
variable (e : PositiveDistanceState (n+1))

noncomputable def sourcePrefixDepth : ℕ :=
  policyDepth (adjustedProfile (d:=n+1) e.mass e.N) e.N e.q e.a e.t

noncomputable def prefixPhasedLeft (z : PrefixAssignment n)
    (ξ : EuclideanSpace ℝ (Fin (n+1))) (x w : EuclideanSpace ℝ (Fin (n+1))) : ℂ :=
  Attempt4PrefixShell.SpatialFourierND.spatialFourierPhase (n+1) ((2:ℝ)^e.a)⁻¹ ξ x * e.prefixInverseLeft z x w
noncomputable def prefixPhasedRight (z : PrefixAssignment n)
    (ξ : EuclideanSpace ℝ (Fin (n+1))) (x w : EuclideanSpace ℝ (Fin (n+1))) : ℂ :=
  Attempt4PrefixShell.SpatialFourierND.spatialFourierPhase (n+1) ((2:ℝ)^e.a)⁻¹ ξ x * e.prefixInverseRight z x w

noncomputable def prefixGraphChildMax (v : ℝ) (Ψ : ℝ → ℝ)
    (z : PrefixAssignment n) (ξ : EuclideanSpace ℝ (Fin (n+1))) : ℝ :=
  _root_.OAI.CurrentFalconer.TreeND.graphSourceChildMax e.ρ e.ρ e.a e.sourcePrefixDepth v e.X e.Y
    (((2:ℝ)^e.N)^(-e.mass e.sourcePrefixDepth))
    (((2:ℝ)^e.N)^(-e.mass e.sourcePrefixDepth)) Ψ
    (e.prefixPhasedLeft z ξ) (e.prefixPhasedRight z ξ)

noncomputable def prefixGraphFactor : ℝ :=
  let A := adjustedProfile (d:=n+1) e.mass e.N
  ((2:ℝ)^e.N)^(-2*(A e.sourcePrefixDepth-A e.a)+height A e.a e.sourcePrefixDepth+
    (e.C+36*(n+1:ℝ)+5)*e.sig)
end PositiveDistanceState
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
