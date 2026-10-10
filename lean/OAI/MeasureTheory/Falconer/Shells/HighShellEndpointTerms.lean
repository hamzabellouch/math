import OAI.MeasureTheory.Falconer.Shells.HighShellCoefficientBounds
import OAI.MeasureTheory.Falconer.Angular.InverseCircleArcLength
import OAI.MeasureTheory.Falconer.Fourier.GraphKernelBounds

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ComplexConjugate
namespace PositiveDistanceData

noncomputable def inverseDescriptorList (d : PositiveDistanceData) : Finset PolicyDescriptor :=
  policyDescriptorList (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t

noncomputable def inverseEndpointSymbol (d : PositiveDistanceData) (k : PairMaskIndex → ℕ)
    (l : Fin 2) : Plane → UnitCircle → ℂ :=
  inheritedCircleSymbol d.inverseDescriptorList id (fun b => k (b,l)) d.Q d.ρ d.mass
    d.N d.lam d.sig d.J d.i (fun _ => 1)

 theorem inverseEndpointSymbol_measurable (d : PositiveDistanceData) (k : PairMaskIndex → ℕ)
    (l : Fin 2) : Measurable (fun z : Plane × UnitCircle => d.inverseEndpointSymbol k l z.1 z.2) :=
  measurable_inheritedCircleSymbol _ _ _ _ _ _ _ _ _ _ _ _ measurable_const

 theorem inverseEndpointSymbol_norm (d : PositiveDistanceData) (hQ : 0 < d.Q.side) (j : ℕ)
    {b : ℂ × (PairMaskIndex → ℕ)} (hb : b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList))
    (l : Fin 2) (x : Plane) (dir : UnitCircle) :
    ‖d.inverseEndpointSymbol b.2 l x dir‖ ≤ symbolDerivativeConstant (2*j)^(2*j) := by
  exact inheritedCircleSymbol_norm_le _ _ _ _ hQ _ _ _ _ _ _ _ _ (2*j)
    (pair_assignment_endpoint_budget _ _ _ (inverseLeibnizTerms_budget j _ hb) l) x (by simp) dir

 theorem inverseCircleOperator_pair_terms (d : PositiveDistanceData) (hQ : 0 < d.Q.side)
    (z : Plane × Plane) (j : ℕ) (dir : UnitCircle) :
    inverseCircleOperator j (d.pairMaskSymbol z) dir =
      ((inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList)).map (fun b =>
        b.1 * ((assignmentScale d.inverseDescriptorList d.N d.sig b.2:ℂ) *
          (d.inverseEndpointSymbol b.2 0 z.1 dir * conj (d.inverseEndpointSymbol b.2 1 z.2 dir))))).sum := by
  have h := d.pairMaskSymbol_inverse_leibniz hQ z j (sourceAngle dir)
  simpa only [inverseCircleOperator, sourceUnitDirection_sourceAngle,
    inverseDescriptorList, inverseEndpointSymbol] using h

end PositiveDistanceData

end PlanarFalconer

end OAI
