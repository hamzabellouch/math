import OAI.MeasureTheory.Falconer.Estimates.WeightedDistanceSourceMapping
import OAI.MeasureTheory.Falconer.Estimates.ActualTwoPointDerivatives

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem inheritedCircleSymbol_zero_assignment (S : Finset PolicyDescriptor)
    (Q : DyadicSquare) (ρ : Measure Plane) (m : ℝ → ℝ) (N : ℕ)
    (lam sig : ℝ) (J i : ℕ) (x : Plane) (dir : UnitCircle) :
    inheritedCircleSymbol S id (fun _ => 0) Q ρ m N lam sig J i (fun _ => 1) x dir =
      (descriptorListMask Q ρ m N lam sig J i S x dir : ℂ) := by
  simp [inheritedCircleSymbol,inheritedMaskProduct,normalizedMaskFactor,
    descriptorAngleMask,descriptorListMask,sourceUnitDirection_sourceAngle]

namespace PositiveDistanceData

noncomputable def pairMaskSymbol (d : PositiveDistanceData) (z : Plane × Plane)
    (dir : UnitCircle) : ℂ :=
  (descriptorListMask d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i
    (policyDescriptorList (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t) z.1 dir : ℂ) *
  (descriptorListMask d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i
    (policyDescriptorList (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t) z.2 dir : ℂ)

theorem pairMaskSymbol_radial (d : PositiveDistanceData) (z : Plane × Plane) :
    d.pairMaskSymbol z (sourceRadialUnit z.2 z.1) = (d.minimalMask z : ℂ) := by
  simp only [pairMaskSymbol,minimalMask,Complex.ofReal_mul]

theorem pairMaskSymbol_inherited (d : PositiveDistanceData) (z : Plane × Plane) (dir : UnitCircle) :
    let S := policyDescriptorList (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t
    d.pairMaskSymbol z dir =
      inheritedCircleSymbol S id (fun _ => 0) d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i (fun _ => 1) z.1 dir *
      conj (inheritedCircleSymbol S id (fun _ => 0) d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i (fun _ => 1) z.2 dir) := by
  dsimp only
  rw [inheritedCircleSymbol_zero_assignment,inheritedCircleSymbol_zero_assignment]
  simp only [pairMaskSymbol,Complex.conj_ofReal]

end PositiveDistanceData

end PlanarFalconer

end OAI
