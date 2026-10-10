import OAI.Geometry.SurfaceImmersion.Atlas.CompactPhaseSolverFamily
import OAI.Geometry.SurfaceImmersion.Geometry.FiniteSplitCancellation

namespace OAI

/-! Uniform cancellation on compact good-phase supports with no assumed phase solver. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

/-- A compact good phase gives a uniform finite-loss cancellation estimate.
The geometry and constants are chosen before the target and both scales. -/
theorem uniform_compact_good_phase_cancellation
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    {φ : JetPolynomial.Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (K : Compacts SmallModes.Base)
    (hImm : ∀ p ∈ (K : Set SmallModes.Base),
      Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) p))
    (hgood : ∀ p ∈ (K : Set SmallModes.Base),
      Good (RealModes.realSecondTensor (G ∘ planeCoordinateIsometry.symm) p)
        (phaseDerivative (coordinatePhase φ) p)) (q : ℕ) :
    ∃ C D : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧ (∀ m, 0 ≤ D m) ∧
      ∀ (A : SupportedField (F := ComplexTensor) K) (τ : ℝ) (s : ℝ≥0),
        0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      ∃ X : RealModes.RField 4, ContDiff ℝ ∞ X ∧ tsupport X ⊆ K ∧
        (∀ m, WeightedBound univ τ m (C m * supportedWeightedSeminorm K s
          (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) A) X) ∧
        (∀ m, WeightedBound univ τ m ((τ/s)^(q+1) * D m * supportedWeightedSeminorm K s
          (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) A)
          (RealModes.realLinearizedTensor (G ∘ planeCoordinateIsometry.symm) X +
            QuadraticMean.displacement τ (coordinatePhase φ) A)) := by
  obtain ⟨t,L,T,c,I,S,hLK,_,hI,hi,hS,hT,hsum⟩ := compact_phase_solver_family hG hφ K hImm hgood
  exact finite_split_cancellation emptyMetricPolynomial hG φ K L T c hLK I hI hi S hS hT hsum q

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
