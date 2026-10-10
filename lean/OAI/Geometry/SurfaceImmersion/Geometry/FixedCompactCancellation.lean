import OAI.Geometry.SurfaceImmersion.Geometry.FixedCompactSolverFamily
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialSplitBudgets

namespace OAI

/-! Finite-loss cancellation on a fixed compact noncritical region, with
polynomial geometric factors and an actual, support-preserving solution. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

theorem fixed_compact_polynomial_cancellation
    {φ : JetPolynomial.Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (K₀ : Compacts SmallModes.Base)
    (hnoncritical : ∀ x ∈ (K₀ : Set SmallModes.Base),
      phaseDerivative (coordinatePhase φ) x ≠ 0) :
    ∃ (N : ℕ) (J S : ℕ → ℝ) (p : ℕ → ℕ) (A : ℕ → ℝ),
      (∀ m, 1 ≤ J m) ∧ (∀ m, 1 ≤ S m) ∧ (∀ m, 1 ≤ A m) ∧
      ∀ {G : JetPolynomial.Base → JetPolynomial.Space} (_hG : ContDiff ℝ ∞ G)
        (K : Compacts SmallModes.Base), (K : Set SmallModes.Base) ⊆ K₀ →
      ∀ D : ℝ, 1 ≤ D →
      (∀ x ∈ (K : Set SmallModes.Base),
        Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) x)) →
      (∀ x ∈ (K : Set SmallModes.Base),
        Good (RealModes.realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
          (phaseDerivative (coordinatePhase φ) x)) →
      (∀ x ∈ (K : Set SmallModes.Base),
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (G ∘ planeCoordinateIsometry.symm) x)
          (SmallModes.coordDeriv SmallModes.dy (G ∘ planeCoordinateIsometry.symm) x))⁻¹‖ ≤ D) →
      (∀ x ∈ (K : Set SmallModes.Base),
        ‖secondQuadratic (RealModes.realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
          (-(phaseDerivative (coordinatePhase φ) x).2,
            (phaseDerivative (coordinatePhase φ) x).1)‖⁻¹ ≤ D) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      ∀ B : ℕ → ℝ, (∀ m, 1 ≤ B m) →
      (∀ m j, j ≤ m+3 → WeightedBound univ 1 j
        (B m/(s : ℝ)^(j-2)) (G ∘ planeCoordinateIsometry.symm)) →
      ∀ q : ℕ, ∀ f : SupportedField (F := ComplexTensor) K,
      ∃ X : RealModes.RField 4, ContDiff ℝ ∞ X ∧ tsupport X ⊆ K ∧
        (∀ m, WeightedBound univ τ m
          ((N : ℝ)*splitSizeBudget q m
            (fun r => A r*(fixedChartSolverBudget J B D r)^(p r))
            (fixedChartSolverBudget J B D) J S * supportedWeightedSeminorm K s
              (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) f) X) ∧
        (∀ m, WeightedBound univ τ m
          ((τ/s)^(q+1)*(N : ℝ)*splitResidualBudget q m
            (fun r => A r*(fixedChartSolverBudget J B D r)^(p r))
            (fixedChartSolverBudget J B D) J S * supportedWeightedSeminorm K s
              (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) f)
          (RealModes.realLinearizedTensor (G ∘ planeCoordinateIsometry.symm) X +
            QuadraticMean.displacement τ (coordinatePhase φ) f)) := by
  obtain ⟨t,J,S,p,A,hJ,hS,hA,hfamily⟩ :=
    fixed_compact_polynomial_solver_family hφ K₀ hnoncritical
  refine ⟨Fintype.card t,J,S,p,A,hJ,hS,hA,?_⟩
  intro G hG K hK D hD hImm hgood hgram hnormal τ s hτ hs hτs hs1 B hB hFj q f
  obtain ⟨L,T,c,hLK,hC,hzero,hCJ,hi,hT,hsum⟩ :=
    hfamily hG K hK D hD hImm hgood hgram hnormal τ s hs hs1 B hB hFj
  exact explicit_finite_split_cancellation hG φ K L T c hτ hs hτs hs1 hLK
    (fun r => A r*(fixedChartSolverBudget J B D r)^(p r))
    (fixedChartSolverBudget J B D) J S hJ hS
    (fun i => ⟨funext (hC i),funext (hzero i),funext (hCJ i)⟩)
    (fun i m j _ hj => hi i m j hj) hT hsum q f

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
