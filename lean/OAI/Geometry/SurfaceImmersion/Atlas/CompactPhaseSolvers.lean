import OAI.Geometry.SurfaceImmersion.Atlas.GoodPhaseTargetSplit
import OAI.Geometry.SurfaceImmersion.Atlas.GoodPhaseSolver
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseSupportCoordinates

namespace OAI

/-! Actual finite phase solvers for a compactly supported tensor target. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation PhaseMean

/-- Local good-phase geometry supplies all the solver data on a finite
support decomposition. There is no assumption of a chart on the entire support. -/
theorem compact_phase_solvers
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    {φ : JetPolynomial.Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (K : Compacts SmallModes.Base)
    (hImm : ∀ p ∈ (K : Set SmallModes.Base),
      Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) p))
    (hgood : ∀ p ∈ (K : Set SmallModes.Base),
      Good (RealModes.realSecondTensor (G ∘ planeCoordinateIsometry.symm) p)
        (phaseDerivative (coordinatePhase φ) p))
    (A : SupportedField (F := ComplexTensor) K) :
    ∃ (t : Finset K) (L : t → Compacts JetPolynomial.Base)
      (B : (i : t) → SupportedField (F := ComplexTensor) (modeSupport (L i)))
      (c : (i : t) → PolynomialSolveData emptyMetricPolynomial 0 G hG φ (L i) 1 1),
      (∀ i, (modeSupport (L i) : Set SmallModes.Base) ⊆ K) ∧
      (∀ i m, (c i).D m = 0) ∧ (∀ x, ∑ i, B i x = A x) := by
  classical
  obtain ⟨t,e,L,B,hLK,hLe,hsum⟩ := split_target_into_good_phase_charts
    (hG.comp planeCoordinateIsometry.symm.contDiff)
    (hφ.comp planeCoordinateIsometry.symm.contDiff) K hImm hgood A
  have hs (i : t) : (modeSupport (jetSupport (L i)) : Set SmallModes.Base) ⊆ (e i).chart.source := by
    simpa only [modeSupport_jetSupport] using hLe i
  choose c hc hD using fun i : t => (e i).exists_unperturbed_solver hG hφ (jetSupport (L i)) (hs i)
  refine ⟨t,fun i => jetSupport (L i),fun i => onModeSupport (L i) (B i),c,?_,hD,?_⟩
  · intro i
    simpa only [modeSupport_jetSupport] using hLK i
  · intro x
    exact hsum x

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
