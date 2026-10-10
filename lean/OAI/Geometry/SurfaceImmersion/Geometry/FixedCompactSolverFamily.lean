import OAI.Geometry.SurfaceImmersion.Atlas.FixedChartNonlinearSolver
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseMarginCompact
import OAI.Geometry.SurfaceImmersion.Atlas.FastPhaseBounds
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialInputNorm
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseSupportCoordinates

namespace OAI

/-! A fixed noncritical phase cover supplies actual polynomially controlled
solvers for every smaller good target support. The cover and split constants
are selected before the immersion, scales, and target. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

theorem fixed_compact_polynomial_solver_family
    {φ : JetPolynomial.Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (K₀ : Compacts SmallModes.Base)
    (hnoncritical : ∀ x ∈ (K₀ : Set SmallModes.Base),
      phaseDerivative (coordinatePhase φ) x ≠ 0) :
    ∃ (t : Finset K₀) (J S : ℕ → ℝ) (p : ℕ → ℕ) (A : ℕ → ℝ),
      (∀ m, 1 ≤ J m) ∧ (∀ m, 1 ≤ S m) ∧ (∀ m, 1 ≤ A m) ∧
      ∀ {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
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
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
      ∀ B : ℕ → ℝ, (∀ m, 1 ≤ B m) →
      (∀ m j, j ≤ m+3 → WeightedBound univ 1 j
        (B m/(s : ℝ)^(j-2)) (G ∘ planeCoordinateIsometry.symm)) →
      ∃ (L : t → Compacts JetPolynomial.Base)
        (T : (i : t) → SupportedField (F := ComplexTensor) K →ₗ[ℝ]
          SupportedField (F := ComplexTensor) (modeSupport (L i)))
        (c : (i : t) → PolynomialSolveData emptyMetricPolynomial 0 G hG φ (L i) τ s),
        (∀ i, (modeSupport (L i) : Set SmallModes.Base) ⊆ K) ∧
        (∀ i m, (c i).C m = A m*(fixedChartSolverBudget J B D m)^(p m)) ∧
        (∀ i m, (c i).D m = 0) ∧
        (∀ i m, (c i).J m = fixedChartSolverBudget J B D m) ∧
        (∀ i m j, j ≤ m → ∀ x ∈ (c i).e.target,
          ‖iteratedFDerivWithin ℝ j (c i).e.symm (c i).e.target x‖ ≤ J m) ∧
        (∀ m i f, supportedWeightedSeminorm (modeSupport (L i)) s m (T i f) ≤
          S m * supportedWeightedSeminorm K s m f) ∧
        (∀ f x, ∑ i, T i f x = f x) := by
  classical
  have hφ' := hφ.comp planeCoordinateIsometry.symm.contDiff
  obtain ⟨t,e,J,hcover,hJ,hf,hi⟩ := noncritical_phase_cover_budgets hφ' K₀ hnoncritical
  obtain ⟨P⟩ := PhasePartitions.exists_compact_phase_partition K₀.isCompact
    (fun i : t => (e i).chart.source) (fun i => (e i).chart.open_source) hcover
  obtain ⟨p,A,hA,hsolver⟩ := fixed_chart_nonlinear_solver
  refine ⟨t,J,P.splitConstant,p,A,hJ,P.one_le_splitConstant,hA,?_⟩
  intro G hG K hK D hD hImm hgood hgram hnormal τ s hs hs1 B hB hFj
  let Q : PhasePartitions.CompactPhasePartition t (K : Set SmallModes.Base)
      (fun i => (e i).chart.source) := P.restrictTarget K hK
  let L : t → Compacts JetPolynomial.Base := fun i => jetSupport (Q.pieceSupport i)
  let T : (i : t) → SupportedField (F := ComplexTensor) K →ₗ[ℝ]
      SupportedField (F := ComplexTensor) (modeSupport (L i)) :=
    fun i => (onModeSupportLM (Q.pieceSupport i)).comp (Q.splitSupportedLM i)
  have hLK (i : t) : (modeSupport (L i) : Set SmallModes.Base) ⊆ K := by
    simpa only [L,modeSupport_jetSupport] using Q.pieceSupport_subset_original i
  have hLe (i : t) : (modeSupport (L i) : Set SmallModes.Base) ⊆ (e i).chart.source := by
    simpa only [L,modeSupport_jetSupport] using Q.pieceSupport_subset_domain i
  have hc (i : t) := hsolver hG (L i) hφ (e i) (hLe i) J hJ (hf i) (hi i) D hD
    (fun x hx => hImm x (hLK i hx)) (fun x hx => hgood x (hLK i hx))
    (fun x hx => hgram x (hLK i hx)) (fun x hx => hnormal x (hLK i hx))
    τ s hs hs1 B hB (fun m j hj => (hFj m j hj).restrict_open_domain
      isOpen_univ (e i).chart.open_source (subset_univ _))
  choose c hC hzero hCJ hInv using hc
  refine ⟨L,T,c,hLK,hC,hzero,hCJ,hInv,?_,?_⟩
  · intro m i f
    change supportedWeightedSeminorm (modeSupport (jetSupport (Q.pieceSupport i))) s m
      (onModeSupport (Q.pieceSupport i) (Q.splitSupported f i)) ≤ _
    rw [onModeSupport_seminorm _ s hs]
    exact Q.splitSupported_uniform_bound m i s hs hs1 f
  · intro f x
    exact Q.sum_splitSupported_apply f x

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
