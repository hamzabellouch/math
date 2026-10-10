import OAI.Geometry.SurfaceImmersion.Atlas.CompactPhaseSolvers
import OAI.Geometry.SurfaceImmersion.Geometry.SplitSupportedBounds
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialInputNorm

namespace OAI

/-! The compact phase cover, target split and solver constants precede the target. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

theorem compact_phase_solver_family
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    {φ : JetPolynomial.Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (K : Compacts SmallModes.Base)
    (hImm : ∀ p ∈ (K : Set SmallModes.Base),
      Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) p))
    (hgood : ∀ p ∈ (K : Set SmallModes.Base),
      Good (RealModes.realSecondTensor (G ∘ planeCoordinateIsometry.symm) p)
        (phaseDerivative (coordinatePhase φ) p)) :
    ∃ (t : Finset K) (L : t → Compacts JetPolynomial.Base)
      (T : (i : t) → SupportedField (F := ComplexTensor) K →ₗ[ℝ]
        SupportedField (F := ComplexTensor) (modeSupport (L i)))
      (c : (i : t) → PolynomialSolveData emptyMetricPolynomial 0 G hG φ (L i) 1 1)
      (I : t → ℕ → ℝ) (S : ℕ → ℝ),
      (∀ i, (modeSupport (L i) : Set SmallModes.Base) ⊆ K) ∧
      (∀ i m, (c i).D m = 0) ∧ (∀ i m, 1 ≤ I i m) ∧
      (∀ i m j, 1 ≤ j → j ≤ m → ∀ x ∈ (c i).e.target,
        ‖iteratedFDerivWithin ℝ j (c i).e.symm (c i).e.target x‖ ≤ I i m) ∧
      (∀ m, 1 ≤ S m) ∧
      (∀ (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 → ∀ m i A,
        supportedWeightedSeminorm (modeSupport (L i)) s m (T i A) ≤
          S m * supportedWeightedSeminorm K s m A) ∧
      (∀ A x, ∑ i, T i A x = A x) := by
  classical
  obtain ⟨t,e,hcover⟩ := finite_good_phase_cover
    (hG.comp planeCoordinateIsometry.symm.contDiff)
    (hφ.comp planeCoordinateIsometry.symm.contDiff) K hImm hgood
  obtain ⟨P⟩ := PhasePartitions.exists_compact_phase_partition K.isCompact
    (fun i : t => (e i).chart.source) (fun i => (e i).chart.open_source) hcover
  let L := fun i : t => jetSupport (P.pieceSupport i)
  let T : (i : t) → SupportedField (F := ComplexTensor) K →ₗ[ℝ]
      SupportedField (F := ComplexTensor) (modeSupport (L i)) :=
    fun i => (onModeSupportLM (P.pieceSupport i)).comp (P.splitSupportedLM i)
  have hs (i : t) : (modeSupport (L i) : Set SmallModes.Base) ⊆ (e i).chart.source := by
    simpa only [L,modeSupport_jetSupport] using P.pieceSupport_subset_domain i
  choose c hc hD using fun i : t => (e i).exists_unperturbed_solver hG hφ (L i) (hs i)
  choose I hI hi using fun (i : t) m => compact_local_weighted_bound (e i).chart.open_target
    isOpen_univ (e i).targetCompact.isCompact (e i).targetBound
    (subset_univ _) (e i).smoothInverse.contDiffOn m
  refine ⟨t,L,T,c,I,P.splitConstant,?_,hD,hI,?_,P.one_le_splitConstant,?_,?_⟩
  · intro i
    simpa only [L,modeSupport_jetSupport] using P.pieceSupport_subset_original i
  · intro i m j _ hj x hx
    rw [hc i] at hx ⊢
    simpa only [one_pow,one_mul] using hi i m 1 zero_le_one le_rfl j hj x hx
  · intro s hs hs1 m i A
    change supportedWeightedSeminorm (modeSupport (jetSupport (P.pieceSupport i))) s m
      (onModeSupport (P.pieceSupport i) (P.splitSupported A i)) ≤ _
    rw [onModeSupport_seminorm _ s hs]
    exact P.splitSupported_uniform_bound m i s hs hs1 A
  · intro A x
    exact P.sum_splitSupported_apply A x

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
