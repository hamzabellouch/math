import OAI.Geometry.SurfaceImmersion.Atlas.NonlinearAtlasErrorBound
import OAI.Geometry.SurfaceImmersion.Atlas.NonlinearAtlasMapBound
import OAI.Geometry.SurfaceImmersion.Primitive.SupportedPrimitiveExpansion
import OAI.Geometry.SurfaceImmersion.Geometry.SingleTensorRestoreBound
import OAI.Geometry.SurfaceImmersion.Primitive.AtlasPrimitiveErrorBound
import OAI.Geometry.SurfaceImmersion.Atlas.SupportedPhaseMetric
import OAI.Geometry.SurfaceImmersion.Atlas.NonlinearAtlasAnsatz
import OAI.Geometry.SurfaceImmersion.Geometry.LocalSingleTensorRestoreBound
import OAI.Geometry.SurfaceImmersion.Correction.AtlasPrimitivePolynomial

namespace OAI

/-! Exact decomposition of a global primitive's metric defect into the
solved polynomial mean error and the finite periodic remainder. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector
local instance phaseExpansionFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance phaseExpansionFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance phaseExpansionDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance phaseExpansionDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance phaseExpansionSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance phaseExpansionSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- The actual finite velocity recursion in a nonlinear phase chart,
with the pulled-back polynomial mean and global supported error estimates. -/
theorem supported_phase_primitive_metric (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ e.source)
    {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)
    {a : JetPolynomial.Base → ℝ} (ha : ContDiff ℝ ∞ a) (hamp : l.HasSpatialAmplitude a)
    (S : TopologicalSpace.Opens JetPolynomial.Base) (hTS : MapsTo e e.source S)
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (n : ℕ) (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0) :
    ∃ P : Fin 3 → Fin n → Expression, (∀ k r, (P k r).SmoothCoeffs univ) ∧
    ∃ loss : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ Dv D : ℝ, 0 ≤ Dv ∧ 0 ≤ D ∧
      ∀ (G : M → Space) (hG : ContMDiff planeModel spaceModel ∞ G)
        (hGQ : MapsTo (lowJet (A.jetChartMap i G ∘ e.symm)) S Q),
      ∀ K : Set JetPolynomial.Base, IsCompact K → K ⊆ S →
      e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base) →
      (∀ x ∈ e.symm '' K, χ x = 1) →
      (∀ p ∈ S, p ∉ K → ∀ t,
        l.velocity (lowJet (A.jetChartMap i G ∘ e.symm) p,t) =
          SurfaceVelocityFamily.normal (lowJet (A.jetChartMap i G ∘ e.symm) p)) →
      ∃ U : ℕ → Family S Space,
        (∀ j p, p ∉ K → (U j).val p = 0) ∧
        (∀ j, ContDiff ℝ ∞ (fun y : JetPolynomial.Base × ℝ => (U j).val y.1 (y.2 : Period))) ∧
        (∀ j, VectorExpression.Represents (A.jetChartMap i G ∘ e.symm) (l.coefficientExpressions n j) (U j)) ∧
        U 0 = (l.geometry (A.jetChartMap i G ∘ e.symm) ((A.jetChartMap_smooth i hG).comp hi)
          (fun _ hp => hQO (hGQ hp))).initial ∧
        (∀ z, ContMDiff planeModel spaceModel ∞ (A.phaseAtlasAnsatz i G e χ U ℓ (n+1) z)) ∧
      ∀ (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
        WeightedEstimates.WeightedBound S s (m+(2*(n+1)+1)) B (lowJet (A.jetChartMap i G ∘ e.symm)) →
        A.WeightedBound z m (Dv*z/s^loss) (A.phaseAtlasAnsatz i G e χ U ℓ (n+1) z-G) ∧
        ∀ (γ : ∀ x : M, CovariantTwoTensor x),
          ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
            (fun x => TotalSpace.mk' TensorFiber x (γ x)) →
        ∀ C : ℝ, A.TensorWeightedBound z m C
          (A.atlasPolynomialMetric (A.primitiveAtlasPolynomial i
            (cutoffTensorPolynomial χ (tensorPolynomialCoordinatePullback P e e.symm))) z G-γ) →
        A.TensorWeightedBound z m (C+D*z^(n+1)/s^loss)
          (inducedTensor (A.phaseAtlasAnsatz i G e χ U ℓ (n+1) z)-
            (γ+A.bundleRestore A.tensorTriv i (fun y => fiberFromThree
              (localizedTensorPullback e χ (fun q => ![a q^2,0,0]) y)))) := by
  obtain ⟨P,hP,_,_,hmean⟩ := l.meanTensorPolynomial_global_extension hQ hQO n
  obtain ⟨loss,hloss⟩ := l.supported_primitive_expansion (S := S) ha hamp hQ hQO n ℓ hℓx hℓy
  refine ⟨P,hP,loss,?_⟩
  intro m B hB
  obtain ⟨C₀,D₀,hC₀,hD₀,hconstruct⟩ := hloss m B hB
  obtain ⟨Dr,hDr,hr⟩ := A.phaseAtlasAnsatz_error_bound i e he hi hχ hχc hχs S.isOpen hTS m
  obtain ⟨Dv,hDv,hvb⟩ := A.phaseAtlasAnsatz_increment_bound i e he hi hχ hχc m
  refine ⟨Dv*C₀,Dr*D₀,mul_nonneg hDv hC₀,mul_nonneg hDr hD₀,?_⟩
  intro G hG hGQ K hK hKS hKA hone hv
  have hGj := (A.jetChartMap_smooth i hG).comp hi
  obtain ⟨U,hU,hzero,hrep,hinit,hrem⟩ := hconstruct (A.jetChartMap i G ∘ e.symm) hGj hGQ
    K hK.isClosed hKS hv
  have heuc : (fun q => JetVelocityCoordinates.toEuclidean ((A.jetChartMap i G ∘ e.symm) q)) =
      A.vectorChartRead i G ∘ e.symm := by
    funext q
    exact spaceCoordinates.symm_apply_apply _
  rw [heuc] at hrem
  refine ⟨U,hzero,hU,hrep,hinit,
    fun z => A.phaseAtlasAnsatz_smooth i hG e he hi hχ U hK.isClosed hKS hzero ℓ (n+1) z,?_⟩
  intro s z hz hzs hs1 hGb
  have hs : 0 < s := hz.trans_le hzs
  have hz1 : z ≤ 1 := hzs.trans hs1
  have hlocalIncrement := (hrem s z hz hzs hs1 hGb).1
  refine ⟨?_,?_⟩
  · have hh := hvb G hG S U K hK.isClosed hKS hzero ℓ (n+1) z z (C₀*z/s^loss)
      hz hz1 (by positivity) hlocalIncrement
    simpa only [mul_div_assoc,mul_assoc] using hh
  intro γ hγ C hsolved
  let B₀ : JetPolynomial.Base → PhaseMean.Tensor := fun q => ![a q^2,0,0]
  have hB₀ : ContDiff ℝ ∞ B₀ := by
    apply contDiff_pi.mpr
    intro k
    fin_cases k
    · exact ha.pow 2
    · exact contDiff_const
    · exact contDiff_const
  have hlocal : WeightedEstimates.WeightedBound S z m (D₀*z^(n+1)/s^loss)
      (A.phaseAtlasRemainder i G e U ℓ (n+1) z P B₀) := by
    apply (hrem s z hz hzs hs1 hGb).2.congr
    intro p hp
    dsimp only [phaseAtlasRemainder,B₀]
    rw [hmean _ hGj z p (hGQ hp)]
  have hh := hr G hG S U K hK hKS hKA hzero hone ℓ (n+1) z n P hP γ hγ B₀ hB₀
    z C (D₀*z^(n+1)/s^loss) hz hz1 (by positivity) hsolved hlocal
  simpa only [B₀,mul_div_assoc,mul_assoc] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
