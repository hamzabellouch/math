import OAI.Geometry.SurfaceImmersion.Primitive.AtlasPrimitiveLocalErrorBound
import OAI.Geometry.SurfaceImmersion.Primitive.SupportedPrimitiveExpansion
import OAI.Geometry.SurfaceImmersion.Primitive.AtlasPrimitiveMapBound

namespace OAI

/-! Construct the actual globally supported primitive from the finite recursion
and its extended polynomial mean operator. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector WeightedEstimates
local instance primitiveExpansionFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance primitiveExpansionFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance primitiveExpansionDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance primitiveExpansionDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance primitiveExpansionSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance primitiveExpansionSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma euclidean_jetChartMap (i : A.centers) (G : M → Space) :
    (fun p => JetVelocityCoordinates.toEuclidean (A.jetChartMap i G p)) =
      A.vectorChartRead i G := by
  funext p
  exact spaceCoordinates.symm_apply_apply _

omit [CompactSpace M] in
lemma periodicAtlasRemainder_mean (i : A.centers) (G : M → Space)
    {S : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family S Space)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ)
    {n : ℕ} (P : Fin 3 → Fin n → Expression) (H : SmallModes.Base → PhaseMean.Tensor)
    (p : SmallModes.Base) :
    A.periodicAtlasRemainder i G U ℓ L z P H p =
      RealModes.realMetricTensor
        (spaceCoordinates ∘ finiteAnsatz (A.vectorChartRead i G) U ℓ L z ∘ planeCoordinateIsometry.symm) p-
      coordinateMetricMap P z (A.jetChartMap i G) p-H p := by
  unfold periodicAtlasRemainder coordinateMetricMap
  rw [A.jetChartMap_plane]
  simp only [Pi.sub_apply,Pi.add_apply]
  abel

/-- The extended mean is chosen once. Its actual periodic realization is
then available uniformly for all admissible nearby maps and small scales. -/
theorem supported_primitive_metric (i : A.centers)
    {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)
    {a : JetPolynomial.Base → ℝ} (ha : ContDiff ℝ ∞ a) (hamp : l.HasSpatialAmplitude a)
    (S : TopologicalSpace.Opens JetPolynomial.Base)
    (houter : (chart (i : M)) '' tsupport (A.outer i) ⊆ S)
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (n : ℕ) (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0) :
    ∃ P : Fin 3 → Fin n → Expression, (∀ k r, (P k r).SmoothCoeffs univ) ∧
    ∃ loss : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ Dv D : ℝ, 0 ≤ Dv ∧ 0 ≤ D ∧
      ∀ (G : M → Space) (hG : ContMDiff planeModel spaceModel ∞ G)
        (hGQ : MapsTo (lowJet (A.jetChartMap i G)) S Q),
      ∀ K : Set JetPolynomial.Base, IsClosed K → K ⊆ S →
      K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base) →
      (∀ p ∈ S, p ∉ K → ∀ t,
        l.velocity (lowJet (A.jetChartMap i G) p,t) = SurfaceVelocityFamily.normal (lowJet (A.jetChartMap i G) p)) →
      ∃ U : ℕ → Family S Space,
        (∀ j p, p ∉ K → (U j).val p = 0) ∧
        (∀ j, ContDiff ℝ ∞ (fun y : JetPolynomial.Base × ℝ => (U j).val y.1 (y.2 : Period))) ∧
        (∀ j, VectorExpression.Represents (A.jetChartMap i G) (l.coefficientExpressions n j) (U j)) ∧
        U 0 = (l.geometry (A.jetChartMap i G) (A.jetChartMap_smooth i hG)
          (fun _ hp => hQO (hGQ hp))).initial ∧
        (∀ z, ContMDiff planeModel spaceModel ∞ (A.periodicAtlasAnsatz i G U ℓ (n+1) z)) ∧
      ∀ (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
        WeightedEstimates.WeightedBound S s (m+(2*(n+1)+1)) B (lowJet (A.jetChartMap i G)) →
      A.WeightedBound z m (Dv*z/s^loss) (A.periodicAtlasAnsatz i G U ℓ (n+1) z-G) ∧
      ∀ (γ : ∀ x : M, CovariantTwoTensor x),
        ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
          (fun x => TotalSpace.mk' TensorFiber x (γ x)) →
      ∀ C : ℝ, A.TensorWeightedBound z m C
        (A.atlasPolynomialMetric (A.primitiveAtlasPolynomial i P) z G-γ) →
      A.TensorWeightedBound z m (C+D*z^(n+1)/s^loss)
        (inducedTensor (A.periodicAtlasAnsatz i G U ℓ (n+1) z)-
          (γ+A.bundleRestore A.tensorTriv i (fun y => fiberFromThree ![a y^2,0,0]))) := by
  obtain ⟨P,hP,_,_,hmean⟩ := l.meanTensorPolynomial_global_extension hQ hQO n
  obtain ⟨loss,hloss⟩ := l.supported_primitive_expansion (S := S) ha hamp hQ hQO n ℓ hℓx hℓy
  refine ⟨P,hP,loss,?_⟩
  intro m B hB
  obtain ⟨C₀,D₀,hC₀,hD₀,hconstruct⟩ := hloss m B hB
  obtain ⟨Dr,hDr,hr⟩ := A.periodicAtlasAnsatz_error_bound_on_outer i S.isOpen houter m
  obtain ⟨Dv,hDv,hvb⟩ := A.periodicAtlasAnsatz_increment_bound i m
  refine ⟨Dv*C₀,Dr*D₀,mul_nonneg hDv hC₀,mul_nonneg hDr hD₀,?_⟩
  intro G hG hGQ K hK hKS hKA hv
  have hGj := A.jetChartMap_smooth i hG
  obtain ⟨U,hU,hzero,hrep,hinit,hrem⟩ := hconstruct (A.jetChartMap i G) hGj hGQ K hK hKS hv
  refine ⟨U,hzero,hU,hrep,hinit,
    fun z => A.periodicAtlasAnsatz_smooth i hG U hK hKS hzero ℓ (n+1) z,?_⟩
  intro s z hz hzs hs1 hGb
  have hs : 0 < s := hz.trans_le hzs
  have hz1 : z ≤ 1 := hzs.trans hs1
  have hlocalIncrement : WeightedEstimates.WeightedBound S z m (C₀*z/s^loss)
      (finiteAnsatz (A.vectorChartRead i G) U ℓ (n+1) z-A.vectorChartRead i G) := by
    apply (hrem s z hz hzs hs1 hGb).1.congr
    intro p _
    simp only [JetVelocityCoordinates.toEuclidean,jetChartMap,Function.comp_apply,
      ContinuousLinearEquiv.symm_apply_apply,Pi.sub_apply]
  refine ⟨?_,?_⟩
  · have hv := hvb G hG S U K hK hKS hzero ℓ (n+1) z z (C₀*z/s^loss) hz hz1
      (div_nonneg (mul_nonneg hC₀ hz.le) (pow_nonneg hs.le _)) hlocalIncrement
    simpa only [mul_div_assoc,mul_assoc] using hv
  intro γ hγ C hsolved
  let H : SmallModes.Base → PhaseMean.Tensor := fun x => ![a (planeCoordinateIsometry.symm x)^2,0,0]
  have hH : ContDiff ℝ ∞ H := by
    apply contDiff_pi.mpr
    intro k
    fin_cases k
    · exact (ha.comp planeCoordinateIsometry.symm.contDiff).pow 2
    · exact contDiff_const
    · exact contDiff_const
  have hR := A.periodicAtlasRemainder_smooth i hG U hK hKS hzero ℓ (n+1) z hP hH
  have hlocal : WeightedEstimates.WeightedBound S z m (D₀*z^(n+1)/s^loss)
      (A.periodicAtlasRemainder i G U ℓ (n+1) z P H ∘ planeCoordinateIsometry) := by
    apply (hrem s z hz hzs hs1 hGb).2.congr
    intro p hp
    rw [Function.comp_apply,A.periodicAtlasRemainder_mean,
      hmean _ hGj z p (hGQ hp),← A.euclidean_jetChartMap i G]
    simp only [H,planeCoordinateIsometry.symm_apply_apply]
  have htransport := weightedBound_comp_isometry_on planeCoordinateIsometry.symm S.isOpen
    (hR.comp planeCoordinateIsometry.contDiff) hlocal
  have heq : (A.periodicAtlasRemainder i G U ℓ (n+1) z P H ∘ planeCoordinateIsometry) ∘
      planeCoordinateIsometry.symm = A.periodicAtlasRemainder i G U ℓ (n+1) z P H := by
    funext p
    simp
  change WeightedEstimates.WeightedBound (planeCoordinateIsometry.symm ⁻¹' (S : Set JetPolynomial.Base))
    z m (D₀*z^(n+1)/s^loss) ((A.periodicAtlasRemainder i G U ℓ (n+1) z P H ∘
      planeCoordinateIsometry) ∘ planeCoordinateIsometry.symm) at htransport
  rw [heq] at htransport
  have hb := hr G hG S U K hK hKS hKA hzero ℓ (n+1) z n P hP γ hγ H hH
    z C (D₀*z^(n+1)/s^loss) hz hz1
    (div_nonneg (mul_nonneg hD₀ (pow_nonneg hz.le _)) (pow_nonneg hs.le _)) hsolved htransport
  simpa only [H,planeCoordinateIsometry.symm_apply_apply,mul_div_assoc,mul_assoc] using hb

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
