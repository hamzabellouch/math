import OAI.Geometry.SurfaceImmersion.Atlas.IndependentUniformPhase
import OAI.Geometry.SurfaceImmersion.Primitive.UniformPhasePrimitive
import OAI.Geometry.SurfaceImmersion.Geometry.ExactGeometricFastFamily
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasMetricJetMargins
import OAI.Geometry.SurfaceImmersion.Correction.UniformPrimitiveMeanRealization
import OAI.Geometry.SurfaceImmersion.Geometry.SupportedPatchGeometry
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasPhaseNormalMargin
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseAnsatzNormal
import OAI.Geometry.SurfaceImmersion.Primitive.NonlinearPrimitiveExpansion
import OAI.Geometry.SurfaceImmersion.Primitive.NonlinearJetProfiles
import OAI.Geometry.SurfaceImmersion.Geometry.NonlinearLowJetNeighborhood
import OAI.Geometry.SurfaceImmersion.Primitive.AtlasPrimitiveExpansion
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasLowJetNeighborhood
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMeanApproximation
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveShiftedPowers
import OAI.Geometry.SurfaceImmersion.Primitive.UniformPrimitiveNormal
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveWeightedBudget
import OAI.Geometry.SurfaceImmersion.Primitive.SupportedPrimitiveGeometry
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveAtlasNormalMargin
import OAI.Geometry.SurfaceImmersion.Primitive.AtlasPrimitiveNormal

namespace OAI

/-! Construct the actual globally supported primitive from the finite recursion
and its extended polynomial mean operator. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector WeightedEstimates
local instance independentExactPhaseFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance independentExactPhaseFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance independentExactPhaseDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance independentExactPhaseDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance independentExactPhaseSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance independentExactPhaseSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace MetricGoodPhaseData
open PrimitiveRealization
variable {g : SmoothMetric M} {F : M → Space}

theorem independent_exact_phase_primitive_metric [T2Space M] (data : MetricGoodPhaseData g F) (A₀ : SmoothingAtlas M)
    (houter : ∀ i x, x ∈ tsupport (A₀.weight i) → A₀.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (hF : ContMDiff planeModel spaceModel ∞ F) (hmetric : g.inner = inducedTensor F)
    (i : A₀.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ e.source)
    (hcover : (A₀.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source)
    {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)
    {a : JetPolynomial.Base → ℝ} (ha : ContDiff ℝ ∞ a) (hamp : l.HasSpatialAmplitude a)
    (S : TopologicalSpace.Opens JetPolynomial.Base)
    (hSc : IsCompact (closure (S : Set JetPolynomial.Base))) (hTS : MapsTo e e.source S)
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (hFQ : MapsTo (lowJet (A₀.jetChartMap i F ∘ e.symm)) S Q)
    (K : Set JetPolynomial.Base) (hK : IsCompact K) (hKS : K ⊆ S)
    (hKA : e.symm '' K ⊆ (A₀.chartWeightCompact i : Set JetPolynomial.Base))
    (hone : ∀ x ∈ e.symm '' K, χ x = 1)
    (hv : ∀ J ∈ O, lowJetPosition J ∉ K → ∀ t, l.velocity (J,t) = SurfaceVelocityFamily.normal J)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0)

    (h : SmoothMetric M)
    (htarget : h.inner = g.inner + A₀.bundleRestore A₀.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![a q^2,0,0]) y))) :
    ∃ G : M → Space, IsSmoothIsometricImmersion M h G ∧ Nonempty (MetricGoodPhaseData h G) := by
  obtain ⟨ρ,R₁,c₁,hρ,hR₁,hc₁,hjet⟩ := data.A.metric_firstJet_margin h
  obtain ⟨c,c₂,V₀,hc,hc₂,hV₀,hfamilies⟩ := data.independent_uniform_phase_primitive_realization
    A₀ houter hF hmetric i e he hi hχ hχc hχs hcover l ha hamp S hSc hTS
    hQ hQO hFQ K hK hKS hKA hone hv ℓ hℓx hℓy
  obtain ⟨D₀,hD₀,hd₀⟩ := A₀.weightedBound_change_atlas (V := Space) data.A 0
  obtain ⟨Dw,hDw,hdw⟩ := A₀.weightedBound_change_atlas (V := Space) data.A 442
  obtain ⟨Ds,hDs,hds⟩ := A₀.shiftedBound_change_atlas (V := Space) data.A 2 440
  obtain ⟨Dt,hDt,hdt⟩ := A₀.tensorWeightedBound_change_atlas data.A 440
  apply data.A.exact_geometric_metric_from_fast_family h data.outer_locally_one R₁ c₁ c₂
    (D₀*V₀) hc₁ hc₂ (mul_nonneg hD₀ hV₀)
  intro N
  obtain ⟨b,u,η,L,C,Cv,P,hb,hb16,hu,hη,hη1,hL,hC,hCv,hP,hfamily⟩ := hfamilies 442 (N+1)
  obtain ⟨η₀,hη₀,_,hsmall⟩ := ExactCorrection.positive_power_threshold (Dt*C) (N+1) ρ
    (by positivity) hρ
  refine ⟨min η η₀,Dt*C,(Dw+Ds)*Cv,lt_min hη hη₀,
    mul_nonneg hDt hC,mul_nonneg (add_nonneg hDw hDs) hCv,?_⟩
  intro z hz hzη
  have hzη' : z < η := hzη.trans_le (min_le_left _ _)
  have hz1 := hzη'.le.trans hη1
  obtain ⟨G,V,hG,hV,hclose,hslow,hweighted,hzero,hshift,herror,hI,hB,hBmargin,hN,hext⟩ :=
    hfamily z hz hzη'
  have herr₀ : A₀.TensorWeightedBound 1 440 (C*z^(N+1)) (inducedTensor V-h.inner) := by
    rw [htarget]
    exact fun j => (herror j).mono_order (by omega)
  have herr : data.A.TensorWeightedBound 1 440 ((Dt*C)*z^(N+1)) (inducedTensor V-h.inner) := by
    have hh := hdt _ 1 (C*z^(N+1)) zero_lt_one le_rfl (by positivity)
      ((A₀.inducedTensor_smooth hV).sub_section h.contMDiff) herr₀
    simpa only [mul_assoc] using hh
  have hexp : (N : ℝ)+1 = ((N+1 : ℕ) : ℝ) := by norm_num
  have hjet' := hjet V hV ((Dt*C)*z^(N+1)) (by positivity)
    (by simpa only [hexp,Real.rpow_natCast] using hsmall z hz (hzη.trans_le (min_le_right _ _)))
    (fun j => (herr j).mono_order (Nat.zero_le 440))
  have hzeroA := hd₀ V 1 V₀ zero_lt_one le_rfl hV₀ hV hzero
  have hwA : data.A.WeightedBound z 442 ((Dw+Ds)*Cv) V := by
    have hh := hdw V z Cv hz hz1 hCv hV hweighted
    exact fun j => (hh j).mono_const (by nlinarith)
  have hsA : data.A.ShiftedBound 2 440 z (((Dw+Ds)*Cv)/z^2) V := by
    have hh := hds V z (Cv/z^2) hz hz1 (by positivity) hV
      (fun j k hk x => hshift j k (by omega) x)
    intro j k hk x
    apply (hh j k hk x).trans
    have heq : Ds*(Cv/z^2) = (Ds*Cv)/z^2 := by ring
    rw [heq]
    exact div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg z)
  refine ⟨V,hV,hzeroA,hwA,hsA,herr,?_⟩
  intro j x hx
  exact ⟨(hjet' j x hx).1,(hjet' j x hx).2,(hBmargin j x hx).le⟩

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
