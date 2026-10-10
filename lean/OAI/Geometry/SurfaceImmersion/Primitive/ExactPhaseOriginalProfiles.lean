import OAI.Geometry.SurfaceImmersion.Primitive.ExactPhasePrimitiveProfiles
import OAI.Geometry.SurfaceImmersion.Primitive.PhaseLeadingProfileStability
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveProfileStability
import OAI.Geometry.SurfaceImmersion.Geometry.ExactGeometricFastFamily
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveMetric
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasMetricJetMargins

namespace OAI

/-! Actual finite-accuracy primitive immersions with a Riemannian target,
uniform first-jet bounds, and a uniform nonzero second-form margin. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes CovarianceCorrector
local instance exactPhaseOriginalProfilesFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance exactPhaseOriginalProfilesFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance exactPhaseOriginalProfilesDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance exactPhaseOriginalProfilesDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance exactPhaseOriginalProfilesSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance exactPhaseOriginalProfilesSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace MetricGoodPhaseData
variable {g : SmoothMetric M} {F : M → Space}

theorem exact_phase_primitive_original_profiles [T2Space M] (data : MetricGoodPhaseData g F)
    (hF : ContMDiff planeModel spaceModel ∞ F) (hmetric : g.inner = inducedTensor F)
    (i : data.A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ e.source)
    (hcover : (data.A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source)
    {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)
    {a : JetPolynomial.Base → ℝ} (ha : ContDiff ℝ ∞ a) (hamp : l.HasSpatialAmplitude a)
    (S : TopologicalSpace.Opens JetPolynomial.Base)
    (hSc : IsCompact (closure (S : Set JetPolynomial.Base))) (hTS : MapsTo e e.source S)
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (hFQ : MapsTo (lowJet (data.A.jetChartMap i F ∘ e.symm)) S Q)
    (K : Set JetPolynomial.Base) (hK : IsCompact K) (hKS : K ⊆ S)
    (hKA : e.symm '' K ⊆ (data.A.chartWeightCompact i : Set JetPolynomial.Base))
    (hone : ∀ x ∈ e.symm '' K, χ x = 1)
    (hv : ∀ J ∈ O, lowJetPosition J ∉ K → ∀ t, l.velocity (J,t) = SurfaceVelocityFamily.normal J)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0)

    (h : SmoothMetric M)
    (htarget : h.inner = g.inner + data.A.bundleRestore data.A.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![a q^2,0,0]) y)))
    {C : Set JetPolynomial.Base} (hC : IsCompact C)
    (hCS : C ⊆ (S : Set JetPolynomial.Base) ∩ e.target) :
    ∀ ε : ℝ, 0 < ε → ∀ ζ : ℝ, 0 < ζ →
    ∃ z : ℝ, 0 < z ∧ z < ζ ∧ z ≤ 1 ∧ ∃ W : M → Space,
      IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      (∀ p ∈ C,
        ‖SurfaceVelocityFamily.Loop.primitiveJetProfile (data.A.vectorChartRead i W ∘ e.symm) z p-
          l.geometricLeadingProfile (data.A.jetChartMap i F ∘ e.symm) ((data.A.jetChartMap_smooth i hF).comp hi)
            (fun _ hp => hQO (hFQ hp)) p ((ℓ p/z : ℝ) : Period)‖ < ε) ∧
      ∃ G : M → Space, ∃ _hG : ContMDiff planeModel spaceModel ∞ G,
        data.A.WeightedBound 1 3 ε (G-F) ∧
        ∃ V : M → Space, ContMDiff planeModel spaceModel ∞ V ∧
          data.A.WeightedBound 1 2 (z^8) (W-V) ∧
          (∀ p ∉ tsupport (data.A.weight i), V =ᶠ[𝓝 p] G) ∧
        ∀ p ∉ data.A.phaseSurfaceSupport i e K, V =ᶠ[𝓝 p] G := by
  have hall := data.exact_phase_primitive_five_profiles hF hmetric i e he hi hχ hχc hχs hcover
    l ha hamp S hSc hTS hQ hQO hFQ K hK hKS hKA hone hv ℓ hℓx hℓy h htarget
  intro ε hε ζ hζ
  obtain ⟨ρ,hρ,hstable⟩ := data.A.phase_geometricLeadingProfile_stability i hF hi l hSc
    (fun _ hp => hQO (hFQ hp)) hC (fun _ hp => (hCS hp).1) (ε/2) (half_pos hε)
  obtain ⟨z,hz,hzζ,hz1,W,hW,hgeometry,G,hG,hGO,hslow,hprofile,V,hV,hcorrection,hexterior⟩ :=
    hall (min (ε/2) ρ) (lt_min (half_pos hε) hρ) ζ hζ
  have hslowρ : data.A.WeightedBound 1 3 ρ (G-F) :=
    fun j => (hslow j).mono_const (min_le_right _ _)
  refine ⟨z,hz,hzζ,hz1,W,hW,hgeometry,?_,G,hG,?_,V,hV,hcorrection,hexterior⟩
  · intro p hp
    have hfirst :
        ‖SurfaceVelocityFamily.Loop.primitiveJetProfile (data.A.vectorChartRead i W ∘ e.symm) z p-
          l.geometricLeadingProfile (data.A.jetChartMap i G ∘ e.symm) ((data.A.jetChartMap_smooth i hG).comp hi)
            hGO p ((ℓ p/z : ℝ) : Period)‖ ≤ ε/2 :=
      (hprofile p (hCS hp)).trans (min_le_left _ _)
    have hsecond := hstable G hG hGO hslowρ p hp ((ℓ p/z : ℝ) : Period)
    have htriangle := dist_triangle
      (SurfaceVelocityFamily.Loop.primitiveJetProfile (data.A.vectorChartRead i W ∘ e.symm) z p)
      (l.geometricLeadingProfile (data.A.jetChartMap i G ∘ e.symm) ((data.A.jetChartMap_smooth i hG).comp hi)
        hGO p ((ℓ p/z : ℝ) : Period))
      (l.geometricLeadingProfile (data.A.jetChartMap i F ∘ e.symm) ((data.A.jetChartMap_smooth i hF).comp hi)
        (fun _ hp => hQO (hFQ hp)) p ((ℓ p/z : ℝ) : Period))
    simp only [dist_eq_norm] at htriangle
    linarith
  · exact fun j => (hslow j).mono_const ((min_le_left _ _).trans (by linarith))

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
