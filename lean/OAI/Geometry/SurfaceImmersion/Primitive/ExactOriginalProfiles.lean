import OAI.Geometry.SurfaceImmersion.Primitive.ExactPrimitiveProfiles
import OAI.Geometry.SurfaceImmersion.Primitive.AtlasLeadingProfileStability
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
local instance exactOriginalProfilesFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance exactOriginalProfilesFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance exactOriginalProfilesDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance exactOriginalProfilesDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance exactOriginalProfilesSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance exactOriginalProfilesSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace MetricGoodPhaseData
variable {g : SmoothMetric M} {F : M → Space}

theorem exact_primitive_original_profiles [T2Space M] (data : MetricGoodPhaseData g F)
    (hF : ContMDiff planeModel spaceModel ∞ F) (hmetric : g.inner = inducedTensor F)
    (i : data.A.centers) {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)
    {a : JetPolynomial.Base → ℝ} (ha : ContDiff ℝ ∞ a) (hamp : l.HasSpatialAmplitude a)
    (S : TopologicalSpace.Opens JetPolynomial.Base)
    (T : TopologicalSpace.Compacts JetPolynomial.Base) (hST : (S : Set JetPolynomial.Base) ⊆ T)
    (houter : (chart (i : M)) '' tsupport (data.A.outer i) ⊆ S)
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (hFQ : MapsTo (lowJet (data.A.jetChartMap i F)) S Q)
    (K : Set JetPolynomial.Base) (hK : IsClosed K) (hKS : K ⊆ S)
    (hKA : K ⊆ (data.A.chartWeightCompact i : Set JetPolynomial.Base))
    (hv : ∀ J ∈ O, lowJetPosition J ∉ K → ∀ t, l.velocity (J,t) = SurfaceVelocityFamily.normal J)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0)
    {C : Set JetPolynomial.Base} (hC : IsCompact C) (hCS : C ⊆ S)
    :
    ∃ h : SmoothMetric M, h.inner = g.inner+data.A.primitiveTensor i a ∧
    ∀ ε : ℝ, 0 < ε → ∀ ζ : ℝ, 0 < ζ →
    ∃ z : ℝ, 0 < z ∧ z < ζ ∧ z ≤ 1 ∧ ∃ W : M → Space,
      IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      (∀ p ∈ C,
        ‖SurfaceVelocityFamily.Loop.primitiveJetProfile (data.A.vectorChartRead i W) z p-
          l.geometricLeadingProfile (data.A.jetChartMap i F) (data.A.jetChartMap_smooth i hF)
            (fun _ hp => hQO (hFQ hp)) p ((ℓ p/z : ℝ) : Period)‖ < ε) ∧
      ∃ G : M → Space, ∃ _hG : ContMDiff planeModel spaceModel ∞ G,
        data.A.WeightedBound 1 3 ε (G-F) ∧
        ∃ V : M → Space, ContMDiff planeModel spaceModel ∞ V ∧
          data.A.WeightedBound 1 2 (z^8) (W-V) ∧
          ∀ p ∉ tsupport (data.A.weight i), V =ᶠ[𝓝 p] G := by
  obtain ⟨h,hh,hall⟩ := data.exact_primitive_five_profiles hF hmetric i l ha hamp S T hST houter
    hQ hQO hFQ K hK hKS hKA hv ℓ hℓx hℓy
  refine ⟨h,hh,?_⟩
  intro ε hε ζ hζ
  obtain ⟨ρ,hρ,hstable⟩ := data.A.geometricLeadingProfile_stability i hF l
    (fun _ hp => hQO (hFQ hp)) hC hCS (ε/2) (half_pos hε)
  obtain ⟨z,hz,hzζ,hz1,W,hW,hgeometry,G,hG,hGO,hslow,hprofile,V,hV,hcorrection,hexterior⟩ :=
    hall (min (ε/2) ρ) (lt_min (half_pos hε) hρ) ζ hζ
  have hslowρ : data.A.WeightedBound 1 3 ρ (G-F) :=
    fun j => (hslow j).mono_const (min_le_right _ _)
  refine ⟨z,hz,hzζ,hz1,W,hW,hgeometry,?_,G,hG,?_,V,hV,hcorrection,hexterior⟩
  · intro p hp
    have hfirst :
        ‖SurfaceVelocityFamily.Loop.primitiveJetProfile (data.A.vectorChartRead i W) z p-
          l.geometricLeadingProfile (data.A.jetChartMap i G) (data.A.jetChartMap_smooth i hG)
            hGO p ((ℓ p/z : ℝ) : Period)‖ ≤ ε/2 :=
      (hprofile p (hCS hp)).trans (min_le_left _ _)
    have hsecond := hstable G hG hGO hslowρ p hp ((ℓ p/z : ℝ) : Period)
    have htriangle := dist_triangle
      (SurfaceVelocityFamily.Loop.primitiveJetProfile (data.A.vectorChartRead i W) z p)
      (l.geometricLeadingProfile (data.A.jetChartMap i G) (data.A.jetChartMap_smooth i hG)
        hGO p ((ℓ p/z : ℝ) : Period))
      (l.geometricLeadingProfile (data.A.jetChartMap i F) (data.A.jetChartMap_smooth i hF)
        (fun _ hp => hQO (hFQ hp)) p ((ℓ p/z : ℝ) : Period))
    simp only [dist_eq_norm] at htriangle
    linarith
  · exact fun j => (hslow j).mono_const ((min_le_left _ _).trans (by linarith))

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
