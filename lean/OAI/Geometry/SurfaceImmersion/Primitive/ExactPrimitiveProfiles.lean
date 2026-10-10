import OAI.Geometry.SurfaceImmersion.Primitive.ExactProfiledPrimitive
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
local instance actualPrimitiveProfilesFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance actualPrimitiveProfilesFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance actualPrimitiveProfilesDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance actualPrimitiveProfilesDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance actualPrimitiveProfilesSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance actualPrimitiveProfilesSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace MetricGoodPhaseData
variable {g : SmoothMetric M} {F : M → Space}

theorem exact_primitive_five_profiles [T2Space M] (data : MetricGoodPhaseData g F)
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
    :
    ∃ h : SmoothMetric M, h.inner = g.inner+data.A.primitiveTensor i a ∧
    ∀ ε : ℝ, 0 < ε → ∀ ζ : ℝ, 0 < ζ →
    ∃ z : ℝ, 0 < z ∧ z < ζ ∧ z ≤ 1 ∧ ∃ W : M → Space,
      IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      ∃ G : M → Space, ∃ hG : ContMDiff planeModel spaceModel ∞ G,
      ∃ hGO : MapsTo (lowJet (data.A.jetChartMap i G)) S O,
      data.A.WeightedBound 1 3 ε (G-F) ∧
      (∀ p ∈ S,
        let geom := l.geometry (data.A.jetChartMap i G) (data.A.jetChartMap_smooth i hG) hGO
        let t : Period := ((ℓ p/z : ℝ) : Period)
        ‖SurfaceVelocityFamily.Loop.primitiveJetProfile (data.A.vectorChartRead i W) z p-
          ![geom.longitudinal.val p t,geom.Y p,geom.C p,
            (geom.longitudinal.slow (coordinateVector 1)).val p t,geom.V.angle.val p t]‖ ≤ ε) ∧
      ∃ V : M → Space, ContMDiff planeModel spaceModel ∞ V ∧
        data.A.WeightedBound 1 2 (z^8) (W-V) ∧
        ∀ p ∉ tsupport (data.A.weight i), V =ᶠ[𝓝 p] G := by
  obtain ⟨h,hh,hall⟩ := data.exact_profiled_primitive_metric hF hmetric i l ha hamp S T hST houter
    hQ hQO hFQ K hK hKS hKA hv ℓ hℓx hℓy
  obtain ⟨D,hD,hprofile⟩ := data.A.primitive_profile_correction_bound i
  refine ⟨h,hh,?_⟩
  intro ε hε ζ hζ
  obtain ⟨η,hη,_,hsmall⟩ := ExactCorrection.positive_power_threshold D 8 (ε/2)
    (by norm_num) (half_pos hε)
  obtain ⟨z,hz,hzcap,hz1,V,W,hV,hnear,hW,hgeometry,hclose⟩ :=
    hall (ε/2) (half_pos hε) (min η ζ) (lt_min hη hζ)
  obtain ⟨G,hG,hGO,hslow,hprof,hext⟩ := hnear
  have hzη := hzcap.trans_le (min_le_left _ _)
  have hzζ := hzcap.trans_le (min_le_right _ _)
  have herror : D*z^8 < ε/2 := by
    simpa only [Real.rpow_ofNat] using hsmall z hz hzη
  have hcorrection := hprofile V W hV hW.1 (z^8) z (pow_nonneg hz.le _) hz.le hz1 hclose
  refine ⟨z,hz,hzζ,hz1,W,hW,hgeometry,G,hG,hGO,?_,?_,V,hV,hclose,hext⟩
  · exact fun j => (hslow j).mono_const (by linarith)
  · intro p hp
    dsimp only
    have htriangle := dist_triangle
      (SurfaceVelocityFamily.Loop.primitiveJetProfile (data.A.vectorChartRead i W) z p)
      (SurfaceVelocityFamily.Loop.primitiveJetProfile (data.A.vectorChartRead i V) z p)
      (![((l.geometry (data.A.jetChartMap i G) (data.A.jetChartMap_smooth i hG) hGO).longitudinal.val p
          ((ℓ p/z : ℝ) : Period)),
        (l.geometry (data.A.jetChartMap i G) (data.A.jetChartMap_smooth i hG) hGO).Y p,
        (l.geometry (data.A.jetChartMap i G) (data.A.jetChartMap_smooth i hG) hGO).C p,
        ((l.geometry (data.A.jetChartMap i G) (data.A.jetChartMap_smooth i hG) hGO).longitudinal.slow
          (coordinateVector 1)).val p ((ℓ p/z : ℝ) : Period),
        (l.geometry (data.A.jetChartMap i G) (data.A.jetChartMap_smooth i hG) hGO).V.angle.val p
          ((ℓ p/z : ℝ) : Period)])
    simp only [dist_eq_norm] at htriangle
    exact htriangle.trans ((add_le_add (hcorrection p) (hprof p hp)).trans (by linarith))

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
