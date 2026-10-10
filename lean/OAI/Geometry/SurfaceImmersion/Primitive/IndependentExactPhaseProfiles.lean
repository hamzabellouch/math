import OAI.Geometry.SurfaceImmersion.Primitive.IndependentExactProfiledPhase
import OAI.Geometry.SurfaceImmersion.Primitive.ExactProfiledPhasePrimitive
import OAI.Geometry.SurfaceImmersion.Primitive.PhaseProfileStability
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
local instance independentActualPhasePrimitiveProfilesFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance independentActualPhasePrimitiveProfilesFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance independentActualPhasePrimitiveProfilesDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance independentActualPhasePrimitiveProfilesDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance independentActualPhasePrimitiveProfilesSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance independentActualPhasePrimitiveProfilesSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace MetricGoodPhaseData
variable {g : SmoothMetric M} {F : M → Space}

theorem independent_exact_phase_primitive_five_profiles [T2Space M] (data : MetricGoodPhaseData g F) (A₀ : SmoothingAtlas M)
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
    ∀ ε : ℝ, 0 < ε → ∀ ζ : ℝ, 0 < ζ →
    ∃ z : ℝ, 0 < z ∧ z < ζ ∧ z ≤ 1 ∧ ∃ W : M → Space,
      IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      ∃ G : M → Space, ∃ hG : ContMDiff planeModel spaceModel ∞ G,
      ∃ hGO : MapsTo (lowJet (A₀.jetChartMap i G ∘ e.symm)) S O,
      A₀.WeightedBound 1 3 ε (G-F) ∧
      (∀ p ∈ (S : Set JetPolynomial.Base) ∩ e.target,
        let geom := l.geometry (A₀.jetChartMap i G ∘ e.symm) ((A₀.jetChartMap_smooth i hG).comp hi) hGO
        let t : Period := ((ℓ p/z : ℝ) : Period)
        ‖SurfaceVelocityFamily.Loop.primitiveJetProfile (A₀.vectorChartRead i W ∘ e.symm) z p-
          ![geom.longitudinal.val p t,geom.Y p,geom.C p,
            (geom.longitudinal.slow (coordinateVector 1)).val p t,geom.V.angle.val p t]‖ ≤ ε) ∧
      ∃ V : M → Space, ContMDiff planeModel spaceModel ∞ V ∧
        A₀.WeightedBound 1 2 (z^8) (W-V) ∧
        (∀ p ∉ tsupport (A₀.weight i), V =ᶠ[𝓝 p] G) ∧
        ∀ p ∉ A₀.phaseSurfaceSupport i e K, V =ᶠ[𝓝 p] G := by
  have hall := data.independent_exact_profiled_phase_primitive_metric A₀ houter hF hmetric i e he hi hχ hχc hχs hcover
    l ha hamp S hSc hTS hQ hQO hFQ K hK hKS hKA hone hv ℓ hℓx hℓy h htarget
  obtain ⟨D,hD,hprofile⟩ := A₀.phase_profile_correction_bound i hi S.isOpen hSc
  intro ε hε ζ hζ
  obtain ⟨η,hη,_,hsmall⟩ := ExactCorrection.positive_power_threshold D 8 (ε/2)
    (by norm_num) (half_pos hε)
  obtain ⟨z,hz,hzcap,hz1,V,W,hV,hnear,hW,hgeometry,hclose⟩ :=
    hall (ε/2) (half_pos hε) (min η ζ) (lt_min hη hζ)
  obtain ⟨G,hG,hGO,hslow,hprof,hext,hextK⟩ := hnear
  have hzη := hzcap.trans_le (min_le_left _ _)
  have hzζ := hzcap.trans_le (min_le_right _ _)
  have herror : D*z^8 < ε/2 := by
    simpa only [Real.rpow_ofNat] using hsmall z hz hzη
  have hcorrection := hprofile V W hV hW.1 (z^8) z (pow_nonneg hz.le _) hz.le hz1 hclose
  refine ⟨z,hz,hzζ,hz1,W,hW,hgeometry,G,hG,hGO,?_,?_,V,hV,hclose,hext,hextK⟩
  · exact fun j => (hslow j).mono_const (by linarith)
  · intro p hp
    dsimp only
    have htriangle := dist_triangle
      (SurfaceVelocityFamily.Loop.primitiveJetProfile (A₀.vectorChartRead i W ∘ e.symm) z p)
      (SurfaceVelocityFamily.Loop.primitiveJetProfile (A₀.vectorChartRead i V ∘ e.symm) z p)
      (![((l.geometry (A₀.jetChartMap i G ∘ e.symm) ((A₀.jetChartMap_smooth i hG).comp hi) hGO).longitudinal.val p
          ((ℓ p/z : ℝ) : Period)),
        (l.geometry (A₀.jetChartMap i G ∘ e.symm) ((A₀.jetChartMap_smooth i hG).comp hi) hGO).Y p,
        (l.geometry (A₀.jetChartMap i G ∘ e.symm) ((A₀.jetChartMap_smooth i hG).comp hi) hGO).C p,
        ((l.geometry (A₀.jetChartMap i G ∘ e.symm) ((A₀.jetChartMap_smooth i hG).comp hi) hGO).longitudinal.slow
          (coordinateVector 1)).val p ((ℓ p/z : ℝ) : Period),
        (l.geometry (A₀.jetChartMap i G ∘ e.symm) ((A₀.jetChartMap_smooth i hG).comp hi) hGO).V.angle.val p
          ((ℓ p/z : ℝ) : Period)])
    simp only [dist_eq_norm] at htriangle
    exact htriangle.trans ((add_le_add (hcorrection p hp.1) (hprof p hp)).trans (by linarith))

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
