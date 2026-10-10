import OAI.Geometry.SurfaceImmersion.Primitive.UniformPrimitiveGeometricApproximation
import OAI.Geometry.SurfaceImmersion.Geometry.ExactFastFamily

namespace OAI

/-! Actual fast approximants with prescribed accuracy in the leading five
primitive derivatives and the slow baseline, retained for the exact step. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes PrimitiveRealization CovarianceCorrector
local instance profiledPrimitiveFamilyFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance profiledPrimitiveFamilyFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance profiledPrimitiveFamilyDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance profiledPrimitiveFamilyDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance profiledPrimitiveFamilySectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance profiledPrimitiveFamilySectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas

def PrimitiveProfileNear (A : SmoothingAtlas M) (F : M → Space) (i : A.centers)
    {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)
    (S : TopologicalSpace.Opens JetPolynomial.Base) (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (ε z : ℝ) (V : M → Space) : Prop :=
  ∃ G : M → Space, ∃ hG : ContMDiff planeModel spaceModel ∞ G,
    ∃ hGO : MapsTo (lowJet (A.jetChartMap i G)) S O,
    A.WeightedBound 1 3 ε (G-F) ∧
    (∀ p ∈ S,
      let geom := l.geometry (A.jetChartMap i G) (A.jetChartMap_smooth i hG) hGO
      let t : Period := ((ℓ p/z : ℝ) : Period)
      ‖SurfaceVelocityFamily.Loop.primitiveJetProfile (A.vectorChartRead i V) z p-
        ![geom.longitudinal.val p t,geom.Y p,geom.C p,
          (geom.longitudinal.slow (coordinateVector 1)).val p t,geom.V.angle.val p t]‖ ≤ ε) ∧
    ∀ p ∉ tsupport (A.weight i), V =ᶠ[𝓝 p] G

end SmoothingAtlas
namespace MetricGoodPhaseData
variable {g : SmoothMetric M} {F : M → Space}

theorem profiled_primitive_fast_family (data : MetricGoodPhaseData g F)
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
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0) :
    ∃ h : SmoothMetric M, h.inner = g.inner+data.A.primitiveTensor i a ∧
    ∃ V₀ R₁ c₁ c₂ : ℝ, 0 ≤ V₀ ∧ 0 < R₁ ∧ 0 < c₁ ∧ 0 < c₂ ∧ ∀ ε : ℝ, 0 < ε →
      data.A.GeometricFastFamilyWithProperty h R₁ c₁ c₂ V₀
        (data.A.PrimitiveProfileNear F i l S ℓ ε) := by
  have hFO : MapsTo (lowJet (data.A.jetChartMap i F)) S O := fun x hx => hQO (hFQ hx)
  have hzero := data.A.primitive_amplitude_zero_off_weight i l hamp S houter
    (data.A.jetChartMap i F) hFO K hKA hv
  let h := data.A.primitiveMetric g i a ha hzero
  obtain ⟨ρ,R₁,c₁,hρ,hR₁,hc₁,hjet⟩ := data.A.metric_firstJet_margin h
  obtain ⟨c,c₂,V₀,hc,hc₂,hV₀,hfamilies⟩ := data.profiled_primitive_mean_realization
    hF hmetric i l ha hamp S T hST houter hQ hQO hFQ K hK hKS hKA hv ℓ hℓx hℓy
  refine ⟨h,rfl,V₀,R₁,c₁,c₂,hV₀,hR₁,hc₁,hc₂,?_⟩
  intro ε hε N
  obtain ⟨lp,b,u,η,L,C,Cv,Dp,P,hb,_,hu,hη,hη1,hL,hC,hCv,_,hblp,hP,hfamily⟩ :=
    hfamilies 442 (N+1)
  obtain ⟨η₀,hη₀,_,hsmall⟩ := ExactCorrection.positive_power_threshold C (N+1) ρ
    (by positivity) hρ
  obtain ⟨ηs,hηs,_,hslow⟩ := ExactCorrection.positive_power_threshold L u ε hu hε
  obtain ⟨ηp,hηp,_,hprofile⟩ := primitive_normal_threshold hb hblp hε Dp
  refine ⟨min η (min η₀ (min ηs ηp)),C,Cv,
    lt_min hη (lt_min hη₀ (lt_min hηs hηp)),hC,hCv,?_⟩
  intro z hz hzη
  have hzbase := hzη.trans_le (min_le_left _ _)
  have hzother := hzη.trans_le (min_le_right _ _)
  have hzmetric := hzother.trans_le (min_le_left _ _)
  have hzprofiles := hzother.trans_le (min_le_right _ _)
  have hzslow := hzprofiles.trans_le (min_le_left _ _)
  have hzprofile := hzprofiles.trans_le (min_le_right _ _)
  obtain ⟨G,V,hG,hV,hclose,hmap,hweighted,hzeroV,hshift,herror,hI,hB,hBmargin,hN,hext,hGs,hGO,hprof⟩ :=
    hfamily z hz hzbase
  have herr : data.A.TensorWeightedBound 1 440 (C*z^(N+1)) (inducedTensor V-h.inner) :=
    fun j => (herror j).mono_order (by omega)
  have hexp : (N : ℝ)+1 = ((N+1 : ℕ) : ℝ) := by norm_num
  have hjet' := hjet V hV (C*z^(N+1)) (by positivity)
    (by simpa only [hexp,Real.rpow_natCast] using hsmall z hz hzmetric)
    (fun j => (herr j).mono_order (by omega))
  refine ⟨V,hV,?_,hzeroV,hweighted,(fun j k hk x => hshift j k (by omega) x),herr,?_⟩
  · refine ⟨G,hGs,hGO,?_,?_,hext⟩
    · exact fun j => (hclose j).mono_const (hslow z hz hzslow).le
    · intro p hp
      exact (hprof p hp).trans (hprofile z hz hzprofile).le
  · intro j x hx
    exact ⟨(hjet' j x hx).1,(hjet' j x hx).2,(hBmargin j x hx).le⟩

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
