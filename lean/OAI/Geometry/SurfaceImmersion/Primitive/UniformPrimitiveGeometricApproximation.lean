import OAI.Geometry.SurfaceImmersion.Correction.UniformPrimitiveMeanRealization
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveMetric
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasMetricJetMargins

namespace OAI

/-! Actual finite-accuracy primitive immersions with a Riemannian target,
uniform first-jet bounds, and a uniform nonzero second-form margin. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes
local instance uniformPrimitiveGeometryFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance uniformPrimitiveGeometryFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance uniformPrimitiveGeometryDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance uniformPrimitiveGeometryDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance uniformPrimitiveGeometrySectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance uniformPrimitiveGeometrySectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace MetricGoodPhaseData
variable {g : SmoothMetric M} {F : M → Space}

theorem uniform_primitive_geometric_approximation (data : MetricGoodPhaseData g F)
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
    ∃ V₀ R₁ c₁ c₂ : ℝ, 0 ≤ V₀ ∧ 0 < R₁ ∧ 0 < c₁ ∧ 0 < c₂ ∧
    ∀ R N : ℕ, ∃ η C Cv : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧ 0 ≤ Cv ∧
      ∀ z : ℝ, 0 < z → z < η → ∃ V : M → Space,
        ContMDiff planeModel spaceModel ∞ V ∧
        data.A.WeightedBound z (R+2) Cv V ∧
        data.A.WeightedBound 1 0 V₀ V ∧
        data.A.ShiftedBound 2 R z (Cv/z^2) V ∧
        data.A.TensorWeightedBound 1 R (C*z^(N+1)) (inducedTensor V-h.inner) ∧
        (∀ p, Function.Injective (mfderiv planeModel spaceModel V p)) ∧
        (∀ p, ∃ v w : SmallModes.Base,
          realSecondForm (coordinateMap V p) v w (coordinateCenter p) ≠ 0) ∧
        ∀ j x, x ∈ (modeSupport (data.A.chartWeightCompact j) : Set SmallModes.Base) →
          ‖firstJetPair (spaceCoordinates ∘ data.A.vectorPlaneRead j V) x‖ ≤ R₁ ∧
          c₁ ≤ NormalFrame.gramDet
            (firstJetPair (spaceCoordinates ∘ data.A.vectorPlaneRead j V) x).1
            (firstJetPair (spaceCoordinates ∘ data.A.vectorPlaneRead j V) x).2 ∧
          c₂ < ‖realSecondTensor (spaceCoordinates ∘ data.A.vectorPlaneRead j V) x‖ := by
  have hFO : MapsTo (lowJet (data.A.jetChartMap i F)) S O := fun x hx => hQO (hFQ hx)
  have hzero := data.A.primitive_amplitude_zero_off_weight i l hamp S houter
    (data.A.jetChartMap i F) hFO K hKA hv
  let h := data.A.primitiveMetric g i a ha hzero
  obtain ⟨ρ,R₁,c₁,hρ,hR₁,hc₁,hjet⟩ := data.A.metric_firstJet_margin h
  obtain ⟨c,c₂,V₀,hc,hc₂,hV₀,hfamilies⟩ :=
    data.uniform_primitive_mean_realization hF hmetric i l ha hamp S T hST houter hQ hQO hFQ
      K hK hKS hKA hv ℓ hℓx hℓy
  refine ⟨h,rfl,V₀,R₁,c₁,c₂,hV₀,hR₁,hc₁,hc₂,?_⟩
  intro R N
  obtain ⟨b,u,η,L,C,Cv,P,hb,hb16,hu,hη,hη1,hL,hC,hCv,hP,hfamily⟩ := hfamilies (R+2) (N+1)
  obtain ⟨η₀,hη₀,_,hsmall⟩ := ExactCorrection.positive_power_threshold C (N+1) ρ
    (by positivity) hρ
  refine ⟨min η η₀,C,Cv,lt_min hη hη₀,(min_le_left _ _).trans hη1,hC,hCv,?_⟩
  intro z hz hzη
  obtain ⟨G,V,hG,hV,hclose,hslow,hweighted,hzero,hshift,herror,hI,hB,hBmargin,hN,hext⟩ :=
    hfamily z hz (hzη.trans_le (min_le_left _ _))
  have herr : data.A.TensorWeightedBound 1 R (C*z^(N+1)) (inducedTensor V-h.inner) :=
    fun j => (herror j).mono_order (by omega)
  have hexp : (N : ℝ)+1 = ((N+1 : ℕ) : ℝ) := by norm_num
  have hjet' := hjet V hV (C*z^(N+1)) (by positivity)
    (by simpa only [hexp,Real.rpow_natCast] using
      hsmall z hz (hzη.trans_le (min_le_right _ _)))
    (fun j => (herr j).mono_order (Nat.zero_le R))
  refine ⟨V,hV,hweighted,hzero,(fun j k hk x => hshift j k (by omega) x),herr,hI,hB,?_⟩
  intro j x hx
  exact ⟨(hjet' j x hx).1,(hjet' j x hx).2,hBmargin j x hx⟩

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
