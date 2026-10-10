import OAI.Geometry.SurfaceImmersion.Correction.IndependentAtlasMean
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
local instance independentPhaseRealizationFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance independentPhaseRealizationFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance independentPhaseRealizationDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance independentPhaseRealizationDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance independentPhaseRealizationSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance independentPhaseRealizationSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace MetricGoodPhaseData
open PrimitiveRealization
variable {g : SmoothMetric M} {F : M → Space}

/-- Arbitrary finite metric accuracy for the actual supported primitive
in a fixed nonlinear phase chart, using only the proved polynomial mean iteration. -/
theorem independent_phase_primitive_mean_realization (data : MetricGoodPhaseData g F) (A₀ : SmoothingAtlas M)
    (hF : ContMDiff planeModel spaceModel ∞ F) (hmetric : g.inner = inducedTensor F)
    (i : A₀.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ e.source)
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
    (R N : ℕ) :
    ∃ (b u η L C Cv : ℝ) (P : ℕ → ℝ), 0 ≤ b ∧ b < 1/16 ∧ 0 < u ∧
      0 < η ∧ η ≤ 1 ∧ 0 ≤ L ∧ 0 ≤ C ∧ 0 ≤ Cv ∧ (∀ m, 0 ≤ P m) ∧
      ∀ z : ℝ, 0 < z → z < η → ∃ G V : M → Space,
        ContMDiff planeModel spaceModel ∞ G ∧ ContMDiff planeModel spaceModel ∞ V ∧
        A₀.WeightedBound 1 3 (L*z^u) (G-F) ∧
        (∀ m, A₀.ShiftedBound 2 m (z^b) (P m) G) ∧
        A₀.WeightedBound z R Cv V ∧
        A₀.ShiftedBound 2 R z (Cv/z^2) V ∧
        A₀.TensorWeightedBound 1 R (C*z^N)
          (inducedTensor V-(g.inner+A₀.bundleRestore A₀.tensorTriv i
            (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![a q^2,0,0]) y)))) ∧
        ∀ p ∉ tsupport (A₀.weight i), V =ᶠ[𝓝 p] G := by
  obtain ⟨ρ,Q',hρ,hQ',hQ'O,hnear⟩ := A₀.nonlinear_lowJet_neighborhood_of_C2 i hF hi
    S.isOpen hSc hQ O.isOpen hQO hFQ
  obtain ⟨Pol,hPol,lm,hconstruct⟩ := A₀.supported_phase_primitive_metric i e he hi hχ hχc hχs
    l ha hamp S hTS hQ' hQ'O (N+(R+2)) ℓ hℓx hℓy
  have hcap : 0 < 1/(1+(lm : ℝ)) := by positivity
  have hPol' := cutoffTensorPolynomial_smooth hχ (tensorPolynomialCoordinatePullback_smooth hPol he hi)
  obtain ⟨b,u,η,L,C,P,hb,hb16,hblm,hu,hη,hη1,hL,hC,hP,hmean⟩ :=
    data.polynomial_mean_approximation_in_atlas A₀ (A₀.primitiveAtlasPolynomial i
      (cutoffTensorPolynomial χ (tensorPolynomialCoordinatePullback Pol e e.symm)))
      (A₀.primitiveAtlasPolynomial_smooth i hPol') hF hmetric (R+2) (N+(R+2))
      (1/(1+(lm : ℝ))) hcap
  obtain ⟨η₀,hη₀,_,hsmall⟩ := ExactCorrection.positive_power_threshold L u ρ hu hρ
  obtain ⟨_,B,_,hB,hprofiles⟩ := A₀.nonlinear_jet_profiles i hi S.isOpen hSc P hP
  obtain ⟨Dmap,D,hDmap,hD,hprimitive⟩ := hconstruct (R+2) (B ((R+2)+(2*(N+(R+2)+1)+1))) (hB _)
  refine ⟨b,u,min η η₀,L,C+D,P 0+P R+Dmap,P,hb,hb16,hu,lt_min hη hη₀,
    (min_le_left _ _).trans hη1,hL,add_nonneg hC hD,
    add_nonneg (add_nonneg (hP 0) (hP R)) hDmap,hP,?_⟩
  intro z hz hzη
  have hzη' : z < η := hzη.trans_le (min_le_left _ _)
  have hz1 : z ≤ 1 := hzη'.le.trans hη1
  have hs : 0 < z^b := Real.rpow_pos_of_pos hz _
  have hs1 : z^b ≤ 1 := Real.rpow_le_one hz.le hz1 hb
  have hzs : z ≤ z^b := by
    have hb1 : b ≤ 1 := by linarith
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hz hz1 hb1
  obtain ⟨G,hG,hclose,hmap,hmean⟩ := hmean z hz hzη'
  have hGQ : MapsTo (lowJet (A₀.jetChartMap i G ∘ e.symm)) S Q' :=
    hnear G hG (fun j => ((hclose j).mono_order (by omega)).mono_const
      (hsmall z hz (hzη.trans_le (min_le_right _ _))).le)
  have hGv : ∀ p ∈ S, p ∉ K → ∀ t,
      l.velocity (lowJet (A₀.jetChartMap i G ∘ e.symm) p,t) =
        SurfaceVelocityFamily.normal (lowJet (A₀.jetChartMap i G ∘ e.symm) p) := by
    intro p hp hpK t
    exact hv _ (hQ'O (hGQ hp)) (by simpa only [lowJetPosition_lowJet] using hpK) t
  obtain ⟨U,hzero,hUs,hrep,hinit,hVs,herror⟩ := hprimitive G hG hGQ K hK hKS hKA hone hGv
  let V := A₀.phaseAtlasAnsatz i G e χ U ℓ (N+(R+2)+1) z
  have hjet := (hprofiles G hG ⟨z^b,hs.le⟩ hs hs1 hmap).2 ((R+2)+(2*(N+(R+2)+1)+1))
  have hsolved : A₀.TensorWeightedBound z (R+2) (C*z^(N+(R+2)))
      (A₀.atlasPolynomialMetric (A₀.primitiveAtlasPolynomial i
        (cutoffTensorPolynomial χ (tensorPolynomialCoordinatePullback Pol e e.symm))) z G-g.inner) :=
    fun j => (hmean j).shrink_scale hz.le hz1
  have herr := (herror (z^b) z hz hzs hs1 hjet).2 g.inner g.contMDiff (C*z^(N+(R+2))) hsolved
  have htot : 0 ≤ C*z^(N+(R+2))+D*z^(N+(R+2)+1)/(z^b)^lm := by positivity
  have hfinal := A₀.tensorWeightedBound_unscaled hz hz1 htot herr
  have hincrement := (herror (z^b) z hz hzs hs1 hjet).1
  have hsmallinc : Dmap*z/(z^b)^lm ≤ Dmap := by
    apply (div_le_iff₀ (pow_pos hs _)).mpr
    exact mul_le_mul_of_nonneg_left (slow_power_dominates_fast hz hz1 hb hblm) hDmap
  have hGweighted := A₀.weighted_of_shifted_two hz.le hzs hs1 (hmap R)
  have hincweighted : A₀.WeightedBound z R Dmap (V-G) :=
    fun j => ((hincrement j).mono_order (by omega)).mono_const hsmallinc
  have hVweighted := A₀.weightedBound_add hG ((hVs z).sub hG) hz.le hGweighted hincweighted
  have hvadd : G+(V-G) = V := by abel
  change A₀.WeightedBound z R (P R+Dmap) (G+(V-G)) at hVweighted
  rw [hvadd] at hVweighted
  have hVweighted' : A₀.WeightedBound z R (P 0+P R+Dmap) V :=
    fun j => (hVweighted j).mono_const (by linarith [hP 0])
  have hshift := A₀.weighted_to_shifted (q := 2) (m := R) hz hz1
    (show 0 ≤ Dmap*z/(z^b)^lm by positivity)
    (show A₀.WeightedBound z (2+R) (Dmap*z/(z^b)^lm) (V-G) from by
      simpa only [V,Nat.add_comm R 2] using hincrement)
  have hshift' : A₀.ShiftedBound 2 R z (Dmap/z^2) (V-G) := by
    intro j k hk x
    exact (hshift j k hk x).trans (div_le_div_of_nonneg_right hsmallinc (sq_nonneg z))
  have hvmap := A₀.shifted_map_recurrence hG ((hVs z).sub hG)
    (hmap 0) (hmap R) hshift' hs hz.le hzs (hP 0) (hP R)
  change A₀.ShiftedBound 2 R z (P 0+(z/(z^b))*P R+Dmap/z^2) (G+(V-G)) at hvmap
  rw [hvadd] at hvmap
  have hvmap' : A₀.ShiftedBound 2 R z ((P 0+P R+Dmap)/z^2) V := by
    intro j k hk x
    exact (hvmap j k hk x).trans (primitive_shifted_budget hz hz1 hzs (hP 0) (hP R) hDmap)
  refine ⟨G,V,hG,hVs z,hclose,hmap,hVweighted',hvmap',?_,?_⟩
  · intro j
    apply ((hfinal j).mono_order (by omega)).mono_const
    have hlead : C*z^(N+(R+2))/z^(R+2) = C*z^N := by
      rw [pow_add,← mul_assoc,mul_div_cancel_right₀ _ (pow_ne_zero _ hz.ne')]
    rw [add_div,hlead]
    have htail := mul_le_mul_of_nonneg_left
      (primitive_tail_power_bound (N := N) (R := R+2) hz hz1 hb hblm) hD
    have heq : D*z^(N+(R+2)+1)/(z^b)^lm/z^(R+2) = D*(z^(N+(R+2)+1)/(z^b)^lm/z^(R+2)) := by ring
    rw [heq]
    calc
      C*z^N+D*(z^(N+(R+2)+1)/(z^b)^lm/z^(R+2)) ≤ C*z^N+D*z^N := add_le_add le_rfl htail
      _ = (C+D)*z^N := by ring
  · intro p hp
    exact A₀.phaseAtlasAnsatz_eventuallyEq i G e hi hχs U hK hKA hzero ℓ (N+(R+2)+1) z hp

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
