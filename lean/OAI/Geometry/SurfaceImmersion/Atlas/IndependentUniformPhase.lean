import OAI.Geometry.SurfaceImmersion.Correction.IndependentAtlasMean
import OAI.Geometry.SurfaceImmersion.Atlas.MixedAtlasGeometry
import OAI.Geometry.SurfaceImmersion.Primitive.IndependentPrimitiveNormalMargin
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
local instance independentUniformPhaseRealizationFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance independentUniformPhaseRealizationFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance independentUniformPhaseRealizationDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance independentUniformPhaseRealizationDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance independentUniformPhaseRealizationSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance independentUniformPhaseRealizationSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace MetricGoodPhaseData
open PrimitiveRealization
variable {g : SmoothMetric M} {F : M → Space}

/-- Arbitrary finite metric accuracy for the actual supported primitive
in a fixed nonlinear phase chart, using only the proved polynomial mean iteration. -/
theorem independent_uniform_phase_primitive_realization (data : MetricGoodPhaseData g F) (A₀ : SmoothingAtlas M)
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
    :
    ∃ c cB V₀ : ℝ, 0 < c ∧ 0 < cB ∧ 0 ≤ V₀ ∧ ∀ R N : ℕ,
    ∃ (b u η L C Cv : ℝ) (P : ℕ → ℝ), 0 ≤ b ∧ b < 1/16 ∧ 0 < u ∧
      0 < η ∧ η ≤ 1 ∧ 0 ≤ L ∧ 0 ≤ C ∧ 0 ≤ Cv ∧ (∀ m, 0 ≤ P m) ∧
      ∀ z : ℝ, 0 < z → z < η → ∃ G V : M → Space,
        ContMDiff planeModel spaceModel ∞ G ∧ ContMDiff planeModel spaceModel ∞ V ∧
        A₀.WeightedBound 1 3 (L*z^u) (G-F) ∧
        (∀ m, A₀.ShiftedBound 2 m (z^b) (P m) G) ∧
        A₀.WeightedBound z R Cv V ∧
        A₀.WeightedBound 1 0 V₀ V ∧
        A₀.ShiftedBound 2 R z (Cv/z^2) V ∧
        A₀.TensorWeightedBound 1 R (C*z^N)
          (inducedTensor V-(g.inner+A₀.bundleRestore A₀.tensorTriv i
            (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![a q^2,0,0]) y)))) ∧
        (∀ p, Function.Injective (mfderiv planeModel spaceModel V p)) ∧
        (∀ p, ∃ v w : SmallModes.Base,
          RealModes.realSecondForm (coordinateMap V p) v w (coordinateCenter p) ≠ 0) ∧
        (∀ j x, x ∈ (modeSupport (data.A.chartWeightCompact j) : Set SmallModes.Base) →
          cB < ‖RealModes.realSecondTensor (spaceCoordinates ∘ data.A.vectorPlaneRead j V) x‖) ∧
        (∀ p ∈ (S : Set JetPolynomial.Base) ∩ e.target,
          let H := SurfaceVelocityFamily.Loop.primitiveNormalTriple (A₀.vectorChartRead i V ∘ e.symm) p
          NormalFrame.gramDet (H 0) (H 1) ≠ 0 ∧
            c < ‖RealModes.realNormalPart (H 0) (H 1) (H 2)‖) ∧
        ∀ p ∉ tsupport (A₀.weight i), V =ᶠ[𝓝 p] G := by
  obtain ⟨ρ,Q',hρ,hQ',hQ'O,hnear⟩ := A₀.nonlinear_lowJet_neighborhood_of_C2 i hF hi
    S.isOpen hSc hQ O.isOpen hQO hFQ
  obtain ⟨ε,c,hε,hc,hnallOrders⟩ := l.all_orders_primitive_normal_geometry (S := S)
    hQ' hQ'O ℓ hℓx hℓy
  obtain ⟨Dt,hDt,htransport⟩ := A₀.phase_normal_margin i e he hi hcover
  have hcLocal : 0 < c/Dt := div_pos hc hDt
  obtain ⟨ρg,hρg,hgeometry⟩ := data.independent_supported_patch_geometry A₀ houter hF i
  obtain ⟨ρB,cB,hρB,hcB,hmargin⟩ := data.independent_primitive_atlas_normal_margin A₀ houter hF i hcLocal
  obtain ⟨V₀,hV₀,hF₀⟩ := A₀.exists_shifted_bound 2 0 hF
  refine ⟨c,cB,V₀+1,hc,hcB,by positivity,?_⟩
  intro R N
  obtain ⟨Pol,hPol,lm,hconstruct⟩ := A₀.supported_phase_primitive_metric i e he hi hχ hχc hχs
    l ha hamp S hTS hQ' hQ'O (N+(R+2)) ℓ hℓx hℓy
  obtain ⟨ln,hnb⟩ := hnallOrders (N+(R+2))
  let loss := max lm ln
  have hcap : 0 < 1/(1+(loss : ℝ)) := by positivity
  have hPol' := cutoffTensorPolynomial_smooth hχ (tensorPolynomialCoordinatePullback_smooth hPol he hi)
  obtain ⟨b,u,η,L,C,P,hb,hb16,hbl,hu,hη,hη1,hL,hC,hP,hmean⟩ :=
    data.polynomial_mean_approximation_in_atlas A₀ (A₀.primitiveAtlasPolynomial i
      (cutoffTensorPolynomial χ (tensorPolynomialCoordinatePullback Pol e e.symm)))
      (A₀.primitiveAtlasPolynomial_smooth i hPol') hF hmetric (R+2) (N+(R+2))
      (1/(1+(loss : ℝ))) hcap
  have hblm : b < 1/(1+(lm : ℝ)) := hbl.trans_le
    (one_div_le_one_div_of_le (by positivity)
      (by dsimp [loss]; exact_mod_cast Nat.add_le_add_left (Nat.le_max_left lm ln) 1))
  have hbln : b < 1/(1+(ln : ℝ)) := hbl.trans_le
    (one_div_le_one_div_of_le (by positivity)
      (by dsimp [loss]; exact_mod_cast Nat.add_le_add_left (Nat.le_max_right lm ln) 1))
  obtain ⟨η₀,hη₀,_,hsmall⟩ := ExactCorrection.positive_power_threshold L u ρ hu hρ
  obtain ⟨ηg,hηg,_,hgsmall⟩ := ExactCorrection.positive_power_threshold L u ρg hu hρg
  obtain ⟨ηB,hηB,_,hBsmall⟩ := ExactCorrection.positive_power_threshold L u ρB hu hρB
  obtain ⟨_,B,_,hB,hprofiles⟩ := A₀.nonlinear_jet_profiles i hi S.isOpen hSc P hP
  obtain ⟨Dmap,D,hDmap,hD,hprimitive⟩ := hconstruct (R+2) (B ((R+2)+(2*(N+(R+2)+1)+1))) (hB _)
  obtain ⟨Dn,_,hnormal⟩ := hnb (B ((2*(N+(R+2))+2)+2)) (hB _)
  obtain ⟨ηn,hηn,_,hnsmall⟩ := primitive_normal_threshold hb hbln hε Dn
  obtain ⟨ηs,hηs,_,hslowzero⟩ := ExactCorrection.positive_power_threshold L u (1/2) hu (by norm_num)
  obtain ⟨ηv,hηv,_,hinczero⟩ := primitive_normal_threshold hb hblm (by norm_num : (0:ℝ) < 1/2) Dmap
  let ηold := min η (min η₀ (min ηn (min ηg ηB)))
  have hηold : 0 < ηold := lt_min hη (lt_min hη₀ (lt_min hηn (lt_min hηg hηB)))
  refine ⟨b,u,min ηold (min ηs ηv),L,C+D,P 0+P R+Dmap,P,hb,hb16,hu,
    lt_min hηold (lt_min hηs hηv),
    (min_le_left _ _).trans ((min_le_left _ _).trans hη1),hL,add_nonneg hC hD,
    add_nonneg (add_nonneg (hP 0) (hP R)) hDmap,hP,?_⟩
  intro z hz hznew
  have hzη : z < ηold := hznew.trans_le (min_le_left _ _)
  have hzs0 : z < ηs := hznew.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hzv0 : z < ηv := hznew.trans_le ((min_le_right _ _).trans (min_le_right _ _))
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
      (hsmall z hz (hzη.trans_le ((min_le_right _ _).trans (min_le_left _ _)))).le)
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
  have hnall : ∀ p ∈ (S : Set JetPolynomial.Base) ∩ e.target,
      let H := SurfaceVelocityFamily.Loop.primitiveNormalTriple (A₀.vectorChartRead i V ∘ e.symm) p
      NormalFrame.gramDet (H 0) (H 1) ≠ 0 ∧ c < ‖RealModes.realNormalPart (H 0) (H 1) (H 2)‖ := by
    intro p hp
    have heq := A₀.phaseAtlasAnsatz_normalTriple i G e hi hχs U hK hKA hzero hone ℓ
      (N+(R+2)+1) z hp.2
    change NormalFrame.gramDet _ _ ≠ 0 ∧ c < ‖_‖
    rw [show SurfaceVelocityFamily.Loop.primitiveNormalTriple (A₀.vectorChartRead i V ∘ e.symm) p =
      SurfaceVelocityFamily.Loop.primitiveNormalTriple
        (finiteAnsatz (A₀.vectorChartRead i G ∘ e.symm) U ℓ (N+(R+2)+1) z) p from heq]
    have hh := hnormal (A₀.jetChartMap i G ∘ e.symm) ((A₀.jetChartMap_smooth i hG).comp hi)
      hGQ (z^b) z hz hzs hs1
      ((hprofiles G hG ⟨z^b,hs.le⟩ hs hs1 hmap).2 ((2*(N+(R+2))+2)+2))
      (hnsmall z hz (hzη.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
      U hUs hrep hinit p hp.1
    have heuc : (fun q => JetVelocityCoordinates.toEuclidean ((A₀.jetChartMap i G ∘ e.symm) q)) =
      A₀.vectorChartRead i G ∘ e.symm := by
      funext q
      exact spaceCoordinates.symm_apply_apply _
    rw [heuc] at hh
    exact hh
  have hext : ∀ p ∉ tsupport (A₀.weight i), V =ᶠ[𝓝 p] G := by
    intro p hp
    exact A₀.phaseAtlasAnsatz_eventuallyEq i G e hi hχs U hK hKA hzero ℓ (N+(R+2)+1) z hp
  have hlocal : ∀ p ∈ tsupport (A₀.weight i),
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A₀.vectorPlaneRead i V)
        (planeCoordinateIsometry (chart (i : M) p))) ∧
      c/Dt < ‖RealModes.realSecondTensor (spaceCoordinates ∘ A₀.vectorPlaneRead i V)
        (planeCoordinateIsometry (chart (i : M) p))‖ := by
    intro p hp
    have hx : chart (i : M) p ∈ (A₀.chartWeightCompact i : Set JetPolynomial.Base) := ⟨p,hp,rfl⟩
    exact htransport V (hVs z) _ hx c hc
      (hnall _ ⟨hTS (hcover hx),e.map_source (hcover hx)⟩)
  have hglobal := hgeometry G V hG (hVs z) (L*z^u) (by positivity)
    (hgsmall z hz (hzη.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))
    (fun j => (hclose j).mono_order (by omega))
    (fun p hp => ⟨(hlocal p hp).1,norm_pos_iff.mp (hcLocal.trans (hlocal p hp).2)⟩) hext
  have hBglobal := hmargin G V hG (hVs z) hglobal.1 (L*z^u) (by positivity)
    (hBsmall z hz (hzη.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))))
    (fun j => (hclose j).mono_order (by omega)) (fun p hp => (hlocal p hp).2) hext
  have hFzero : A₀.WeightedBound 1 0 V₀ F := by
    intro j k hk x hx
    have hk0 : k = 0 := by omega
    subst k
    simpa only [one_pow,one_mul,iteratedFDerivWithin_univ] using hF₀ j 0 (by omega) x
  have hslow0 : A₀.WeightedBound 1 0 (1/2) (G-F) := fun j =>
    ((hclose j).mono_order (Nat.zero_le _)).mono_const (hslowzero z hz hzs0).le
  have hinc0 : A₀.WeightedBound 1 0 (1/2) (V-G) := by
    intro j k hk x hx
    have hk0 : k = 0 := by omega
    subst k
    have hh := hincrement j 0 (by omega) x hx
    simp only [pow_zero,one_mul] at hh ⊢
    exact hh.trans (hinczero z hz hzv0).le
  have hsum0 := A₀.weightedBound_add hF (hG.sub hF) zero_le_one hFzero hslow0
  have hsum1 := A₀.weightedBound_add (hF.add (hG.sub hF)) ((hVs z).sub hG)
    zero_le_one hsum0 hinc0
  have hVzero : A₀.WeightedBound 1 0 (V₀+1) V := by
    change A₀.WeightedBound 1 0 (V₀+1/2+1/2) (F+(G-F)+(V-G)) at hsum1
    have hsumid : F+(G-F)+(V-G) = V := by abel
    rw [hsumid] at hsum1
    convert hsum1 using 1; ring
  refine ⟨G,V,hG,hVs z,hclose,hmap,hVweighted',hVzero,hvmap',?_,hglobal.1,hglobal.2,hBglobal,hnall,hext⟩
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

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
