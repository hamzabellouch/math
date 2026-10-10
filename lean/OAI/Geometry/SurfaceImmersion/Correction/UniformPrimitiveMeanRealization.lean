import OAI.Geometry.SurfaceImmersion.Correction.PrimitiveMeanRealization
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasLowJetNeighborhood
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMeanApproximation
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveShiftedPowers
import OAI.Geometry.SurfaceImmersion.Primitive.UniformPrimitiveNormal
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveWeightedBudget
import OAI.Geometry.SurfaceImmersion.Primitive.SupportedPrimitiveGeometry
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveAtlasNormalMargin
import OAI.Geometry.SurfaceImmersion.Primitive.AtlasPrimitiveNormal
import OAI.Geometry.SurfaceImmersion.Primitive.UniformPrimitiveProfiles

namespace OAI

/-! Construct the actual globally supported primitive from the finite recursion
and its extended polynomial mean operator. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector
open WeightedEstimates NormalFrame
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

theorem all_orders_primitive_normal_geometry {S : TopologicalSpace.Opens JetPolynomial.Base}
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hx : ℓ (coordinateVector 0) = 1) (hy : ℓ (coordinateVector 1) = 0) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∀ n : ℕ, ∃ loss : ℕ,
      ∀ B : ℝ, 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
        (hGQ : MapsTo (lowJet G) S Q),
      ∀ (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      WeightedBound S s ((2*n+2)+2) B (lowJet G) → D*z/s^loss < ε →
      ∀ U : ℕ → Family S Euclidean,
        (∀ i, ContDiff ℝ ∞ (fun y : JetPolynomial.Base × ℝ => (U i).val y.1 (y.2 : Period))) →
        (∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i)) →
        U 0 = (l.geometry G hG (fun _ hp => hQO (hGQ hp))).initial →
      ∀ p ∈ S,
        let H := primitiveNormalTriple (finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q))
          U ℓ (n+1) z) p
        gramDet (H 0) (H 1) ≠ 0 ∧ c < ‖realNormalPart (H 0) (H 1) (H 2)‖ := by
  obtain ⟨ε,c,hε,hc,hn⟩ := l.compact_normal_margin hQ hQO
  refine ⟨ε,c,hε,hc,?_⟩
  intro n
  obtain ⟨loss,hb⟩ := l.uniform_primitive_normal_triple (S := S) hQ hQO n ℓ hx hy
  refine ⟨loss,?_⟩
  intro B hB
  obtain ⟨D,hD,hd⟩ := hb B hB
  refine ⟨D,hD,?_⟩
  intro G hG hGQ s z hz hzs hs1 hbound hsmall U hU hrep hinit p hp
  exact hn _ (hGQ hp) (ℓ p/z) _
    ((hd G hG hGQ s z hz hzs hs1 hbound U hU hrep hinit p hp).trans_lt hsmall)

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector WeightedEstimates
local instance uniformPrimitiveRealizationFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance uniformPrimitiveRealizationFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance uniformPrimitiveRealizationDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance uniformPrimitiveRealizationDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance uniformPrimitiveRealizationSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance uniformPrimitiveRealizationSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace MetricGoodPhaseData
open PrimitiveRealization
variable {g : SmoothMetric M} {F : M → Space}

/-- Arbitrary finite metric accuracy for a genuine supported primitive.
The slow baseline maps are constructed by the polynomial mean iteration;
their admissibility follows from the original map's compact jet margin. -/
theorem profiled_primitive_mean_realization (data : MetricGoodPhaseData g F)
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
    ∃ c cB V₀ : ℝ, 0 < c ∧ 0 < cB ∧ 0 ≤ V₀ ∧ ∀ R N : ℕ,
    ∃ lp : ℕ, ∃ (b u η L C Cv Dp : ℝ) (P : ℕ → ℝ), 0 ≤ b ∧ b < 1/16 ∧ 0 < u ∧
      0 < η ∧ η ≤ 1 ∧ 0 ≤ L ∧ 0 ≤ C ∧ 0 ≤ Cv ∧ 0 ≤ Dp ∧
      b < 1/(1+(lp : ℝ)) ∧ (∀ m, 0 ≤ P m) ∧
      ∀ z : ℝ, 0 < z → z < η → ∃ G V : M → Space,
        ContMDiff planeModel spaceModel ∞ G ∧ ContMDiff planeModel spaceModel ∞ V ∧
        data.A.WeightedBound 1 3 (L*z^u) (G-F) ∧
        (∀ m, data.A.ShiftedBound 2 m (z^b) (P m) G) ∧
        data.A.WeightedBound z R Cv V ∧
        data.A.WeightedBound 1 0 V₀ V ∧
        data.A.ShiftedBound 2 R z (Cv/z^2) V ∧
        data.A.TensorWeightedBound 1 R (C*z^N)
          (inducedTensor V-(g.inner+data.A.bundleRestore data.A.tensorTriv i
            (fun y => fiberFromThree ![a y^2,0,0]))) ∧
        (∀ p, Function.Injective (mfderiv planeModel spaceModel V p)) ∧
        (∀ p, ∃ v w : SmallModes.Base,
          RealModes.realSecondForm (coordinateMap V p) v w (coordinateCenter p) ≠ 0) ∧
        (∀ j x, x ∈ (modeSupport (data.A.chartWeightCompact j) : Set SmallModes.Base) →
          cB < ‖RealModes.realSecondTensor (spaceCoordinates ∘ data.A.vectorPlaneRead j V) x‖) ∧
        (∀ p ∈ S,
          let H := SurfaceVelocityFamily.Loop.primitiveNormalTriple (data.A.vectorChartRead i V) p
          NormalFrame.gramDet (H 0) (H 1) ≠ 0 ∧
            c < ‖RealModes.realNormalPart (H 0) (H 1) (H 2)‖) ∧
        (∀ p ∉ tsupport (data.A.weight i), V =ᶠ[𝓝 p] G) ∧
        ∃ hGs : ContMDiff planeModel spaceModel ∞ G,
        ∃ hGO : MapsTo (lowJet (data.A.jetChartMap i G)) S O,
          ∀ p ∈ S,
            let geom := l.geometry (data.A.jetChartMap i G) (data.A.jetChartMap_smooth i hGs) hGO
            let t : Period := ((ℓ p/z : ℝ) : Period)
            ‖SurfaceVelocityFamily.Loop.primitiveJetProfile (data.A.vectorChartRead i V) z p-
              ![geom.longitudinal.val p t,geom.Y p,geom.C p,
                (geom.longitudinal.slow (coordinateVector 1)).val p t,geom.V.angle.val p t]‖ ≤
              Dp*z/(z^b)^lp := by
  obtain ⟨ρg,hρg,hgeometry⟩ := data.supported_primitive_geometry hF i
  obtain ⟨ρ,Q',hρ,hQ',hQ'O,hnear⟩ := data.A.lowJet_neighborhood_of_C2 i hF S.isOpen hQ O.isOpen hQO hFQ
  obtain ⟨ε,c,hε,hc,hnallOrders⟩ := l.all_orders_primitive_normal_geometry (S := S)
    hQ' hQ'O ℓ hℓx hℓy
  obtain ⟨ρB,cB,hρB,hcB,hmargin⟩ := data.primitive_atlas_normal_margin hF i hc
  obtain ⟨V₀,hV₀,hF₀⟩ := data.A.exists_shifted_bound 2 0 hF
  refine ⟨c,cB,V₀+1,hc,hcB,by positivity,?_⟩
  intro R N
  obtain ⟨Pol,hPol,lm,hconstruct⟩ := data.A.supported_primitive_metric i l ha hamp S houter
    hQ' hQ'O (N+(R+2)) ℓ hℓx hℓy
  obtain ⟨ln,hnb⟩ := hnallOrders (N+(R+2))
  obtain ⟨lp,hpb⟩ := l.uniform_primitive_five_profiles (S := S) hQ' hQ'O
    (N+(R+2)) ℓ hℓx hℓy
  let loss := max (max lm ln) lp
  have hcap : 0 < 1/(1+(loss : ℝ)) := by positivity
  obtain ⟨b,u,η,L,C,P,hb,hb16,hbl,hu,hη,hη1,hL,hC,hP,hmean⟩ :=
    data.polynomial_mean_approximation (data.A.primitiveAtlasPolynomial i Pol)
      (data.A.primitiveAtlasPolynomial_smooth i hPol) hF hmetric (R+2) (N+(R+2))
      (1/(1+(loss : ℝ))) hcap
  have hblm : b < 1/(1+(lm : ℝ)) := hbl.trans_le
    (one_div_le_one_div_of_le (by positivity)
      (by dsimp [loss]; exact_mod_cast Nat.add_le_add_left ((Nat.le_max_left lm ln).trans (Nat.le_max_left _ _)) 1))
  have hbln : b < 1/(1+(ln : ℝ)) := hbl.trans_le
    (one_div_le_one_div_of_le (by positivity)
      (by dsimp [loss]; exact_mod_cast Nat.add_le_add_left ((Nat.le_max_right lm ln).trans (Nat.le_max_left _ _)) 1))
  have hblp : b < 1/(1+(lp : ℝ)) := hbl.trans_le
    (one_div_le_one_div_of_le (by positivity)
      (by dsimp [loss]; exact_mod_cast Nat.add_le_add_left (Nat.le_max_right (max lm ln) lp) 1))
  obtain ⟨η₀,hη₀,_,hsmall⟩ := ExactCorrection.positive_power_threshold L u ρ hu hρ
  obtain ⟨ηg,hηg,_,hgsmall⟩ := ExactCorrection.positive_power_threshold L u ρg hu hρg
  obtain ⟨ηB,hηB,_,hBsmall⟩ := ExactCorrection.positive_power_threshold L u ρB hu hρB
  obtain ⟨_,B,_,hB,hprofiles⟩ := data.A.atlas_jet_profiles
    (fun _ => (S : Set JetPolynomial.Base)) (fun _ => S.isOpen) (fun _ => T) (fun _ => hST) P hP
  obtain ⟨Dmap,D,hDmap,hD,hprimitive⟩ := hconstruct (R+2) (B i ((R+2)+(2*(N+(R+2)+1)+1))) (hB _ _)
  obtain ⟨Dn,_,hnormal⟩ := hnb (B i ((2*(N+(R+2))+2)+2)) (hB _ _)
  obtain ⟨Dp,hDp,hprofile⟩ := hpb (B i ((2*(N+(R+2))+2)+2)) (hB _ _)
  obtain ⟨ηn,hηn,_,hnsmall⟩ := primitive_normal_threshold hb hbln hε Dn
  obtain ⟨ηs,hηs,_,hslowzero⟩ := ExactCorrection.positive_power_threshold L u (1/2) hu (by norm_num)
  obtain ⟨ηv,hηv,_,hinczero⟩ := primitive_normal_threshold hb hblm (by norm_num : (0:ℝ) < 1/2) Dmap
  let ηold := min η (min η₀ (min ηn (min ηg ηB)))
  have hηold : 0 < ηold := lt_min hη (lt_min hη₀ (lt_min hηn (lt_min hηg hηB)))
  refine ⟨lp,b,u,min ηold (min ηs ηv),L,C+D,P 0+P R+Dmap,Dp,P,hb,hb16,hu,
    lt_min hηold (lt_min hηs hηv),
    (min_le_left _ _).trans ((min_le_left _ _).trans hη1),hL,add_nonneg hC hD,
    add_nonneg (add_nonneg (hP 0) (hP R)) hDmap,hDp,hblp,hP,?_⟩
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
  have hGQ : MapsTo (lowJet (data.A.jetChartMap i G)) S Q' :=
    hnear G hG (fun j => ((hclose j).mono_order (by omega)).mono_const
      (hsmall z hz (hzη.trans_le ((min_le_right _ _).trans (min_le_left _ _)))).le)
  have hGv : ∀ p ∈ S, p ∉ K → ∀ t,
      l.velocity (lowJet (data.A.jetChartMap i G) p,t) =
        SurfaceVelocityFamily.normal (lowJet (data.A.jetChartMap i G) p) := by
    intro p hp hpK t
    exact hv _ (hQ'O (hGQ hp)) (by simpa only [lowJetPosition_lowJet] using hpK) t
  obtain ⟨U,hzero,hUs,hrep,hinit,hVs,herror⟩ := hprimitive G hG hGQ K hK hKS hKA hGv
  let V := data.A.periodicAtlasAnsatz i G U ℓ (N+(R+2)+1) z
  have hjet := (hprofiles G hG ⟨z^b,hs.le⟩ hs hs1 hmap).2 i ((R+2)+(2*(N+(R+2)+1)+1))
  have hsolved : data.A.TensorWeightedBound z (R+2) (C*z^(N+(R+2)))
      (data.A.atlasPolynomialMetric (data.A.primitiveAtlasPolynomial i Pol) z G-g.inner) :=
    fun j => (hmean j).shrink_scale hz.le hz1
  have herr := (herror (z^b) z hz hzs hs1 hjet).2 g.inner g.contMDiff (C*z^(N+(R+2))) hsolved
  have htot : 0 ≤ C*z^(N+(R+2))+D*z^(N+(R+2)+1)/(z^b)^lm := by positivity
  have hfinal := data.A.tensorWeightedBound_unscaled hz hz1 htot herr
  have hincrement := (herror (z^b) z hz hzs hs1 hjet).1
  have hsmallinc : Dmap*z/(z^b)^lm ≤ Dmap := by
    apply (div_le_iff₀ (pow_pos hs _)).mpr
    exact mul_le_mul_of_nonneg_left (slow_power_dominates_fast hz hz1 hb hblm) hDmap
  have hGweighted := data.A.weighted_of_shifted_two hz.le hzs hs1 (hmap R)
  have hincweighted : data.A.WeightedBound z R Dmap (V-G) :=
    fun j => ((hincrement j).mono_order (by omega)).mono_const hsmallinc
  have hVweighted := data.A.weightedBound_add hG ((hVs z).sub hG) hz.le hGweighted hincweighted
  have hvadd : G+(V-G) = V := by abel
  change data.A.WeightedBound z R (P R+Dmap) (G+(V-G)) at hVweighted
  rw [hvadd] at hVweighted
  have hVweighted' : data.A.WeightedBound z R (P 0+P R+Dmap) V :=
    fun j => (hVweighted j).mono_const (by linarith [hP 0])
  have hshift := data.A.weighted_to_shifted (q := 2) (m := R) hz hz1
    (show 0 ≤ Dmap*z/(z^b)^lm by positivity)
    (show data.A.WeightedBound z (2+R) (Dmap*z/(z^b)^lm) (V-G) from by
      simpa only [V,Nat.add_comm R 2] using hincrement)
  have hshift' : data.A.ShiftedBound 2 R z (Dmap/z^2) (V-G) := by
    intro j k hk x
    exact (hshift j k hk x).trans (div_le_div_of_nonneg_right hsmallinc (sq_nonneg z))
  have hvmap := data.A.shifted_map_recurrence hG ((hVs z).sub hG)
    (hmap 0) (hmap R) hshift' hs hz.le hzs (hP 0) (hP R)
  change data.A.ShiftedBound 2 R z (P 0+(z/(z^b))*P R+Dmap/z^2) (G+(V-G)) at hvmap
  rw [hvadd] at hvmap
  have hvmap' : data.A.ShiftedBound 2 R z ((P 0+P R+Dmap)/z^2) V := by
    intro j k hk x
    exact (hvmap j k hk x).trans (primitive_shifted_budget hz hz1 hzs (hP 0) (hP R) hDmap)
  have hcoord : data.A.vectorChartRead i V =
      finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (data.A.jetChartMap i G q))
        U ℓ (N+(R+2)+1) z := by
    rw [data.A.euclidean_jetChartMap]
    funext q
    apply spaceCoordinates.injective
    exact congrFun (data.A.periodicAtlasAnsatz_coordinate i G U hK hKA hzero ℓ
      (N+(R+2)+1) z) q
  have hnall : ∀ p ∈ S,
      let H := SurfaceVelocityFamily.Loop.primitiveNormalTriple (data.A.vectorChartRead i V) p
      NormalFrame.gramDet (H 0) (H 1) ≠ 0 ∧
        c < ‖RealModes.realNormalPart (H 0) (H 1) (H 2)‖ := by
    rw [hcoord]
    exact hnormal (data.A.jetChartMap i G) (data.A.jetChartMap_smooth i hG) hGQ
      (z^b) z hz hzs hs1
      ((hprofiles G hG ⟨z^b,hs.le⟩ hs hs1 hmap).2 i ((2*(N+(R+2))+2)+2))
      (hnsmall z hz (hzη.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))) U hUs hrep hinit
  have hext : ∀ p ∉ tsupport (data.A.weight i), V =ᶠ[𝓝 p] G := by
    intro p hp
    exact data.A.periodicAtlasAnsatz_eventuallyEq i G U hK hKA hzero ℓ (N+(R+2)+1) z hp
  have hglobal := hgeometry G V hG (hVs z) (L*z^u) (by positivity)
    (hgsmall z hz (hzη.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))
    (fun j => (hclose j).mono_order (by omega)) (fun p hp => by
      have hpouter : p ∈ tsupport (data.A.outer i) := subset_tsupport _ (by
        change data.A.outer i p ≠ 0
        rw [data.A.outer_one i p hp]
        norm_num)
      have hh := hnall (chart (i : M) p) (houter ⟨p,hpouter,rfl⟩)
      exact ⟨hh.1,norm_pos_iff.mp (hc.trans hh.2)⟩) hext
  have hBglobal := hmargin G V hG (hVs z) hglobal.1 (L*z^u) (by positivity)
    (hBsmall z hz (hzη.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))))
    (fun j => (hclose j).mono_order (by omega)) (fun p hp => by
      have hpouter : p ∈ tsupport (data.A.outer i) := subset_tsupport _ (by
        change data.A.outer i p ≠ 0
        rw [data.A.outer_one i p hp]
        norm_num)
      have hh := hnall (chart (i : M) p) (houter ⟨p,hpouter,rfl⟩)
      exact data.A.secondTensor_margin_of_primitive_normal i (hVs z)
        (chart (i : M) p) hc hh.1 hh.2) hext
  have hFzero : data.A.WeightedBound 1 0 V₀ F := by
    intro j k hk x hx
    have hk0 : k = 0 := by omega
    subst k
    simpa only [one_pow,one_mul,iteratedFDerivWithin_univ] using hF₀ j 0 (by omega) x
  have hslow0 : data.A.WeightedBound 1 0 (1/2) (G-F) := fun j =>
    ((hclose j).mono_order (Nat.zero_le _)).mono_const (hslowzero z hz hzs0).le
  have hinc0 : data.A.WeightedBound 1 0 (1/2) (V-G) := by
    intro j k hk x hx
    have hk0 : k = 0 := by omega
    subst k
    have hh := hincrement j 0 (by omega) x hx
    simp only [pow_zero,one_mul] at hh ⊢
    exact hh.trans (hinczero z hz hzv0).le
  have hsum0 := data.A.weightedBound_add hF (hG.sub hF) zero_le_one hFzero hslow0
  have hsum1 := data.A.weightedBound_add (hF.add (hG.sub hF)) ((hVs z).sub hG)
    zero_le_one hsum0 hinc0
  have hVzero : data.A.WeightedBound 1 0 (V₀+1) V := by
    change data.A.WeightedBound 1 0 (V₀+1/2+1/2) (F+(G-F)+(V-G)) at hsum1
    have hsumid : F+(G-F)+(V-G) = V := by abel
    rw [hsumid] at hsum1
    convert hsum1 using 1; ring
  refine ⟨G,V,hG,hVs z,hclose,hmap,hVweighted',hVzero,hvmap',
    fun j => ((hfinal j).mono_order (by omega)).mono_const ?_,
    hglobal.1,hglobal.2,hBglobal,hnall,hext,?_⟩
  · have hlead : C*z^(N+(R+2))/z^(R+2) = C*z^N := by
      rw [pow_add,← mul_assoc,mul_div_cancel_right₀ _ (pow_ne_zero _ hz.ne')]
    rw [add_div,hlead]
    have htail := mul_le_mul_of_nonneg_left
      (primitive_tail_power_bound (N := N) (R := R+2) hz hz1 hb hblm) hD
    have heq : D*z^(N+(R+2)+1)/(z^b)^lm/z^(R+2) = D*(z^(N+(R+2)+1)/(z^b)^lm/z^(R+2)) := by ring
    rw [heq]
    calc
      C*z^N+D*(z^(N+(R+2)+1)/(z^b)^lm/z^(R+2)) ≤ C*z^N+D*z^N := add_le_add le_rfl htail
      _ = (C+D)*z^N := by ring

  · refine ⟨hG,fun p hp => hQ'O (hGQ hp),?_⟩
    intro p hp
    rw [hcoord]
    exact hprofile (data.A.jetChartMap i G) (data.A.jetChartMap_smooth i hG) hGQ
      (z^b) z hz hzs hs1
      ((hprofiles G hG ⟨z^b,hs.le⟩ hs hs1 hmap).2 i ((2*(N+(R+2))+2)+2))
      U hUs hrep hinit p hp

/-- The geometric consequence with profile bookkeeping erased. -/
theorem uniform_primitive_mean_realization (data : MetricGoodPhaseData g F)
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
    ∃ c cB V₀ : ℝ, 0 < c ∧ 0 < cB ∧ 0 ≤ V₀ ∧ ∀ R N : ℕ,
    ∃ (b u η L C Cv : ℝ) (P : ℕ → ℝ), 0 ≤ b ∧ b < 1/16 ∧ 0 < u ∧
      0 < η ∧ η ≤ 1 ∧ 0 ≤ L ∧ 0 ≤ C ∧ 0 ≤ Cv ∧ (∀ m, 0 ≤ P m) ∧
      ∀ z : ℝ, 0 < z → z < η → ∃ G V : M → Space,
        ContMDiff planeModel spaceModel ∞ G ∧ ContMDiff planeModel spaceModel ∞ V ∧
        data.A.WeightedBound 1 3 (L*z^u) (G-F) ∧
        (∀ m, data.A.ShiftedBound 2 m (z^b) (P m) G) ∧
        data.A.WeightedBound z R Cv V ∧
        data.A.WeightedBound 1 0 V₀ V ∧
        data.A.ShiftedBound 2 R z (Cv/z^2) V ∧
        data.A.TensorWeightedBound 1 R (C*z^N)
          (inducedTensor V-(g.inner+data.A.bundleRestore data.A.tensorTriv i
            (fun y => fiberFromThree ![a y^2,0,0]))) ∧
        (∀ p, Function.Injective (mfderiv planeModel spaceModel V p)) ∧
        (∀ p, ∃ v w : SmallModes.Base,
          RealModes.realSecondForm (coordinateMap V p) v w (coordinateCenter p) ≠ 0) ∧
        (∀ j x, x ∈ (modeSupport (data.A.chartWeightCompact j) : Set SmallModes.Base) →
          cB < ‖RealModes.realSecondTensor (spaceCoordinates ∘ data.A.vectorPlaneRead j V) x‖) ∧
        (∀ p ∈ S,
          let H := SurfaceVelocityFamily.Loop.primitiveNormalTriple (data.A.vectorChartRead i V) p
          NormalFrame.gramDet (H 0) (H 1) ≠ 0 ∧
            c < ‖RealModes.realNormalPart (H 0) (H 1) (H 2)‖) ∧
        ∀ p ∉ tsupport (data.A.weight i), V =ᶠ[𝓝 p] G := by
  obtain ⟨c,cB,V₀,hc,hcB,hV₀,hall⟩ := data.profiled_primitive_mean_realization
    hF hmetric i l ha hamp S T hST houter hQ hQO hFQ K hK hKS hKA hv ℓ hℓx hℓy
  refine ⟨c,cB,V₀,hc,hcB,hV₀,?_⟩
  intro R N
  obtain ⟨lp,b,u,η,L,C,Cv,Dp,P,hb,hb16,hu,hη,hη1,hL,hC,hCv,_,_,hP,hfamily⟩ := hall R N
  refine ⟨b,u,η,L,C,Cv,P,hb,hb16,hu,hη,hη1,hL,hC,hCv,hP,?_⟩
  intro z hz hzη
  obtain ⟨G,V,hG,hV,hclose,hmap,hvb,hv0,hshift,herr,himm,hB,hglobal,hlocal,hext,_⟩ := hfamily z hz hzη
  exact ⟨G,V,hG,hV,hclose,hmap,hvb,hv0,hshift,herr,himm,hB,hglobal,hlocal,hext⟩

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
