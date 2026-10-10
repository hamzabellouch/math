import OAI.Geometry.IsometricImmersion.Comparison.OriginalClassComparisonWithLow
import OAI.Geometry.IsometricImmersion.Comparison.ActualComparisonCoefficientData
import OAI.Geometry.IsometricImmersion.Comparison.ComparisonUpperVelocity
import OAI.Geometry.IsometricImmersion.Comparison.ActualComparisonTestCost
import OAI.Geometry.IsometricImmersion.Pulses.PulseScalarContradiction

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor SmoothLocal.Model

theorem exists_original_pulse_exclusion
    {g0 gStar : MetricField} {V : Set Coord}
    (hg0 : SmoothPositiveOn g0 V) (hgStar : SmoothPositiveOn gStar V)
    (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {kappa q0 : ℝ} (M : ℕ) (hkappa : 0 < kappa) (hM : 0 < M)
    (hq0 : |q0| ≤ 1/20)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p=modelCurvature kappa p) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ boundedClassWidth kappa M*r ≤ 1/20 ∧
      ∀ N : ℕ, 10 < N → ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1/2 ∧
        ∀ᶠ tau : ℕ in atTop,
          ∀ (eta : metricPatchSet g0 kappa) (z : Coord → ℝ),
            BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
            |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤
              1/(100*boundedClassWidth kappa M) →
            ¬ (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
                testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                  metricApproximationAccuracy tau) := by
  obtain ⟨G,d,r,hG,hd,hr,hrhalf,hGstar,hdstar,hlow,hLr,hrsmall,hcuts,hcomparison⟩ :=
    exists_original_class_comparison_with_low_data hg0 hgStar hV hSV M hkappa hM hq0 hbackground
  have hGstar2 : ∀ i j k, k ≤ 2 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G :=
    fun i j k hk p hp => hGstar i j k (by omega) p hp
  let L := boundedClassWidth kappa M
  let a := L*r/16
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hLrpos : 0 < L*r := mul_pos hL hr
  have ha : 0 < a := div_pos hLrpos (by norm_num)
  have haHalf : a ≤ L*r/2 := by dsimp only [a]; linarith
  have haI : a < L*r := by dsimp only [a]; linarith
  have hminv : 0 < 1/(M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  have hxxfloor : 0 < (boundedClassSpeed kappa M)^2/(4*(M : ℝ)) :=
    div_pos (sq_pos_of_pos (boundedClassSpeed_pos hkappa hM)) (mul_pos (by norm_num) (Nat.cast_pos.mpr hM))
  refine ⟨r,hr,hrhalf,hLr,?_⟩
  intro N hN
  obtain ⟨C,Csource,Cgradient,c3,_hC,_hCsource,hCgradient,hc3,hPfinite,hcomparisonN⟩ := hcomparison N hN
  obtain ⟨K,K1,hK,hK1,hcoefficients⟩ := exists_actual_comparison_coefficient_data_at_radius
    hgStar hV hSV M hG.le hd hGstar2 hdstar hkappa hM hq0 hr hrhalf hLr hrsmall N (by omega)
  obtain ⟨CPseg,Aseg,_hCPseg,_hAseg,hsegments⟩ := exists_actual_reference_segment_at_radius
    hgStar hV hSV M hG.le hd hGstar2 hdstar hkappa hM hq0 hr hrhalf hLr hrsmall N (by omega)
  obtain ⟨BZ,hBZ,hZcuts⟩ := hcuts N
  obtain ⟨BP,hBP,hPjets⟩ := hPfinite (N+1)
  let E := (2*a)*cutoffEdgeDerivativeBound a ha N (BZ+BP)
  let C0 := 4*pulseTestDerivativeBound a ha*K*Real.sqrt (2*a)*Cgradient
  let C1 := 4*axisBumpDerivativeBound a ha 0*(K1+K)*Real.sqrt (2*a)*Cgradient
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hC0 : 0 ≤ C0 := by
    dsimp only [C0]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (pulseTestDerivativeBound_nonneg ha)) hK0) (Real.sqrt_nonneg _)) hCgradient
  obtain ⟨delta,hdelt,hdhalf,hcontradict⟩ := exists_delta_then_frequency_for_moment_contradiction hc3 hC0 N
  obtain ⟨T,_hT,hcontradictT⟩ := hcontradict E C1
  refine ⟨delta,hdelt,hdhalf,?_⟩
  have hlarge : ∀ᶠ tau : ℕ in atTop, T ≤ (tau : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop T)
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [hcomparisonN delta hdelt hdhalf,hlow a ha N hN delta,
    hZcuts N hN delta hdelt,hPjets delta hdelt hdhalf,hcoefficients delta hdelt hdhalf,
    hsegments delta hdelt hdhalf,hlarge,hwidth]
    with tau hcomparisonTau hlowTau hZcutsTau hPjetsTau hcoeffTau hsegmentsTau ht hw
  intro eta z hclass hcenter happ
  let g := perturbedMetric g0 eta.val
  obtain ⟨U,hU,hSU,hUV,_hg0U,hgU,hh⟩ := bounded_class_actual_cap_data hg0 hV hSV eta hclass
  obtain ⟨hg8,hdet⟩ := hlowTau g U hgU hU hSU happ
  have hg4 : ∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G := fun i j k hk p hp => hg8 i j k (by omega) p hp
  have hmodel : ∀ p ∈ U, gaussianCurvature g0 p=modelCurvature kappa p := fun p hp => hbackground p (hUV hp)
  obtain ⟨W,Y,hf⟩ := exists_capInductionFlow hgU hU hSU hG.le (Nat.cast_nonneg M)
    hd hminv hminv hg8 hdet hh hkappa hmodel (perturbationTensor_tsupport_subset eta.val) eta.property.2
  let zs := heightInShearCoordinates z q0
  let gs := metricInShearCoordinates gStar q0
  let gt := metricInShearCoordinates g q0
  let P := taylorApproximation gs (-delta/(tau : ℝ))
    (heightCauchyValue zs (-delta/(tau : ℝ))) (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
  let I := Ioo (-(L*r)) (L*r)
  let Us := inverseShearCoordinates q0 ⁻¹' U
  let D := Us ∩ spatialStrip I
  let S := pulseStrip a delta (tau : ℝ)
  have hUs : IsOpen Us := shearedModelDomain_isOpen hU q0
  have hD : IsOpen D := hUs.inter (spatialStrip_isOpen isOpen_Ioo)
  have htpos : (0 : ℝ) < tau := zero_lt_one.trans_le hw.1
  have hbr : delta/(tau : ℝ) ≤ r := by
    have heq : delta/(tau : ℝ)=2*(delta/(2*(tau : ℝ))) := by ring
    rw [heq]
    linarith [hw.2]
  have htime0 : 0 ≤ delta/(tau : ℝ) := div_nonneg hdelt.le htpos.le
  have hpointEq (x t : ℝ) : boxPoint x t = (![x,t] : Coord) := pulse_boxPoint_eq x t
  have hsubset : S ⊆ pulseStrip (L*r/2) delta (tau : ℝ) := by
    intro p hp
    exact ⟨⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩,hp.2⟩
  have hcoordinates (p : Coord) (hp : p ∈ S) : |p 0| ≤ L*r ∧ |p 1| ≤ r :=
    ⟨(abs_le.mpr hp.1).trans haI.le,(abs_le.mpr hp.2).trans hbr⟩
  have hgeom (p : Coord) (hp : p ∈ S) := actual_central_sheared_solution_margins
    eta hclass hG.le hd hkappa hr.le hLr hq0 hrsmall hg4 hdet hcenter
      (hcoordinates p hp).1 (hcoordinates p hp).2
  have hpS (p : Coord) (hp : p ∈ S) : inverseShearCoordinates q0 p ∈ modelSquare := (hgeom p hp).1
  have hSD : S ⊆ D := by
    intro p hp
    exact ⟨hSU (hpS p hp),⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩⟩
  have hgStarU : SmoothPositiveOn gStar U :=
    ⟨fun i j => (hgStar.1 i j).mono hUV,fun p hp => hgStar.2 p (hUV hp)⟩
  have hgsUs := metricInShearCoordinates_smoothPositive hgStarU q0
  have hgtUs := metricInShearCoordinates_smoothPositive hgU q0
  have hgsD : SmoothPositiveOn gs D :=
    ⟨fun i j => (hgsUs.1 i j).mono inter_subset_left,fun p hp => hgsUs.2 p hp.1⟩
  have hgtD : SmoothPositiveOn gt D :=
    ⟨fun i j => (hgtUs.1 i j).mono inter_subset_left,fun p hp => hgtUs.2 p hp.1⟩
  have hzsUs := heightInShearCoordinates_contDiffOn hh.smooth q0
  have hzsD : ContDiffOn ℝ ∞ zs D := hzsUs.mono inter_subset_left
  obtain ⟨hP,hCauchy,_hdegree,_hres,_hresc,_hresm,_hsource,hgradient,_hsourcec,hpositive⟩ :=
    hcomparisonTau eta z hclass hcenter happ
  have hPD : ContDiffOn ℝ ∞ P D := hP.mono inter_subset_right
  have hcoeff := hcoeffTau g0 eta U W z Y hgU hU hh hf hclass hg4 hdet hcenter happ
  have hsegments := (hsegmentsTau g0 eta U W z Y hgU hU hh hf hclass hg4 hdet hcenter happ).2.2
  have hseg (p : Coord) (hp : p ∈ S) (sigma : ℝ) (hsigma : sigma ∈ Icc (0 : ℝ) 1) :
      qHeightJetSegment P zs sigma p ∈ darbouxQStateDomain gs D := by
    exact ⟨by simpa only [statePoint_qHeightJetSegment] using hSD hp,
      abs_pos.mp (hxxfloor.trans_le (hsegments p (hsubset hp) sigma hsigma).1)⟩
  have hcut (x : ℝ) (hx : x ∈ I) (t : ℝ) (ht : |t| ≤ r) : (![x,t] : Coord) ∈ D := by
    refine ⟨hSU ?_,hx⟩
    apply sectionFourClosedSlab_mem_shearedModelSquare hr hrhalf hLr hq0
    exact ⟨abs_le.mpr ⟨hx.1.le,hx.2.le⟩,ht⟩
  have hinitial (x : ℝ) (hx : x ∈ Icc (-a) a) :
      coordPartial 1 (comparisonDifference P zs) (boxPoint x (-(delta/(tau : ℝ))))=0 := by
    have hxI : x ∈ I := ⟨by linarith [hx.1],by linarith [hx.2]⟩
    have ht0 : |-(delta/(tau : ℝ))| ≤ r := by rw [abs_neg,abs_of_nonneg htime0]; exact hbr
    have hpD : boxPoint x (-(delta/(tau : ℝ))) ∈ D := by rw [hpointEq]; exact hcut x hxI _ ht0
    have hs := CoordinateBound.iterated_sub hzsD hPD hD [1] hpD
    change coordPartial 1 (comparisonDifference P zs) (boxPoint x (-(delta/(tau : ℝ)))) =
      coordPartial 1 zs (boxPoint x (-(delta/(tau : ℝ))))-
        coordPartial 1 P (boxPoint x (-(delta/(tau : ℝ)))) at hs
    have he := (hCauchy x hxI).2
    change coordPartial 1 P ![x,-delta/(tau : ℝ)] =
      coordPartial 1 zs ![x,-delta/(tau : ℝ)] at he
    rw [neg_div] at he
    rw [hpointEq,he,sub_self] at hs
    simpa only [hpointEq] using hs
  have hPjetsActual := hPjetsTau eta z hclass hcenter happ
  have hZcutsActual := hZcutsTau eta z hclass hcenter happ
  have hedge (n : ℕ) (hn : n ≤ N) (x : ℝ) (hx : x ∈ Icc (-a) a) :
      ‖iteratedFDeriv ℝ n (heightCauchyVelocity (comparisonDifference P zs) (delta/(tau : ℝ))) x‖ ≤ BZ+BP := by
    have hxI : x ∈ I := ⟨by linarith [hx.1],by linarith [hx.2]⟩
    have hxhalf : |x| ≤ L*r/2 := (abs_le.mpr hx).trans haHalf
    have hPcut := upper_cauchy_jets_of_actual_coordinate_bound hPjetsActual.1
      (show L*r/2<L*r by linarith) htime0 hPjetsActual.2.2 hxhalf n hn
    have hzcut := (hZcutsActual x hxhalf n hn).2.2
    apply comparison_upper_velocity_jet_bound hD isOpen_Ioo hPD hzsD (delta/(tau : ℝ))
      (fun y hy => hcut y hy _ (by rw [abs_of_nonneg htime0]; exact hbr)) hxI n hzcut hPcut.2
  have hcost := actual_comparison_source_test_cost ha hdelt.le hw.1 hK0 hK1 hCgradient
    (add_nonneg hBZ hBP) hgtD hgsD hD hzsD hPD hSD
    (fun p hp => (hgeom p hp).2.2.2.2.2.1)
    (fun p hp => abs_pos.mp ((boundedClassShearHxxFloor_pos hkappa hM).trans_le (hgeom p hp).2.1))
    hseg (fun i p hp => (hcoeff i p (hsubset hp)).1)
    (fun i p hp => (hcoeff i p (hsubset hp)).2) hgradient hinitial hedge
  change |pulseWeightedMoment a delta (tau : ℝ) (actualComparisonSource gStar g z q0 P)| ≤
    E/(tau : ℝ)^N+C0*delta^2*(tau : ℝ)/(tau : ℝ)^N+C1*delta^2/(tau : ℝ)^N at hcost
  exact hcontradictT (tau : ℝ) ht
    (pulseWeightedMoment a delta (tau : ℝ) (actualComparisonSource gStar g z q0 P)) hpositive hcost

end SmoothLocal.Perturbation

end

end OAI
