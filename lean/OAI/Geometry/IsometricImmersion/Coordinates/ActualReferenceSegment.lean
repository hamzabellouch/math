import OAI.Geometry.IsometricImmersion.Coordinates.ActualCentralShearMargins
import OAI.Geometry.IsometricImmersion.Pulses.ActualPulseMetricCloseness
import OAI.Geometry.IsometricImmersion.Taylor.ActualTaylorFiniteJets
import OAI.Geometry.IsometricImmersion.Darboux.QClosedStripMargins
import OAI.Geometry.IsometricImmersion.Pulses.QReferenceForcingMargins

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_reference_segment_at_radius
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 r : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hgStarB : ∀ i j k, k ≤ 2 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G)
    (hdStar : ∀ p ∈ modelSquare, d ≤ (gStar p).det)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20)
    (hr : 0 < r) (hrhalf : r < 1/2) (hLr : boundedClassWidth kappa M*r ≤ 1/20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
      (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M))
    (N : ℕ) (hN : 2 < N) :
    ∃ C A : ℝ, 0 ≤ C ∧ 1 ≤ A ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 →
      ∀ᶠ tau : ℕ in atTop,
        ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa) (U W : Set Coord)
          (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
          SmoothPositiveOn (perturbedMetric g0 eta.val) U → IsOpen U →
          CapInductionHeight (perturbedMetric g0 eta.val) U (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) z →
          CapInductionFlow (perturbedMetric g0 eta.val) U G (M : ℝ) d (1/(M : ℝ)) (1/(M : ℝ)) kappa z Y W →
          BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
          (∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j) p‖ ≤ G) →
          (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
          |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
              testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                metricApproximationAccuracy tau) →
          let zs := heightInShearCoordinates z q0
          let gs := metricInShearCoordinates gStar q0
          let P := taylorApproximation gs (-delta/(tau : ℝ))
            (heightCauchyValue zs (-delta/(tau : ℝ)))
            (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
          ContDiffOn ℝ ∞ P (spatialStrip (Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r))) ∧
          CoordinateBound P (pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ)) 3 C ∧
          (∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
            ∀ sigma ∈ Icc (0 : ℝ) 1,
              (boundedClassSpeed kappa M)^2/(4*(M : ℝ)) ≤
                |stateQDenominator gs (qHeightJetSegment P zs sigma p)| ∧
              |stateQDenominator gs (qHeightJetSegment P zs sigma p)| ≤ A ∧
              (1/(M : ℝ))/2 ≤ stateEnergy gs (qHeightJetSegment P zs sigma p) ∧
              ((((boundedClassSpeed kappa M)^2/(2*(M : ℝ)))*(1/(M : ℝ)))/2)/A^2 ≤
                qFirstCoefficient gs 5 (qHeightJetSegment P zs sigma p) ∧
              (((kappa/2)/2)*((1/(M : ℝ))/2))/A^2 ≤
                (qFirstCoefficient gs 4 (qHeightJetSegment P zs sigma p)/2)^2+
                  qFirstCoefficient gs 5 (qHeightJetSegment P zs sigma p)) := by
  let L := boundedClassWidth kappa M
  let Z := (2*(1+|q0|))^3*(M : ℝ)
  let nu := (boundedClassSpeed kappa M)^2/(2*(M : ℝ))
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hnu : 0 < nu := boundedClassShearHxxFloor_pos hkappa hM
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hminv : 0 < 1/(M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  have hq1 : |q0| ≤ 1 := hq0.trans (by norm_num)
  have ha : 0 < L*r/16 := div_pos (mul_pos hL hr) (by norm_num)
  obtain ⟨C,hC,hPjets⟩ := exists_actual_taylor_finite_jets_at_radius
    hgStar hV hSV M hG hd hkappa hM hq0 hr hrhalf hLr hrsmall N 3
  obtain ⟨epsilon,A,hepsilon,hA,htransfer⟩ := exists_uniform_Q_closed_strip_margins
    (16*G) 1 Z C (mul_nonneg (by norm_num) hG) (by norm_num) hZ hC
      hd hnu hminv hminv (half_pos hkappa)
  obtain ⟨tauRef,htauRef,hfloor⟩ := exists_bounded_patch_reference_initial_floor
    G kappa d q0 M hG hkappa hd hM hq0
  refine ⟨C,A,hC,hA,?_⟩
  intro delta hdelt hdhalf
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  have hlarge : ∀ᶠ tau : ℕ in atTop, 2*delta*(Z+C)/epsilon ≤ (tau : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop _)
  filter_upwards [hPjets delta hdelt hdhalf,hwidth,hlarge,eventually_ge_atTop tauRef,
    actual_sheared_metric_finite_reference_closeness hgStar hV hSV hq1 ha 2 N hN hepsilon delta]
    with tau hPtau hw htlarge htRef hclose
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let g := perturbedMetric g0 eta.val
  let gs := metricInShearCoordinates gStar q0
  let gt := metricInShearCoordinates g q0
  let zs := heightInShearCoordinates z q0
  let a := -delta/(tau : ℝ)
  let b := delta/(tau : ℝ)
  let I := Ioo (-(L*r)) (L*r)
  let P := taylorApproximation gs a (heightCauchyValue zs a) (heightCauchyVelocity zs a) N
  let S := closedRectangle (-(L*r/2)) (L*r/2) a b
  have hSP : S = pulseStrip (L*r/2) delta (tau : ℝ) := by
    simp only [S,pulseStrip,a,b,neg_div]
  let Us := inverseShearCoordinates q0 ⁻¹' U
  let Vs := inverseShearCoordinates q0 ⁻¹' V
  let D := (Us ∩ Vs) ∩ spatialStrip I
  have hUs : IsOpen Us := shearedModelDomain_isOpen hU q0
  have hVs : IsOpen Vs := shearedModelDomain_isOpen hV q0
  have hD : IsOpen D := (hUs.inter hVs).inter (spatialStrip_isOpen isOpen_Ioo)
  have hSU : modelSquare ⊆ U := hf.squareSubset.trans hf.domainSubset
  have htpos : (0 : ℝ) < tau := zero_lt_one.trans_le hw.1
  have hbnonneg : 0 ≤ b := div_nonneg hdelt.le htpos.le
  have hab : a ≤ b := by
    dsimp only [a,b]
    rw [neg_div]
    exact neg_le_self hbnonneg
  have hbr : b ≤ r := by
    have he : delta/(tau : ℝ)=2*(delta/(2*(tau : ℝ))) := by ring
    dsimp only [b]
    rw [he]
    linarith [hw.2]
  have haabs : |a| ≤ r := by
    dsimp only [a]
    rw [abs_div,abs_neg,abs_of_pos hdelt,abs_of_pos htpos]
    exact hbr
  have hLrpos : 0 < L*r := mul_pos hL hr
  have hhr : r ≤ 1/20 := by
    have hL1 : 1 ≤ L := (by norm_num : (1 : ℝ) ≤ 100).trans (boundedClassWidth_ge_hundred kappa M)
    have hh : r ≤ L*r := by nlinarith
    exact hh.trans hLr
  have hcoordinates (p : Coord) (hp : p ∈ S) : |p 0| ≤ L*r ∧ |p 1| ≤ r := by
    have hx : |p 0| ≤ L*r/2 := abs_le.mpr hp.1
    have ht : |p 1| ≤ b := abs_le.mpr
      ⟨by simpa only [a,b,neg_div] using hp.2.1,hp.2.2⟩
    exact ⟨hx.trans (by linarith),ht.trans hbr⟩
  have hgeom (p : Coord) (hp : p ∈ S) := actual_central_sheared_solution_margins
    eta hclass hG hd hkappa hr.le hLr hq0 hrsmall hgB hdet hcenter
      (hcoordinates p hp).1 (hcoordinates p hp).2
  have hpS (p : Coord) (hp : p ∈ S) : inverseShearCoordinates q0 p ∈ modelSquare := (hgeom p hp).1
  have hbox : S ⊆ D := by
    intro p hp
    refine ⟨⟨hSU (hpS p hp),hSV (hpS p hp)⟩,?_⟩
    exact ⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩
  have hpoint (p : Coord) (hp : p ∈ S) : ‖p‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    fin_cases i
    · exact (hcoordinates p hp).1.trans (hLr.trans (by norm_num))
    · exact (hcoordinates p hp).2.trans (hhr.trans (by norm_num))
  have hgtUs : SmoothPositiveOn gt Us := metricInShearCoordinates_smoothPositive hg q0
  have hgsVs : SmoothPositiveOn gs Vs := metricInShearCoordinates_smoothPositive hgStar q0
  have hgtD : SmoothPositiveOn gt D :=
    ⟨fun i j => (hgtUs.1 i j).mono (fun _ hp => hp.1.1),fun p hp => hgtUs.2 p hp.1.1⟩
  have hgsD : SmoothPositiveOn gs D :=
    ⟨fun i j => (hgsVs.1 i j).mono (fun _ hp => hp.1.2),fun p hp => hgsVs.2 p hp.1.2⟩
  have hzsUs : ContDiffOn ℝ ∞ zs Us := heightInShearCoordinates_contDiffOn hh.smooth q0
  have hzsD := hzsUs.mono (show D ⊆ Us from fun _ hp => hp.1.1)
  obtain ⟨hP,_hPfull,hPBpulse⟩ := hPtau g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have hPB : CoordinateBound P S 3 C := by rw [hSP]; exact hPBpulse
  have hPD : ContDiffOn ℝ ∞ P D := hP.mono inter_subset_right
  have hzB : CoordinateBound zs S 3 Z := bounded_class_sheared_C3_on_actual_region hclass q0 hpS
  have htwo (g1 : MetricField) (U1 : Set Coord) (hg1 : SmoothPositiveOn g1 U1)
      (hU1 : IsOpen U1) (hSU1 : modelSquare ⊆ U1)
      (hB1 : ∀ i j k, k ≤ 2 → ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => g1 q i j) p‖ ≤ G)
      (i j : Fin 2) (k : ℕ) (hk : k ≤ 2) (p : Coord) (hp : p ∈ S) :
      ‖iteratedFDeriv ℝ k (fun q => metricInShearCoordinates g1 q0 q i j) p‖ ≤ 16*G := by
    apply (sheared_metric_full_jet_bound hg1.1 hU1 hq1 hG (hSU1 (hpS p hp)) k
      (fun l m => hB1 l m k hk _ (hpS p hp)) i j).trans
    have he : (2 : ℝ)^k ≤ 4 := by
      exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk).trans (by norm_num)
    nlinarith
  have hg2 := htwo g U hg hU hSU (fun i j k hk => hgB i j k (by omega))
  have hgs2 := htwo gStar V hgStar hV hSV hgStarB
  have hdetT (p : Coord) (hp : p ∈ S) : d ≤ |(gt p).det| := by
    rw [metricDet_in_shear_coordinates]
    exact hdet _ (hpS p hp)
  have hdetR (p : Coord) (hp : p ∈ S) : d ≤ |(gs p).det| := by
    rw [metricDet_in_shear_coordinates]
    exact (hdStar _ (hpS p hp)).trans (le_abs_self _)
  have hmetric (i j : Fin 2) (k : ℕ) (hk : k ≤ 2) (p : Coord) (hp : p ∈ S) :
      ‖iteratedFDeriv ℝ k (fun q => gs q i j-gt q i j) p‖ ≤ epsilon :=
    hclose.2.2 g U hg hU hSU happ i j k hk p (hpS p hp)
  have hduration : (Z+C)*(b-a) ≤ epsilon := by
    have hh := (div_le_iff₀ hepsilon).mp htlarge
    have he : (Z+C)*(b-a)=(2*delta*(Z+C))/(tau : ℝ) := by dsimp only [a,b]; ring
    rw [he]
    apply (div_le_iff₀ htpos).mpr
    nlinarith
  have hcutS (x : ℝ) (hx : x ∈ I) : inverseShearCoordinates q0 ![x,a] ∈ modelSquare := by
    apply sectionFourClosedSlab_mem_shearedModelSquare hr hrhalf hLr hq0
    exact ⟨abs_le.mpr ⟨hx.1.le,hx.2.le⟩,haabs⟩
  have hcutU (x : ℝ) (hx : x ∈ I) : (![x,a] : Coord) ∈ Us := hSU (hcutS x hx)
  have h0 := heightCauchyValue_contDiffOn hzsUs a hcutU
  have h1 := heightCauchyVelocity_contDiffOn hzsUs hUs a hcutU
  have hden := hfloor g0 gStar V eta z r N delta tau hgStar hV hSV hclass hr hLr hrsmall
    hgB hdet hcenter hdelt htRef hbr happ
  have hxx0 : ∀ x ∈ I, covHessian gs (linearCauchy a (heightCauchyValue zs a)
      (heightCauchyVelocity zs a)) ![x,a] 0 0 ≠ 0 := by
    intro x hx hzero
    have hh := hden x hx
    rw [hzero,abs_zero] at hh
    have hc : 0 < (boundedClassSpeed kappa M)^2/(4*(M : ℝ)) := by
      have he : (boundedClassSpeed kappa M)^2/(4*(M : ℝ))=nu/2 := by dsimp only [nu]; ring
      rw [he]
      exact half_pos hnu
    linarith
  have hjet0 := (taylorApproximation_properties hgsVs hVs isOpen_Ioo h0 h1 a
    (fun x hx => hSV (hcutS x hx)) hxx0 N).2.1
  have hinitial (x : ℝ) (hx : x ∈ Icc (-(L*r/2)) (L*r/2)) :
      qSolutionJet P (boxPoint x a)=qSolutionJet zs (boxPoint x a) := by
    have hxI : x ∈ I := ⟨by linarith [hx.1],by linarith [hx.2]⟩
    have he : boxPoint x a = (![x,a] : Coord) := by
      ext i
      fin_cases i <;> simp [boxPoint]
    rw [he]
    exact (hjet0 x hxI).trans (linearCauchy_height_initial_state hzsUs hUs (-(L*r)) (L*r) a hcutU hxI)
  have hresult := htransfer gt gs zs P D hgtD hgsD hD hzsD hPD
    (-(L*r/2)) (L*r/2) a b hab hbox hpoint hg2 hgs2 hzB hPB hdetT hdetR hmetric hduration hinitial
    (fun p hp => (hgeom p hp).2.1) (fun p hp => (hgeom p hp).2.2.1)
    (fun p hp => (hgeom p hp).2.2.2.1) (fun p hp => (hgeom p hp).2.2.2.2.1)
    (fun p hp => (hgeom p hp).2.2.2.2.2.1) (fun p hp => (hgeom p hp).2.2.2.2.2.2)
  refine ⟨hP,hPBpulse,?_⟩
  intro p hp sigma hsigma
  have hpS' : p ∈ S := by rw [hSP]; exact hp
  have hm := (hresult (p 0) hpS'.1 (p 1) hpS'.2).1 sigma hsigma
  have he : boxPoint (p 0) (p 1)=p := by ext i; fin_cases i <;> simp [boxPoint]
  have hhalf : nu/2=(boundedClassSpeed kappa M)^2/(4*(M : ℝ)) := by dsimp only [nu]; ring
  simpa only [he,hhalf] using hm

end SmoothLocal.Perturbation

end

end OAI
