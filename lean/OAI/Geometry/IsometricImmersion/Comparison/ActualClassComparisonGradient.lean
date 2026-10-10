import OAI.Geometry.IsometricImmersion.Metrics.SmoothMetricRestriction
import OAI.Geometry.IsometricImmersion.Coordinates.ActualReferenceSegment
import OAI.Geometry.IsometricImmersion.Comparison.ActualComparisonGradient
import OAI.Geometry.IsometricImmersion.Comparison.ComparisonPulseGeometry
import OAI.Geometry.IsometricImmersion.Taylor.TaylorInitialVelocity

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_class_comparison_gradient_from_source
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
    ∃ Cgradient : ℝ, 0 ≤ Cgradient ∧
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
          ∀ F : ℝ, 0 ≤ F →
            (∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
              |actualComparisonSource gStar (perturbedMetric g0 eta.val) z q0 P p| ≤ F) →
            ∀ theta ∈ Icc (-(delta/(tau : ℝ))) (delta/(tau : ℝ)), ∀ i : Fin 2,
              Real.sqrt (∫ x in Icc (-(boundedClassWidth kappa M*r/16)) (boundedClassWidth kappa M*r/16),
                (coordPartial i (comparisonDifference P zs) (boxPoint x theta))^2) ≤
                Cgradient*F*delta/(tau : ℝ) := by
  let L := boundedClassWidth kappa M
  let Z := (2*(1+|q0|))^3*(M : ℝ)
  let nu := (boundedClassSpeed kappa M)^2/(2*(M : ℝ))
  let gs := metricInShearCoordinates gStar q0
  let Vs := inverseShearCoordinates q0 ⁻¹' V
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hLrpos : 0 < L*r := mul_pos hL hr
  have hnu : 0 < nu := boundedClassShearHxxFloor_pos hkappa hM
  have hminv : 0 < 1/(M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  obtain ⟨CP,A,_,hA,hsegment⟩ := exists_actual_reference_segment_at_radius
    hgStar hV hSV M hG hd hgStarB hdStar hkappa hM hq0 hr hrhalf hLr hrsmall N hN
  let s0 := ((nu*(1/(M : ℝ)))/2)/A^2
  have hs0 : 0 < s0 := div_pos (half_pos (mul_pos hnu hminv))
    (sq_pos_of_pos (zero_lt_one.trans_le hA))
  have hgs : SmoothPositiveOn gs Vs := metricInShearCoordinates_smoothPositive hgStar q0
  have hVs : IsOpen Vs := shearedModelDomain_isOpen hV q0
  obtain ⟨CE,hCE,hgradient⟩ := exists_actual_comparison_gradient hgs hVs
    (shearedModelSquare_isCompact q0) (shearedModelSquare_subset_domain hSV q0)
    1 CP Z (by norm_num) (half_pos hnu) hs0
  let speed := comparisonEnergySpeed CE
  let rate := comparisonEnergyRate CE CP Z s0
  let Cgradient := 2*Real.exp 1*Real.sqrt (2*(1+1/s0))*Real.sqrt (2*(L*r/4))
  have hs : 0 ≤ speed := add_nonneg (zero_le_one.trans hCE) (Real.sqrt_nonneg _)
  have hCg : 0 ≤ Cgradient := by dsimp [Cgradient]; positivity
  refine ⟨Cgradient,hCg,?_⟩
  intro delta hdelt hdhalf
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  have hlarge : ∀ᶠ tau : ℕ in atTop, rate*(2*delta) ≤ (tau : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop _)
  have hpulse : 0 < L*r/16 := div_pos hLrpos (by norm_num : (0 : ℝ) < 16)
  filter_upwards [hsegment delta hdelt hdhalf,hwidth,hlarge,
    comparison_pulse_geometry_eventually hpulse hs delta hdelt.le]
    with tau hsegTau hw hrateTau htravel
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let g := perturbedMetric g0 eta.val
  let gt := metricInShearCoordinates g q0
  let zs := heightInShearCoordinates z q0
  let a := -delta/(tau : ℝ)
  let b := delta/(tau : ℝ)
  let I := Ioo (-(L*r)) (L*r)
  let P := taylorApproximation gs a (heightCauchyValue zs a) (heightCauchyVelocity zs a) N
  let T := closedRectangle (-(L*r/2)) (L*r/2) a b
  have hTP : T = pulseStrip (L*r/2) delta (tau : ℝ) := by
    simp only [T,pulseStrip,a,b,neg_div]
  let Us := inverseShearCoordinates q0 ⁻¹' U
  let D := (Us ∩ Vs) ∩ spatialStrip I
  have hUs : IsOpen Us := shearedModelDomain_isOpen hU q0
  have hD : IsOpen D := (hUs.inter hVs).inter (spatialStrip_isOpen isOpen_Ioo)
  have hSU : modelSquare ⊆ U := hf.squareSubset.trans hf.domainSubset
  have htpos : (0 : ℝ) < tau := zero_lt_one.trans_le hw.1
  have hbnonneg : 0 ≤ b := div_nonneg hdelt.le htpos.le
  have hab : a ≤ b := by dsimp only [a,b]; simp only [neg_div]; linarith
  have hbr : b ≤ r := by
    have he : delta/(tau : ℝ)=2*(delta/(2*(tau : ℝ))) := by ring
    dsimp only [b]
    rw [he]
    linarith [hw.2]
  have hcoordinates (p : Coord) (hp : p ∈ T) : |p 0| ≤ L*r ∧ |p 1| ≤ r := by
    have hx : |p 0| ≤ L*r/2 := abs_le.mpr hp.1
    have ht : |p 1| ≤ b := abs_le.mpr
      ⟨by simpa only [a,b,neg_div] using hp.2.1,hp.2.2⟩
    exact ⟨hx.trans (by linarith),ht.trans hbr⟩
  have hgeom (p : Coord) (hp : p ∈ T) := actual_central_sheared_solution_margins
    eta hclass hG hd hkappa hr.le hLr hq0 hrsmall hgB hdet hcenter
      (hcoordinates p hp).1 (hcoordinates p hp).2
  have hpS (p : Coord) (hp : p ∈ T) : inverseShearCoordinates q0 p ∈ modelSquare := (hgeom p hp).1
  have hbox : T ⊆ D := by
    intro p hp
    exact ⟨⟨hSU (hpS p hp),hSV (hpS p hp)⟩,
      ⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩⟩
  have hpoint (p : Coord) (hp : p ∈ T) : ‖p‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    fin_cases i
    · change |p 0| ≤ 1
      exact (hcoordinates p hp).1.trans (hLr.trans (by norm_num))
    · change |p 1| ≤ 1
      exact (hcoordinates p hp).2.trans (by linarith)
  have hgt : SmoothPositiveOn gt D :=
    (metricInShearCoordinates_smoothPositive hg q0).mono (fun p hp => hp.1.1)
  have hzsUs : ContDiffOn ℝ ∞ zs Us := heightInShearCoordinates_contDiffOn hh.smooth q0
  have hzsD : ContDiffOn ℝ ∞ zs D := hzsUs.mono (fun p hp => hp.1.1)
  obtain ⟨hP,hPB,hsegActual⟩ := hsegTau g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have hPD : ContDiffOn ℝ ∞ P D := hP.mono inter_subset_right
  have hzB : CoordinateBound zs T 3 Z := bounded_class_sheared_C3_on_actual_region hclass q0 hpS
  have hPB' : CoordinateBound P T 3 CP := by rw [hTP]; exact hPB
  have hCauchy := actual_taylor_Cauchy_of_smooth gs zs a N isOpen_Ioo hP
  have hpointEq (x t : ℝ) : boxPoint x t=(![x,t] : Coord) := by
    ext i
    fin_cases i
    · change x*1+t*0=x
      ring
    · change x*0+t*1=t
      ring
  have hvalue (x : ℝ) (hx : x ∈ Ioo (-(L*r/2)) (L*r/2)) :
      P (boxPoint x a)=zs (boxPoint x a) := by
    rw [hpointEq]
    exact (hCauchy x ⟨by linarith [hx.1],by linarith [hx.2]⟩).1
  have hvelocity (x : ℝ) (hx : x ∈ Ioo (-(L*r/2)) (L*r/2)) :
      coordPartial 1 P (boxPoint x a)=coordPartial 1 zs (boxPoint x a) := by
    rw [hpointEq]
    exact (hCauchy x ⟨by linarith [hx.1],by linarith [hx.2]⟩).2
  have hmargin (p : Coord) (hp : p ∈ T) (sigma : ℝ) (hsigma : sigma ∈ Icc (0 : ℝ) 1) :
      nu/2 ≤ |stateQDenominator gs (qHeightJetSegment P zs sigma p)| ∧
        s0 ≤ qFirstCoefficient gs 5 (qHeightJetSegment P zs sigma p) := by
    have hm := hsegActual p (by simpa only [hTP] using hp) sigma hsigma
    have he : nu/2=(boundedClassSpeed kappa M)^2/(4*(M : ℝ)) := by dsimp [nu]; ring
    exact ⟨by simpa only [he] using hm.1,hm.2.2.2.1⟩
  have htravel' : speed*(b-a) ≤ L*r/4-L*r/16 := by
    have he : b-a=2*delta/(tau : ℝ) := by dsimp [a,b]; ring
    rw [he]
    calc
      speed*(2*delta/(tau : ℝ)) ≤ 3*(L*r/16) := htravel.2.1
      _ = L*r/4-L*r/16 := by ring
  dsimp only
  intro F hF hsource theta htheta i
  have hsourceMetric (p : Coord) (hp : p ∈ T) :
      |metricComparisonSource gt gs P zs p| ≤ F := by
    change |actualComparisonSource gStar g z q0 P p| ≤ F
    exact hsource p (by simpa only [hTP] using hp)
  have hgrad := hgradient gt P zs D (L*r/2) (L*r/4) (L*r/16) a b F
    hD (fun p hp => hp.1.2) hgt hPD hzsD (by positivity) (by linarith) hab
    hbox (fun p hp => hpS p hp) hpoint hPB' hzB
    (fun p hp => (hgeom p hp).2.2.2.2.2.1)
    (fun p hp => abs_pos.mp (hnu.trans_le (hgeom p hp).2.1))
    hmargin hvalue hvelocity (by positivity) hF htravel'
    hsourceMetric theta
    (by simpa only [a,b,neg_div] using htheta) i
  have he : b-a=2*delta/(tau : ℝ) := by dsimp [a,b]; ring
  rw [he] at hgrad
  have hexp := comparison_exponential_le_fixed htpos hrateTau
  have hbound := mul_le_mul_of_nonneg_right hexp hF
  have hbound := mul_le_mul_of_nonneg_right hbound (Real.sqrt_nonneg (2*(L*r/4)))
  have hduration : 0 ≤ 2*delta/(tau : ℝ) :=
    div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hdelt.le) htpos.le
  have hbound := mul_le_mul_of_nonneg_right hbound hduration
  have hbound := mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg (2*(1+1/s0)))
  apply hgrad.trans
  convert hbound using 1
  dsimp [Cgradient]
  ring

end SmoothLocal.Perturbation

end

end OAI
