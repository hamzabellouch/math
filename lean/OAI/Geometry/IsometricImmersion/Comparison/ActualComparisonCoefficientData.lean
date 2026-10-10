import OAI.Geometry.IsometricImmersion.Coordinates.ActualReferenceSegment
import OAI.Geometry.IsometricImmersion.Comparison.ComparisonCoefficientBounds

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_comparison_coefficient_data_at_radius
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
    ∃ K K1 : ℝ, 1 ≤ K ∧ 0 ≤ K1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 → ∀ᶠ tau : ℕ in atTop,
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
            (heightCauchyValue zs (-delta/(tau : ℝ))) (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
          ∀ i : Fin 6, ∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
            |comparisonCoefficient gs P zs i p| ≤ K ∧
            |coordPartial 0 (comparisonCoefficient gs P zs i) p| ≤ K1 := by
  let L := boundedClassWidth kappa M
  let Z := (2*(1+|q0|))^3*(M : ℝ)
  let gs := metricInShearCoordinates gStar q0
  let Vs := inverseShearCoordinates q0 ⁻¹' V
  let c := (boundedClassSpeed kappa M)^2/(4*(M : ℝ))
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hc : 0 < c := div_pos (sq_pos_of_pos (boundedClassSpeed_pos hkappa hM))
    (mul_pos (by norm_num) (Nat.cast_pos.mpr hM))
  obtain ⟨CP,_,_,_,hsegment⟩ := exists_actual_reference_segment_at_radius
    hgStar hV hSV M hG hd hgStarB hdStar hkappa hM hq0 hr hrhalf hLr hrsmall N hN
  have hgs := metricInShearCoordinates_smoothPositive hgStar q0
  have hVs : IsOpen Vs := shearedModelDomain_isOpen hV q0
  obtain ⟨K,hK,hcoeff⟩ := exists_uniform_comparison_coefficient_bounds hgs hVs
    (shearedModelSquare_isCompact q0) (shearedModelSquare_subset_domain hSV q0) 1 CP Z (by norm_num) hc
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  refine ⟨K,K*(max 1 CP+max 1 Z),hK,by positivity,?_⟩
  intro delta hdelt hdhalf
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [hsegment delta hdelt hdhalf,hwidth] with tau hsegmentTau hw
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let zs := heightInShearCoordinates z q0
  let P := taylorApproximation gs (-delta/(tau : ℝ))
    (heightCauchyValue zs (-delta/(tau : ℝ))) (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
  let I := Ioo (-(L*r)) (L*r)
  let T := pulseStrip (L*r/2) delta (tau : ℝ)
  let Us := inverseShearCoordinates q0 ⁻¹' U
  let D := (Us ∩ Vs) ∩ spatialStrip I
  have hUs : IsOpen Us := shearedModelDomain_isOpen hU q0
  have hD : IsOpen D := (hUs.inter hVs).inter (spatialStrip_isOpen isOpen_Ioo)
  have hbr : delta/(tau : ℝ) ≤ r := by
    have heq : delta/(tau : ℝ)=2*(delta/(2*(tau : ℝ))) := by ring
    rw [heq]
    linarith [hw.2]
  have hSU : modelSquare ⊆ U := hf.squareSubset.trans hf.domainSubset
  have hcoordinates (p : Coord) (hp : p ∈ T) : |p 0| ≤ L*r ∧ |p 1| ≤ r :=
    ⟨(abs_le.mpr hp.1).trans (by linarith [mul_pos hL hr]),(abs_le.mpr hp.2).trans hbr⟩
  have hgeom (p : Coord) (hp : p ∈ T) := actual_central_sheared_solution_margins
    eta hclass hG hd hkappa hr.le hLr hq0 hrsmall hgB hdet hcenter
      (hcoordinates p hp).1 (hcoordinates p hp).2
  have hpS (p : Coord) (hp : p ∈ T) : inverseShearCoordinates q0 p ∈ modelSquare := (hgeom p hp).1
  have hTD : T ⊆ D := by
    intro p hp
    exact ⟨⟨hSU (hpS p hp),hSV (hpS p hp)⟩,
      ⟨by linarith [hp.1.1,mul_pos hL hr],by linarith [hp.1.2,mul_pos hL hr]⟩⟩
  have hpoint (p : Coord) (hp : p ∈ T) : ‖p‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    fin_cases i
    · exact (hcoordinates p hp).1.trans (hLr.trans (by norm_num))
    · exact (hcoordinates p hp).2.trans (hrhalf.le.trans (by norm_num))
  have ht := hsegmentTau g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have hP : ContDiffOn ℝ ∞ P D := ht.1.mono inter_subset_right
  have hzs : ContDiffOn ℝ ∞ zs D := (heightInShearCoordinates_contDiffOn hh.smooth q0).mono
    (fun _ hp => hp.1.1)
  have hzB : CoordinateBound zs T 3 Z := bounded_class_sheared_C3_on_actual_region hclass q0 hpS
  have hactual := hcoeff P zs D T hD (fun _ hp => hp.1.2) hP hzs
    (fun p hp => hpS p hp) hTD hpoint ht.2.1 hzB (fun p hp sigma hs => (ht.2.2 p hp sigma hs).1)
  dsimp only
  intro i p hp
  exact ⟨(hactual i p hp).1,(hactual i p hp).2 0⟩

end SmoothLocal.Perturbation

end

end OAI
