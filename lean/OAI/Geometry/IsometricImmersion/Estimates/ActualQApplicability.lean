import OAI.Geometry.IsometricImmersion.Coordinates.ActualReferenceSegment
import OAI.Geometry.IsometricImmersion.Estimates.ActualQPointBounds

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_Q_applicability_at_radius
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
    ∃ Aref A D dcompare : ℝ, 1 ≤ Aref ∧ 0 ≤ A ∧ 0 ≤ D ∧ 0 < dcompare ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 →
      ∀ᶠ tau : ℕ in atTop,
        2 ≤ tau ∧ N ≤ tau ∧
        SmoothPositiveOn (testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ)) modelOpenSquare ∧
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
          ∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
            QPulsePointBounds gStar (perturbedMetric g0 eta.val) z modelOpenSquare q0
              (boundedClassWidth kappa M*r/16) delta (tau : ℝ) N
              (8*G) (G+1) (max (8*G) (boundedClassShearedStateBudget q0 M)) D A d dcompare
              ((boundedClassSpeed kappa M)^2/(4*(M : ℝ))) (metricApproximationAccuracy tau)
              (qPulseFirstJetBudget (boundedClassWidth kappa M*r/16)
                (div_pos (mul_pos (boundedClassWidth_pos kappa M) hr) (by norm_num)) N delta (tau : ℝ)) p ∧
            (1/(M : ℝ))/2 ≤ heightEnergy (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p ∧
            |covHessian (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p 0 0| ≤ Aref ∧
            (metricInShearCoordinates gStar q0 p).det ≤ 2*G^2 ∧
            forcingFloor ((1/(M : ℝ))/2) (2*G^2) Aref ≤
              |forcingCoefficient (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p| ∧
            covHessian (metricInShearCoordinates (perturbedMetric g0 eta.val) q0)
              (heightInShearCoordinates z q0) p 0 0 ≠ 0 := by
  let L := boundedClassWidth kappa M
  let c := (boundedClassSpeed kappa M)^2/(4*(M : ℝ))
  have hc : 0 < c := by
    have hh := boundedClassShearHxxFloor_pos hkappa hM
    have he : c=((boundedClassSpeed kappa M)^2/(2*(M : ℝ)))/2 := by dsimp only [c]; ring
    rw [he]
    exact half_pos hh
  have he : 0 < (1/(M : ℝ))/2 := half_pos (one_div_pos.mpr (Nat.cast_pos.mpr hM))
  obtain ⟨_,Aref,_,hAref,hsegment⟩ := exists_actual_reference_segment_at_radius
    hgStar hV hSV M hG hd hgStarB hdStar hkappa hM hq0 hr hrhalf hLr hrsmall N hN
  obtain ⟨A,D,dcompare,hA,hD,hdcompare,hpoint⟩ := exists_actual_Q_point_bounds_from_reference_floor
    hgStar hV hSV M hG hd hc hgStarB hdStar hq0 hr hLr N (by omega)
  refine ⟨Aref,A,D,dcompare,hAref,hA,hD,hdcompare,?_⟩
  intro delta hdelt hdhalf
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [hsegment delta hdelt hdhalf,hpoint delta hdelt,hwidth] with tau hsTau hpTau hw
  refine ⟨hpTau.1,hpTau.2.1,hpTau.2.2.1,?_⟩
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let g := perturbedMetric g0 eta.val
  let gs := metricInShearCoordinates gStar q0
  let zs := heightInShearCoordinates z q0
  let S := pulseStrip (L*r/2) delta (tau : ℝ)
  have hs := (hsTau g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ).2.2
  have hbr : delta/(tau : ℝ) ≤ r := by
    have heq : delta/(tau : ℝ)=2*(delta/(2*(tau : ℝ))) := by ring
    rw [heq]
    linarith [hw.2]
  have hcoordinates (p : Coord) (hp : p ∈ S) : |p 0| ≤ L*r ∧ |p 1| ≤ r :=
    ⟨(abs_le.mpr hp.1).trans (by linarith [mul_pos (boundedClassWidth_pos kappa M) hr]),
      (abs_le.mpr hp.2).trans hbr⟩
  have hgeom (p : Coord) (hp : p ∈ S) := actual_central_sheared_solution_margins
    eta hclass hG hd hkappa hr.le hLr hq0 hrsmall hgB hdet hcenter
      (hcoordinates p hp).1 (hcoordinates p hp).2
  have hpS (p : Coord) (hp : p ∈ S) : inverseShearCoordinates q0 p ∈ modelSquare := (hgeom p hp).1
  have hgs := metricInShearCoordinates_smoothPositive hgStar q0
  have hreference (p : Coord) (hp : p ∈ S) :
      c ≤ |covHessian gs zs p 0 0| ∧ |covHessian gs zs p 0 0| ≤ Aref ∧
        (1/(M : ℝ))/2 ≤ heightEnergy gs zs p := by
    have hm := hs p hp 1 (by norm_num)
    simp only [qHeightJetSegment,stateSegment_one,stateQDenominator_qSolutionJet] at hm
    have hE := hm.2.2.1
    unfold stateEnergy at hE
    rw [statePoint_qSolutionJet,stateGradient_qSolutionJet,
      jetEnergy_at_height hgs (hSV (hpS p hp)) zs] at hE
    exact ⟨hm.1,hm.2.1,hE⟩
  have hSU : modelSquare ⊆ U := hf.squareSubset.trans hf.domainSubset
  have hQ := hpTau.2.2.2 g U z hg hU hSU hclass
    (fun i j k hk => hgB i j k (by omega)) hdet happ (fun p hp => (hreference p hp).1)
  intro p hp
  have href := hreference p hp
  have hdetup : (gs p).det ≤ 2*G^2 := by
    rw [metricDet_in_shear_coordinates]
    apply actual_det_upper_of_entry_bound gStar _ hG
    intro i j
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hgStarB i j 0 (by norm_num) _ (hpS p hp)
  have hforcing := forcingCoefficient_floor_of_reference_margins hgs (hSV (hpS p hp))
    he hc href.2.2 hdetup href.1 href.2.1
  have hactual : covHessian (metricInShearCoordinates g q0) zs p 0 0 ≠ 0 :=
    abs_pos.mp ((boundedClassShearHxxFloor_pos hkappa hM).trans_le (hgeom p hp).2.1)
  exact ⟨hQ p hp,href.2.2,href.2.1,hdetup,hforcing,hactual⟩

end SmoothLocal.Perturbation

end

end OAI
