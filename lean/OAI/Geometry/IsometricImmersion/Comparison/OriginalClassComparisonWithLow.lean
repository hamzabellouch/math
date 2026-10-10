import OAI.Geometry.IsometricImmersion.Comparison.ActualClassComparisonMoment
import OAI.Geometry.IsometricImmersion.Caps.ActualClassTwoSidedCauchy
import OAI.Geometry.IsometricImmersion.Taylor.ActualTaylorFiniteJets

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor SmoothLocal.Model

theorem exists_original_class_comparison_with_low_data
    {g0 gStar : MetricField} {V : Set Coord}
    (hg0 : SmoothPositiveOn g0 V) (hgStar : SmoothPositiveOn gStar V)
    (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {kappa q0 : ℝ} (M : ℕ) (hkappa : 0 < kappa) (hM : 0 < M)
    (hq0 : |q0| ≤ 1/20)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p = modelCurvature kappa p) :
    ∃ G d r : ℝ, 0 < G ∧ 0 < d ∧ 0 < r ∧ r < 1/2 ∧
      (∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G) ∧
      (∀ p ∈ modelSquare, d ≤ (gStar p).det) ∧
      (∀ a : ℝ, 0 < a → ∀ N : ℕ, 10 < N → ∀ delta : ℝ,
        ∀ᶠ tau : ℕ in atTop,
          ∀ (gTau : MetricField) (U : Set Coord), SmoothPositiveOn gTau U → IsOpen U → modelSquare ⊆ U →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
                testMetric gStar q0 a N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau) →
            (∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ G) ∧
            (∀ p ∈ modelSquare, d ≤ |(gTau p).det|)) ∧
      boundedClassWidth kappa M*r ≤ 1/20 ∧
      heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
        (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M) ∧
      (∀ K : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 10 < N → ∀ delta : ℝ, 0 < delta →
        ∀ᶠ tau : ℕ in atTop,
          ∀ (eta : metricPatchSet g0 kappa) (z : Coord → ℝ),
            BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
            |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤
              1/(100*boundedClassWidth kappa M) →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
                testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                  metricApproximationAccuracy tau) →
            ∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 → ∀ n ≤ K,
              (‖iteratedFDeriv ℝ n (heightCauchyValue (heightInShearCoordinates z q0)
                (-delta/(tau : ℝ))) x‖ ≤ B ∧
              ‖iteratedFDeriv ℝ n (heightCauchyVelocity (heightInShearCoordinates z q0)
                (-delta/(tau : ℝ))) x‖ ≤ B) ∧
              (‖iteratedFDeriv ℝ n (heightCauchyValue (heightInShearCoordinates z q0)
                (delta/(tau : ℝ))) x‖ ≤ B ∧
              ‖iteratedFDeriv ℝ n (heightCauchyVelocity (heightInShearCoordinates z q0)
                (delta/(tau : ℝ))) x‖ ≤ B)) ∧
      ∀ N : ℕ, 10 < N → ∃ C Csource Cgradient c3 : ℝ,
        0 ≤ C ∧ 0 < Csource ∧ 0 ≤ Cgradient ∧ 0 < c3 ∧
        (∀ K : ℕ, ∃ CP : ℝ, 0 ≤ CP ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 → ∀ᶠ tau : ℕ in atTop,
            ∀ (eta : metricPatchSet g0 kappa) (z : Coord → ℝ),
              BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
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
              (∀ j ≤ K, ∀ p : Coord, |p 0| ≤ boundedClassWidth kappa M*r/2 →
                |p 1| ≤ delta/(tau : ℝ) → ‖iteratedFDeriv ℝ j P p‖ ≤ CP) ∧
              CoordinateBound P (pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ)) K CP) ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 → ∀ᶠ tau : ℕ in atTop,
          ∀ (eta : metricPatchSet g0 kappa) (z : Coord → ℝ),
            BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
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
            (∀ x ∈ Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r),
              P ![x,-delta/(tau : ℝ)] = zs ![x,-delta/(tau : ℝ)] ∧
              coordPartial 1 P ![x,-delta/(tau : ℝ)] = coordPartial 1 zs ![x,-delta/(tau : ℝ)]) ∧
            (∀ x, ∃ poly : Polynomial ℝ, poly.natDegree ≤ N+1 ∧ ∀ t, poly.eval t = P ![x,t]) ∧
            (∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 →
              ∀ t ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ)),
                (boundedClassSpeed kappa M)^2/(8*(M : ℝ)) ≤ |covHessian gs P ![x,t] 0 0| ∧
                |qResidual gs P ![x,t]| ≤ C/(tau : ℝ)^N) ∧
            ContinuousOn (qResidual gs P) (pulseStrip (boundedClassWidth kappa M*r/16) delta (tau : ℝ)) ∧
            |pulseWeightedMoment (boundedClassWidth kappa M*r/16) delta (tau : ℝ) (qResidual gs P)| ≤
              (2*C*(∫ x : ℝ, axisBump (boundedClassWidth kappa M*r/16) x))*delta/(tau : ℝ)^(N+1) ∧
            (∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
              |actualComparisonSource gStar (perturbedMetric g0 eta.val) z q0 P p| ≤
                Csource*(tau : ℝ)^2/(tau : ℝ)^N) ∧
            (∀ theta ∈ Icc (-(delta/(tau : ℝ))) (delta/(tau : ℝ)), ∀ i : Fin 2,
              Real.sqrt (∫ x in Icc (-(boundedClassWidth kappa M*r/16)) (boundedClassWidth kappa M*r/16),
                (coordPartial i (comparisonDifference P zs) (boxPoint x theta))^2) ≤
                Cgradient*delta*(tau : ℝ)/(tau : ℝ)^N) ∧
            ContinuousOn (actualComparisonSource gStar (perturbedMetric g0 eta.val) z q0 P)
              (pulseStrip (boundedClassWidth kappa M*r/16) delta (tau : ℝ)) ∧
            c3*delta*(tau : ℝ)/(tau : ℝ)^N ≤
              |pulseWeightedMoment (boundedClassWidth kappa M*r/16) delta (tau : ℝ)
                (actualComparisonSource gStar (perturbedMetric g0 eta.val) z q0 P)| := by
  obtain ⟨G,d,hG,hd,hGstar,hdstar,hlow,hcuts⟩ :=
    exists_actual_class_two_sided_cauchy_bounds_at_every_radius
      hg0 hgStar hV hSV M hkappa hM hq0 hbackground
  have hGstar2 : ∀ i j : Fin 2, ∀ k ≤ 2, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G :=
    fun i j k hk p hp => hGstar i j k (by omega) p hp
  obtain ⟨r,hr,hrhalf,hLr,hrsmall,hcomparison⟩ :=
    exists_actual_class_comparison_moment hgStar hV hSV M hG.le hd hGstar2 hdstar hkappa hM hq0
  refine ⟨G,d,r,hG,hd,hr,hrhalf,hGstar,hdstar,hlow,hLr,hrsmall,
    hcuts r hr hrhalf hLr hrsmall,?_⟩
  intro N hN
  obtain ⟨C,Csource,Cgradient,c3,hC,hCs,hCg,hc3,hcomparisonN⟩ := hcomparison N (by omega)
  refine ⟨C,Csource,Cgradient,c3,hC,hCs,hCg,hc3,?_,?_⟩
  · intro K
    obtain ⟨CP,hCP,hPjets⟩ := exists_actual_taylor_finite_jets_at_radius
      hgStar hV hSV M hG.le hd hkappa hM hq0 hr hrhalf hLr hrsmall N K
    refine ⟨CP,hCP,?_⟩
    intro delta hdelt hdhalf
    have ha : 0 < boundedClassWidth kappa M*r/16 :=
      div_pos (mul_pos (boundedClassWidth_pos kappa M) hr) (by norm_num)
    filter_upwards [hPjets delta hdelt hdhalf,
      hlow (boundedClassWidth kappa M*r/16) ha N hN delta] with tau hPjetsTau hlowTau
    intro eta z hclass hcenter happ
    obtain ⟨U,hU,hSU,hUV,_,hgU,hh⟩ := bounded_class_actual_cap_data hg0 hV hSV eta hclass
    obtain ⟨hg8,hdet⟩ := hlowTau (perturbedMetric g0 eta.val) U hgU hU hSU happ
    have hg4 : ∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j) p‖ ≤ G :=
      fun i j k hk p hp => hg8 i j k (by omega) p hp
    have hmodel : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p :=
      fun p hp => hbackground p (hUV hp)
    have hc : 0 < 1/(M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
    obtain ⟨W,Y,hf⟩ := exists_capInductionFlow hgU hU hSU hG.le (Nat.cast_nonneg M)
      hd hc hc hg8 hdet hh hkappa hmodel (perturbationTensor_tsupport_subset eta.val) eta.property.2
    exact hPjetsTau g0 eta U W z Y hgU hU hh hf hclass hg4 hdet hcenter happ
  intro delta hdelt hdhalf
  have ha : 0 < boundedClassWidth kappa M*r/16 := by
    exact div_pos (mul_pos (boundedClassWidth_pos kappa M) hr) (by norm_num)
  filter_upwards [hcomparisonN delta hdelt hdhalf,
    hlow (boundedClassWidth kappa M*r/16) ha N hN delta] with tau hcTau hlowTau
  intro eta z hclass hcenter happ
  obtain ⟨U,hU,hSU,hUV,_,hgU,hh⟩ := bounded_class_actual_cap_data hg0 hV hSV eta hclass
  obtain ⟨hg8,hdet⟩ := hlowTau (perturbedMetric g0 eta.val) U hgU hU hSU happ
  have hg4 : ∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j) p‖ ≤ G :=
    fun i j k hk p hp => hg8 i j k (by omega) p hp
  have hmodel : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p :=
    fun p hp => hbackground p (hUV hp)
  have hc : 0 < 1/(M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  obtain ⟨W,Y,hf⟩ := exists_capInductionFlow hgU hU hSU hG.le (Nat.cast_nonneg M)
    hd hc hc hg8 hdet hh hkappa hmodel (perturbationTensor_tsupport_subset eta.val) eta.property.2
  exact hcTau g0 eta U W z Y hgU hU hh hf hclass hg4 hdet hcenter happ

end SmoothLocal.Perturbation

end

end OAI
