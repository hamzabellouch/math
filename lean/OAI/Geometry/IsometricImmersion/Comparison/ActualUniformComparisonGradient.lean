import OAI.Geometry.IsometricImmersion.Taylor.ActualUniformTaylorRich
import OAI.Geometry.IsometricImmersion.Comparison.ActualClassComparisonSourceBound
import OAI.Geometry.IsometricImmersion.Comparison.ActualClassComparisonGradient

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_uniform_comparison_gradient
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hgStarB : ∀ i j k, k ≤ 2 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G)
    (hdStar : ∀ p ∈ modelSquare, d ≤ (gStar p).det)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ boundedClassWidth kappa M*r ≤ 1/20 ∧
      heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
        (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M) ∧
      ∀ N : ℕ, 2 < N → ∃ Cres Csource Cgradient : ℝ,
        0 ≤ Cres ∧ 0 < Csource ∧ 0 ≤ Cgradient ∧
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
            (∀ x ∈ Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r),
              P ![x,-delta/(tau : ℝ)] = zs ![x,-delta/(tau : ℝ)] ∧
              coordPartial 1 P ![x,-delta/(tau : ℝ)] = coordPartial 1 zs ![x,-delta/(tau : ℝ)]) ∧
            (∀ x, ∃ Q : Polynomial ℝ, Q.natDegree ≤ N+1 ∧ ∀ t, Q.eval t = P ![x,t]) ∧
            (∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 →
              ∀ t ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ)),
                (boundedClassSpeed kappa M)^2/(8*(M : ℝ)) ≤ |covHessian gs P ![x,t] 0 0| ∧
                |qResidual gs P ![x,t]| ≤ Cres/(tau : ℝ)^N) ∧
            ContinuousOn (qResidual gs P)
              (pulseStrip (boundedClassWidth kappa M*r/16) delta (tau : ℝ)) ∧
            |pulseWeightedMoment (boundedClassWidth kappa M*r/16) delta (tau : ℝ) (qResidual gs P)| ≤
              (2*Cres*(∫ x : ℝ, axisBump (boundedClassWidth kappa M*r/16) x))*delta/(tau : ℝ)^(N+1) ∧
            (∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
              |actualComparisonSource gStar (perturbedMetric g0 eta.val) z q0 P p| ≤
                Csource*(tau : ℝ)^2/(tau : ℝ)^N) ∧
            (∀ theta ∈ Icc (-(delta/(tau : ℝ))) (delta/(tau : ℝ)), ∀ i : Fin 2,
              Real.sqrt (∫ x in Icc (-(boundedClassWidth kappa M*r/16)) (boundedClassWidth kappa M*r/16),
                (coordPartial i (comparisonDifference P zs) (boxPoint x theta))^2) ≤
                Cgradient*delta*(tau : ℝ)/(tau : ℝ)^N) := by
  obtain ⟨r,hr,hrhalf,hLr,hrsmall,hTaylor⟩ :=
    exists_actual_uniform_taylor_comparison_and_moment hgStar hV hSV M hG hd hkappa hM hq0
  refine ⟨r,hr,hrhalf,hLr,hrsmall,?_⟩
  intro N hN
  obtain ⟨Cres,hCres,hTaylorN⟩ := hTaylor N
  obtain ⟨Csource,hCsource,hsource⟩ := exists_actual_class_comparison_source_bound_at_radius
    hgStar hV hSV M hG hd hgStarB hdStar hkappa hM hq0 hr hrhalf hLr hrsmall N hN Cres hCres
  obtain ⟨CE,hCE,hgradient⟩ := exists_actual_class_comparison_gradient_from_source
    hgStar hV hSV M hG hd hgStarB hdStar hkappa hM hq0 hr hrhalf hLr hrsmall N hN
  refine ⟨Cres,Csource,CE*Csource,hCres,hCsource,mul_nonneg hCE hCsource.le,?_⟩
  intro delta hdelt hdhalf
  filter_upwards [hTaylorN delta hdelt hdhalf,hsource delta hdelt hdhalf,hgradient delta hdelt hdhalf]
    with tau htaylor hsourceTau hgradientTau
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let L := boundedClassWidth kappa M
  let zs := heightInShearCoordinates z q0
  let gs := metricInShearCoordinates gStar q0
  let P := taylorApproximation gs (-delta/(tau : ℝ))
    (heightCauchyValue zs (-delta/(tau : ℝ)))
    (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
  have ht := htaylor g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have hres (p : Coord) (hp : p ∈ pulseStrip (L*r/2) delta (tau : ℝ)) :
      |qResidual gs P p| ≤ Cres/(tau : ℝ)^N := by
    have he : ![p 0,p 1] = p := by ext i; fin_cases i <;> rfl
    have htime : p 1 ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ)) := by
      simpa only [neg_div] using hp.2
    simpa only [he] using (ht.2.2.2.1 (p 0) (abs_le.mpr hp.1) (p 1) htime).2
  have hs := hsourceTau.2 g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ P hres
  refine ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1,ht.2.2.2.2.1,ht.2.2.2.2.2,hs,?_⟩
  have htpos : (0 : ℝ) < tau := zero_lt_one.trans_le (by exact_mod_cast hsourceTau.1)
  have hF : 0 ≤ Csource*(tau : ℝ)^2/(tau : ℝ)^N := by positivity
  intro theta htheta i
  have hgrad := hgradientTau g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
    (Csource*(tau : ℝ)^2/(tau : ℝ)^N) hF hs theta htheta i
  apply hgrad.trans_eq
  field_simp [htpos.ne']

end SmoothLocal.Perturbation

end

end OAI
