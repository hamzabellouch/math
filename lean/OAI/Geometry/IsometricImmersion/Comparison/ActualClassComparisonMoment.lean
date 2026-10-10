import OAI.Geometry.IsometricImmersion.Pulses.ActualClassQForcingMoment
import OAI.Geometry.IsometricImmersion.Comparison.ActualUniformComparisonGradient
import OAI.Geometry.IsometricImmersion.Comparison.ActualComparisonSource

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_class_comparison_moment
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
      ∀ N : ℕ, 2 < N → ∃ C Csource Cgradient c3 : ℝ,
        0 ≤ C ∧ 0 < Csource ∧ 0 ≤ Cgradient ∧ 0 < c3 ∧
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
  obtain ⟨r,hr,hrhalf,hLr,hrsmall,hTaylor⟩ :=
    exists_actual_uniform_comparison_gradient hgStar hV hSV M hG hd hgStarB hdStar hkappa hM hq0
  refine ⟨r,hr,hrhalf,hLr,hrsmall,?_⟩
  intro N hN
  let L := boundedClassWidth kappa M
  let a := L*r/16
  have ha : 0 < a := div_pos (mul_pos (boundedClassWidth_pos kappa M) hr) (by norm_num)
  obtain ⟨C,Csource,Cgradient,hC,hCsource,hCgradient,hTaylorN⟩ := hTaylor N hN
  obtain ⟨cQ,hcQ,hQmoment⟩ := exists_actual_class_Q_forcing_moment_at_radius
    hgStar hV hSV M hG hd hgStarB hdStar hkappa hM hq0 hr hrhalf hLr hrsmall N hN
  obtain ⟨Aref,A,D,dcompare,_,_,_,_,happlicable⟩ :=
    exists_actual_Q_applicability_at_radius hgStar hV hSV M hG hd hgStarB hdStar
      hkappa hM hq0 hr hrhalf hLr hrsmall N hN
  let R := 2*C*(∫ x : ℝ, axisBump a x)
  have hR : 0 ≤ R := mul_nonneg (mul_nonneg (by norm_num) hC) (axisBump_integral_pos ha).le
  obtain ⟨T,_,habsorb⟩ := taylor_moment_absorption_threshold hR hcQ N
  refine ⟨C,Csource,Cgradient,cQ/2,hC,hCsource,hCgradient,half_pos hcQ,?_⟩
  intro delta hdelt hdhalf
  have hlarge : ∀ᶠ tau : ℕ in atTop, T ≤ (tau : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop T)
  filter_upwards [hTaylorN delta hdelt hdhalf,hQmoment delta hdelt hdhalf,
    happlicable delta hdelt hdhalf,hlarge] with tau hTaylorTau hQTau hATau ht
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let g := perturbedMetric g0 eta.val
  let gs := metricInShearCoordinates gStar q0
  let zs := heightInShearCoordinates z q0
  let P := taylorApproximation gs (-delta/(tau : ℝ))
    (heightCauchyValue zs (-delta/(tau : ℝ))) (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
  have hTaylorActual := hTaylorTau g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have hQlower := hQTau g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have hpoint := hATau.2.2.2 g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have hsub : pulseStrip a delta (tau : ℝ) ⊆ pulseStrip (L*r/2) delta (tau : ℝ) := by
    intro p hp
    refine ⟨⟨?_,?_⟩,hp.2⟩ <;> dsimp only [a] at hp <;>
      linarith [hp.1.1,hp.1.2,mul_pos (boundedClassWidth_pos kappa M) hr]
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans (hf.squareSubset.trans hf.domainSubset)
  have hOV : modelOpenSquare ⊆ V := modelOpenSquare_subset.trans hSV
  have hgO : SmoothPositiveOn g modelOpenSquare :=
    ⟨fun i j => (hg.1 i j).mono hOU,fun p hp => hg.2 p (hOU hp)⟩
  have hgStarO : SmoothPositiveOn gStar modelOpenSquare :=
    ⟨fun i j => (hgStar.1 i j).mono hOV,fun p hp => hgStar.2 p (hOV hp)⟩
  have hzO := hh.smooth.mono hOU
  have hSU : ∀ p ∈ pulseStrip a delta (tau : ℝ), inverseShearCoordinates q0 p ∈ modelOpenSquare :=
    fun p hp => (hpoint p (hsub hp)).1.point_mem
  have hc : 0 < (boundedClassSpeed kappa M)^2/(4*(M : ℝ)) :=
    div_pos (sq_pos_of_pos (boundedClassSpeed_pos hkappa hM)) (mul_pos (by norm_num) (Nat.cast_pos.mpr hM))
  have hxxRef : ∀ p ∈ pulseStrip a delta (tau : ℝ), covHessian gs zs p 0 0 ≠ 0 :=
    fun p hp => abs_pos.mp (hc.trans_le (hpoint p (hsub hp)).1.referenceXX)
  have hxxActual : ∀ p ∈ pulseStrip a delta (tau : ℝ),
      covHessian (metricInShearCoordinates g q0) zs p 0 0 ≠ 0 :=
    fun p hp => (hpoint p (hsub hp)).2.2.2.2.2
  have hQc : ContinuousOn (actualShearedQForcing gStar g z q0) (pulseStrip a delta (tau : ℝ)) :=
    ((sheared_Q_on_height_contDiffOn hgO hzO modelOpenSquare_isOpen q0 hSU hxxActual).sub
      (sheared_Q_on_height_contDiffOn hgStarO hzO modelOpenSquare_isOpen q0 hSU hxxRef)).continuousOn
  have hPc : ContinuousOn (qResidual gs P) (pulseStrip a delta (tau : ℝ)) := hTaylorActual.2.2.2.2.1
  have hPres := hTaylorActual.2.2.2.2.2.1
  have htriangle := actualComparisonSource_moment_triangle hQc hPc
  have habs := habsorb (tau : ℝ) ht delta hdelt.le
  change |pulseWeightedMoment a delta (tau : ℝ) (qResidual gs P)| ≤ R*delta/(tau : ℝ)^(N+1) at hPres
  refine ⟨hTaylorActual.1,hTaylorActual.2.1,hTaylorActual.2.2.1,hTaylorActual.2.2.2.1,
    hPc,hPres,hTaylorActual.2.2.2.2.2.2.1,hTaylorActual.2.2.2.2.2.2.2,hQc.sub hPc,?_⟩
  have hhalf : (cQ/2)*delta*(tau : ℝ)/(tau : ℝ)^N =
      (cQ*delta*(tau : ℝ)/(tau : ℝ)^N)/2 := by ring
  rw [hhalf] at habs ⊢
  linarith

end SmoothLocal.Perturbation

end

end OAI
