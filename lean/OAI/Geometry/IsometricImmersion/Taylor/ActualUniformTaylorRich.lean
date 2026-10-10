import OAI.Geometry.IsometricImmersion.Taylor.ActualUniformTaylorPulse
import OAI.Geometry.IsometricImmersion.Pulses.PulseMomentError

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_uniform_taylor_comparison_and_moment
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ boundedClassWidth kappa M*r ≤ 1/20 ∧
      heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
        (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M) ∧
      ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 →
        ∀ᶠ tau : ℕ in atTop,
          ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa) (U W : Set Coord)
            (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
            SmoothPositiveOn (perturbedMetric g0 eta.val) U → IsOpen U →
            CapInductionHeight (perturbedMetric g0 eta.val) U (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) z →
            CapInductionFlow (perturbedMetric g0 eta.val) U G (M : ℝ) d (1/(M : ℝ)) (1/(M : ℝ)) kappa z Y W →
            BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
            (∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G) →
            (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
            |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
                testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                  metricApproximationAccuracy tau) →
            let zs := heightInShearCoordinates z q0
            let gs := metricInShearCoordinates gStar q0
            let z0 := taylorApproximation gs (-delta/(tau : ℝ))
              (heightCauchyValue zs (-delta/(tau : ℝ)))
              (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
            ContDiffOn ℝ ∞ z0 (spatialStrip (Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r))) ∧
            (∀ x ∈ Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r),
              z0 ![x,-delta/(tau : ℝ)] = zs ![x,-delta/(tau : ℝ)] ∧
              coordPartial 1 z0 ![x,-delta/(tau : ℝ)] = coordPartial 1 zs ![x,-delta/(tau : ℝ)]) ∧
            (∀ x, ∃ P : Polynomial ℝ, P.natDegree ≤ N+1 ∧ ∀ t, P.eval t = z0 ![x,t]) ∧
            (∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 →
              ∀ t ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ)),
                (boundedClassSpeed kappa M)^2/(8*(M : ℝ)) ≤ |covHessian gs z0 ![x,t] 0 0| ∧
                |qResidual gs z0 ![x,t]| ≤ C/(tau : ℝ)^N) ∧
            ContinuousOn (qResidual gs z0)
              (pulseStrip (boundedClassWidth kappa M*r/16) delta (tau : ℝ)) ∧
            |pulseWeightedMoment (boundedClassWidth kappa M*r/16) delta (tau : ℝ) (qResidual gs z0)| ≤
              (2*C*(∫ x : ℝ, axisBump (boundedClassWidth kappa M*r/16) x))*delta/(tau : ℝ)^(N+1) := by
  obtain ⟨r,hr,hrhalf,hLr,hrsmall,hTaylor⟩ :=
    exists_actual_uniform_taylor_pulse hgStar hV hSV M hG hd hkappa hM hq0
  refine ⟨r,hr,hrhalf,hLr,hrsmall,?_⟩
  intro N
  obtain ⟨C,hC,hN⟩ := hTaylor N
  refine ⟨C,hC,?_⟩
  intro delta hdelt hdhalf
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [hN delta hdelt hdhalf,hwidth] with tau htaylor hwidthTau
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have ht := htaylor g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let L := boundedClassWidth kappa M
  let a := L*r/16
  let gs := metricInShearCoordinates gStar q0
  let zs := heightInShearCoordinates z q0
  let P := taylorApproximation gs (-delta/(tau : ℝ))
    (heightCauchyValue zs (-delta/(tau : ℝ)))
    (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
  let I := Ioo (-(L*r)) (L*r)
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have ha : 0 < a := div_pos (mul_pos hL hr) (by norm_num)
  have htr : (0 : ℝ) < tau := zero_lt_one.trans_le hwidthTau.1
  have hdw : delta/(tau : ℝ) ≤ r := by
    have he : delta/(tau : ℝ) = 2*(delta/(2*(tau : ℝ))) := by ring
    rw [he]
    linarith [hwidthTau.2]
  have hP : ContDiffOn ℝ ∞ P (spatialStrip I) := ht.1
  have hpoint (p : Coord) (hp : p ∈ pulseStrip a delta (tau : ℝ)) :
      (boundedClassSpeed kappa M)^2/(8*(M : ℝ)) ≤ |covHessian gs P p 0 0| ∧
      |qResidual gs P p| ≤ C/(tau : ℝ)^N := by
    have hx : |p 0| ≤ L*r/2 := (abs_le.mpr hp.1).trans (by dsimp [a]; nlinarith [mul_pos hL hr])
    have htime : p 1 ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ)) := by
      simpa only [neg_div] using hp.2
    have he : ![p 0,p 1] = p := by ext i; fin_cases i <;> rfl
    simpa only [he] using ht.2.2.2 (p 0) hx (p 1) htime
  have hgs := metricInShearCoordinates_smoothPositive hgStar q0
  have hVs := shearedModelDomain_isOpen hV q0
  have hc : 0 < (boundedClassSpeed kappa M)^2/(8*(M : ℝ)) :=
    div_pos (sq_pos_of_pos (boundedClassSpeed_pos hkappa hM))
      (mul_pos (by norm_num) (Nat.cast_pos.mpr hM))
  have hsub : pulseStrip a delta (tau : ℝ) ⊆
      comparisonDomain gs (inverseShearCoordinates q0 ⁻¹' V) P I := by
    intro p hp
    have hx : |p 0| ≤ L*r/2 := (abs_le.mpr hp.1).trans (by dsimp [a]; nlinarith [mul_pos hL hr])
    have hpI : p ∈ spatialStrip I := by
      exact ⟨by linarith [(abs_le.mp hx).1,mul_pos hL hr],
        by linarith [(abs_le.mp hx).2,mul_pos hL hr]⟩
    have htime : p 1 ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ)) := by
      simpa only [neg_div] using hp.2
    have he : ![p 0,p 1] = p := by ext i; fin_cases i <;> rfl
    have hpS : p ∈ shearedModelSquare q0 := by
      simpa only [he] using pulseRectangle_mem_shearedModelSquare hL hr hrhalf hLr hq0 hdw hx htime
    exact mem_comparisonDomain hpI (shearedModelSquare_subset_domain hSV q0 hpS)
      (abs_pos.mp (hc.trans_le (hpoint p hp).1))
  refine ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2,
    (qResidual_contDiffOn hgs hVs isOpen_Ioo hP).continuousOn.mono hsub,?_⟩
  apply (pulseWeightedMoment_bound ha hdelt.le htr (div_nonneg hC (pow_nonneg htr.le N))
    (fun p hp => (hpoint p hp).2)).trans_eq
  rw [pow_succ]
  field_simp [htr.ne']
  ring

end SmoothLocal.Perturbation

end

end OAI
