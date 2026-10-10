import OAI.Geometry.IsometricImmersion.Estimates.ActualQApplicability
import OAI.Geometry.IsometricImmersion.Comparison.QApproximationMargins
import OAI.Geometry.IsometricImmersion.Comparison.ComparisonEnergyScaling

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_class_comparison_source_bound_at_radius
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
    (N : ℕ) (hN : 2 < N) (Cres : ℝ) (hCres : 0 ≤ Cres) :
    ∃ Csource : ℝ, 0 < Csource ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 →
      ∀ᶠ tau : ℕ in atTop,
        1 ≤ tau ∧
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
          ∀ P : Coord → ℝ,
            (∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
              |qResidual (metricInShearCoordinates gStar q0) P p| ≤ Cres/(tau : ℝ)^N) →
            ∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
              |actualComparisonSource gStar (perturbedMetric g0 eta.val) z q0 P p| ≤
                Csource*(tau : ℝ)^2/(tau : ℝ)^N := by
  let L := boundedClassWidth kappa M
  let a := L*r/16
  let c := (boundedClassSpeed kappa M)^2/(4*(M : ℝ))
  let BQ := max (8*G) (boundedClassShearedStateBudget q0 M)
  have ha : 0 < a := div_pos (mul_pos (boundedClassWidth_pos kappa M) hr) (by norm_num)
  have hc : 0 < c := by
    have hh := boundedClassShearHxxFloor_pos hkappa hM
    have he : c=((boundedClassSpeed kappa M)^2/(2*(M : ℝ)))/2 := by dsimp only [c]; ring
    rw [he]
    exact half_pos hh
  obtain ⟨_,A,D,dcompare,_,hA,hD,hdcompare,happlicable⟩ :=
    exists_actual_Q_applicability_at_radius hgStar hV hSV M hG hd hgStarB hdStar
      hkappa hM hq0 hr hrhalf hLr hrsmall N hN
  obtain ⟨H,Cfirst,Ctest,Ccompare,_,hCf,_,hCc,hsource⟩ :=
    exists_actual_comparison_source_pointwise_bound (8*G) (G+1) BQ D A Cres
      hd hdcompare hc hD hA ha N (by omega)
  let Csource := 2*A*pulseLeadingBound a ha+1
  have hCs : 0 < Csource := by
    have hpulse := pulseLeadingBound_nonneg ha
    dsimp only [Csource]
    positivity
  refine ⟨Csource,hCs,?_⟩
  intro delta hdelt hdhalf
  obtain ⟨T,_,hsourceT⟩ := hsource delta hdelt
  let Q := 8+scalarPulseFirstJetBound a ha delta
  have hlarge : ∀ᶠ tau : ℕ in atTop,
      T ≤ (tau : ℝ) ∧
      comparisonLowerSourceCoefficient A Cfirst Ctest Ccompare Cres 1 Q a ha delta ≤ (tau : ℝ) := by
    apply (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (p := fun t : ℝ => T ≤ t ∧
        comparisonLowerSourceCoefficient A Cfirst Ctest Ccompare Cres 1 Q a ha delta ≤ t)
    filter_upwards [eventually_ge_atTop T,
      eventually_ge_atTop (comparisonLowerSourceCoefficient A Cfirst Ctest Ccompare Cres 1 Q a ha delta)]
      with t ht hscale
    exact ⟨ht,hscale⟩
  filter_upwards [happlicable delta hdelt hdhalf,
    actual_Q_approximation_eventual_margins (G+1) BQ H hd hdcompare hc ha N (by omega) delta,hlarge]
    with tau hactual hmarg hlargeTau
  rcases hmarg with ⟨ht2,_,_,heps1,hepsSmall,hepsScale,_,hepsQ1,hepsQSmall,hxxSmall⟩
  have ht1 : 1 ≤ tau := by omega
  have htR : (1 : ℝ) ≤ tau := by exact_mod_cast ht1
  refine ⟨ht1,?_⟩
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ P hres p hp
  let g := perturbedMetric g0 eta.val
  have hSU : modelSquare ⊆ U := hf.squareSubset.trans hf.domainSubset
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
  have hOV : modelOpenSquare ⊆ V := modelOpenSquare_subset.trans hSV
  have hgO : SmoothPositiveOn g modelOpenSquare :=
    ⟨fun i j => (hg.1 i j).mono hOU,fun p hp => hg.2 p (hOU hp)⟩
  have hgStarO : SmoothPositiveOn gStar modelOpenSquare :=
    ⟨fun i j => (hgStar.1 i j).mono hOV,fun p hp => hgStar.2 p (hOV hp)⟩
  have hzO := hh.smooth.mono hOU
  have hpoint := hactual.2.2.2 g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have hb := hsourceT (tau : ℝ) hlargeTau.1 gStar g q0 modelOpenSquare hgStarO hactual.2.2.1 hgO
    modelOpenSquare_isOpen z P hzO (metricApproximationAccuracy tau)
    (qPulseFirstJetBudget a ha N delta (tau : ℝ))
    heps1 hepsSmall hepsQ1 hepsQSmall hxxSmall p (hpoint p hp).1 (hres p hp)
  apply hb.trans
  apply comparisonSourceBudget_le_leading (E := 1) (Q := Q) ha N hA hCf hCc hCres htR
  · simpa only [one_mul] using hepsScale
  · exact le_rfl
  · exact hlargeTau.2

end SmoothLocal.Perturbation

end

end OAI
