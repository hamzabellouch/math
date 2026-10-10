import OAI.Geometry.IsometricImmersion.Estimates.ActualQApplicability
import OAI.Geometry.IsometricImmersion.Comparison.QApproximationMargins
import OAI.Geometry.IsometricImmersion.Estimates.ActualQMomentPositive

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_class_Q_forcing_moment_at_radius
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
    ∃ c3 : ℝ, 0 < c3 ∧ ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 →
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
          c3*delta*(tau : ℝ)/(tau : ℝ)^N ≤
            |pulseWeightedMoment (boundedClassWidth kappa M*r/16) delta (tau : ℝ)
              (actualShearedQForcing gStar (perturbedMetric g0 eta.val) z q0)| := by
  let L := boundedClassWidth kappa M
  let a := L*r/16
  let c := (boundedClassSpeed kappa M)^2/(4*(M : ℝ))
  let e := (1/(M : ℝ))/2
  let BQ := max (8*G) (boundedClassShearedStateBudget q0 M)
  have ha : 0 < a := div_pos (mul_pos (boundedClassWidth_pos kappa M) hr) (by norm_num)
  have hc : 0 < c := by
    have hh := boundedClassShearHxxFloor_pos hkappa hM
    have heq : c=((boundedClassSpeed kappa M)^2/(2*(M : ℝ)))/2 := by dsimp only [c]; ring
    rw [heq]
    exact half_pos hh
  have he : 0 < e := half_pos (one_div_pos.mpr (Nat.cast_pos.mpr hM))
  obtain ⟨Aref,A,D,dcompare,_,hA,hD,hdcompare,happlicable⟩ :=
    exists_actual_Q_applicability_at_radius hgStar hV hSV M hG hd hgStarB hdStar
      hkappa hM hq0 hr hrhalf hLr hrsmall N hN
  obtain ⟨c3,H,_,_,_,hc3,_,_,_,_,hforcing⟩ :=
    exists_actual_Q_moment_positive_lower (8*G) (G+1) BQ D A (2*G^2) Aref
      hd hdcompare hc he hD hA ha N (by omega)
  refine ⟨c3,hc3,?_⟩
  intro delta hdelt hdhalf
  obtain ⟨T,_,hforcingT⟩ := hforcing delta hdelt
  have hlarge : ∀ᶠ tau : ℕ in atTop, T ≤ (tau : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop T)
  filter_upwards [happlicable delta hdelt hdhalf,
    actual_Q_approximation_eventual_margins (G+1) BQ H hd hdcompare hc ha N (by omega) delta,hlarge]
    with tau hactual hmarg ht
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
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
  have hsubset : pulseStrip a delta (tau : ℝ) ⊆ pulseStrip (L*r/2) delta (tau : ℝ) := by
    intro p hp
    refine ⟨⟨?_,?_⟩,hp.2⟩ <;> dsimp only [a] at hp <;>
      linarith [hp.1.1,hp.1.2,mul_pos (boundedClassWidth_pos kappa M) hr]
  rcases hmarg with ⟨_,_,heps,heps1,hepsSmall,hepsScale,hepsQ,hepsQ1,hepsQSmall,hxxSmall⟩
  exact hforcingT (tau : ℝ) ht gStar g q0 modelOpenSquare hgStarO hactual.2.2.1 hgO
    modelOpenSquare_isOpen z hzO (metricApproximationAccuracy tau) (qPulseFirstJetBudget a ha N delta (tau : ℝ))
      heps hepsQ heps1 hepsSmall hepsQ1 hepsQSmall hxxSmall hepsScale le_rfl
      (fun p hp => (hpoint p (hsubset hp)).1)
      (fun p hp => (hpoint p (hsubset hp)).2.2.2.2.2)
      (fun p hp => (hpoint p (hsubset hp)).2.1)
      (fun p hp => (hpoint p (hsubset hp)).2.2.2.1)
      (fun p hp => (hpoint p (hsubset hp)).2.2.1)

end SmoothLocal.Perturbation

end

end OAI
