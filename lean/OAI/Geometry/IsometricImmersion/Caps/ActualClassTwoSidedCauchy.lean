import OAI.Geometry.IsometricImmersion.Caps.ActualUpperOffPulseCauchy
import OAI.Geometry.IsometricImmersion.Metrics.ActualLowMetricFloor
import OAI.Geometry.IsometricImmersion.Caps.BoundedClassCapData

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.Flow SmoothLocal.ODE
open SmoothLocal.HighEquation SmoothLocal.Weighted SmoothLocal.Taylor SmoothLocal.Model

theorem exists_actual_class_two_sided_cauchy_bounds_at_every_radius
    {g0 gStar : MetricField} {V : Set Coord}
    (hg0 : SmoothPositiveOn g0 V) (hgStar : SmoothPositiveOn gStar V)
    (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {kappa q0 : ℝ} (M : ℕ) (hkappa : 0 < kappa) (hM : 0 < M)
    (hq0 : |q0| ≤ 1/20)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p = modelCurvature kappa p) :
    ∃ G d : ℝ, 0 < G ∧ 0 < d ∧
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
      ∀ r : ℝ, 0 < r → r < 1/2 → boundedClassWidth kappa M*r ≤ 1/20 →
      heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
        (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M) →
      ∀ K : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 10 < N → ∀ delta : ℝ, 0 < delta →
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
                (delta/(tau : ℝ))) x‖ ≤ B) := by
  obtain ⟨G,d,hG,hd,hGstar,hdstar,hlow⟩ :=
    exists_actual_low_metric_data_before_pulse_parameters hgStar hV hSV 8
  let L := boundedClassWidth kappa M
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hc : 0 < 1/(M : ℝ) := one_div_pos.mpr hMR
  refine ⟨G,d,hG,hd,hGstar,hdstar,?_,?_⟩
  · intro a ha N hN delta
    filter_upwards [hlow q0 a ha N (by omega) delta] with tau htau
    exact htau.2
  intro r hr hrhalf hLr hrsmall K
  obtain ⟨BL,hBL,hLbound⟩ := exists_actual_off_pulse_cauchy_bounds_at_radius
    hgStar hV hSV M hG.le hd hkappa hM hq0 hr hrhalf hLr hrsmall K
  obtain ⟨BU,hBU,hUbound⟩ := exists_actual_upper_off_pulse_cauchy_bounds_at_radius
    hgStar hV hSV M hG.le hd hkappa hM hq0 hr hrhalf hLr hrsmall K
  refine ⟨BL+BU,add_nonneg hBL hBU,?_⟩
  intro N hN delta hdelt
  have ha : 0 < L*r/16 := by positivity
  filter_upwards [hlow q0 (L*r/16) ha N (by omega) delta,
    hLbound N delta hdelt,hUbound N delta hdelt] with tau hlowTau hLTau hUTau
  intro eta z hclass hcenter happ x hx n hn
  obtain ⟨U,hU,hSU,hUV,hg0U,hgU,hh⟩ := bounded_class_actual_cap_data hg0 hV hSV eta hclass
  have hlowActual := hlowTau.2 (perturbedMetric g0 eta.val) U hgU hU hSU happ
  have hg8 := hlowActual.1
  have hdet := hlowActual.2
  have hg4 : ∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j) p‖ ≤ G :=
    fun i j k hk p hp => hg8 i j k (by omega) p hp
  have hmodel : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p :=
    fun p hp => hbackground p (hUV hp)
  obtain ⟨W,Y,hf⟩ := exists_capInductionFlow hgU hU hSU hG.le (Nat.cast_nonneg M)
    hd hc hc hg8 hdet hh hkappa hmodel (perturbationTensor_tsupport_subset eta.val) eta.property.2
  have hleft := hLTau g0 eta U W z Y hgU hU hh hf hclass hg4 hdet hcenter happ x hx n hn
  have hright := hUTau g0 eta U z hg0U hgU hU hSU hmodel hh hclass hg8 hdet hcenter happ x hx n hn
  have hBLsum : BL ≤ BL+BU := by
    calc
      BL = BL+0 := by ring
      _ ≤ BL+BU := add_le_add le_rfl hBU
  have hBUsum : BU ≤ BL+BU := by
    calc
      BU = 0+BU := by ring
      _ ≤ BL+BU := add_le_add hBL le_rfl
  exact ⟨⟨hleft.1.trans hBLsum,hleft.2.trans hBLsum⟩,
    ⟨hright.1.trans hBUsum,hright.2.trans hBUsum⟩⟩

end SmoothLocal.Perturbation

end

end OAI
