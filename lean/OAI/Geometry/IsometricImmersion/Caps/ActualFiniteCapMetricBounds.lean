import OAI.Geometry.IsometricImmersion.Pulses.ActualTwoSidedPulseSeparation
import OAI.Geometry.IsometricImmersion.Comparison.FiniteApproximationJets
import OAI.Geometry.IsometricImmersion.Calculus.FiniteUpperMetricJets

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.Flow.Reflection
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.HighEquation

def finiteCapRequiredMetricOrder (nLower nUpper : ℕ) : ℕ :=
  max (max 8 (nLower+3)) (max 8 (nUpper+3))

theorem exists_actual_finite_cap_metric_budgets
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G Z d c e0 kappa q0 L : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hL : 0 < L) (hq0 : |q0| ≤ 1/20) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ L*r ≤ 1/20 ∧
      heightQuotientJetBound G Z d c*(r+107*(L*r)/100) ≤ 9/(100*L) ∧
      ∀ nLower nUpper : ℕ, ∃ B : ℝ, 0 ≤ B ∧
        ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
          ∀ᶠ tau : ℕ in atTop, finiteCapRequiredMetricOrder nLower nUpper ≤ tau ∧
            ∀ (gTau : MetricField) (U W : Set Coord) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
              SmoothPositiveOn gTau U → IsOpen U →
              CapInductionHeight gTau U Z c e0 z →
              CapInductionFlow gTau U G Z d c e0 kappa z Y W →
              |hessianQuotient gTau z 0-q0| ≤ 1/(100*L) →
              (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
                ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
                  testMetric gStar q0 (L*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                    metricApproximationAccuracy tau) →
              (∀ R : LowerCapRectangle (-r/2),
                FiniteCapMetricJets gTau Y (fun _ _ => B) (lowerCapPointwiseRequests nLower R)) ∧
              (∀ R : UpperCapRectangle (r/2),
                FiniteUpperCapMetricJets gTau Y (fun _ _ => B) (upperCapPointwiseRequests nUpper R)) := by
  obtain ⟨r,hr,hrhalf,hLr,hrsmall,hsep⟩ :=
    exists_uniform_actual_two_sided_pulse_exclusion (e0 := e0) (kappa := kappa)
      hG hZ hd hc hL hq0
  refine ⟨r,hr,hrhalf,hLr,hrsmall,?_⟩
  intro nLower nUpper
  let m := finiteCapRequiredMetricOrder nLower nUpper
  obtain ⟨Bstar,hBstar,hbase⟩ := fixed_metric_finite_coefficient_jet_bound hgStar hV hSV m
  refine ⟨Bstar+1,add_nonneg hBstar zero_le_one,?_⟩
  intro N delta hdelta
  filter_upwards [hsep N delta hdelta,eventually_ge_atTop m] with tau htau hm
  refine ⟨hm,?_⟩
  intro gTau U W z Y hgTau hU hh hf hcenter happrox
  obtain ⟨hsepLower,hsepUpper⟩ := htau.2 gTau gStar U W z Y hh hf hcenter
  have herror := metricApproximationAccuracy_le_one htau.1
  have hbound (i j : Fin 2) (k : ℕ) (hk : k ≤ m) (p : Coord) (hpS : p ∈ modelSquare)
      (heq : testMetric gStar q0 (L*r/16) N delta (tau : ℝ) =ᶠ[𝓝 p] gStar) :
      ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ Bstar+1 := by
    have h := metric_jet_norm_le_of_approximation_locality hgStar hgTau hV hU
      (hSV hpS) (hf.domainSubset (hf.squareSubset hpS)) heq i j k
      (hbase i j k hk p hpS) (happrox i j k (hk.trans hm) p hpS)
    exact h.trans (add_le_add le_rfl herror)
  constructor
  · intro R b hb i j k hk p hp
    have hkM : k ≤ m :=
      (lowerCapPointwiseRequests_full_order_le nLower R b hb hk).trans (le_max_left _ _)
    exact hbound i j k hkM p (hf.image_subset_square b.2 hp) (hsepLower b.2 p hp)
  · intro R b hb i j k hk p hp
    have hkM : k ≤ m :=
      (upperCapPointwiseRequests_full_order_le nUpper R b hb hk).trans (le_max_right _ _)
    have hpS : p ∈ modelSquare :=
      (b.2.image_properties (capChart_contDiffOn hf.jointSmooth) hf.displacement).2.2 hp
    exact hbound i j k hkM p hpS (hsepUpper b.2 p hp)

end SmoothLocal.Pulse

end

end OAI
