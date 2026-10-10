import OAI.Geometry.IsometricImmersion.Caps.ActualFiniteCapMetricBounds

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted
open SmoothLocal.HighEquation SmoothLocal.Analytic

theorem exists_actual_finite_lower_cut_height_bounds
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G Z d c e0 kappa q0 L : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hL : 0 < L) (hq0 : |q0| ≤ 1/20) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ L*r ≤ 1/20 ∧
      heightQuotientJetBound G Z d c*(r+107*(L*r)/100) ≤ 9/(100*L) ∧
      ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
          ∀ᶠ tau : ℕ in atTop,
            ∀ (gTau : MetricField) (U W : Set Coord) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
              SmoothPositiveOn gTau U → IsOpen U →
              (∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
                ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ G) →
              (∀ p ∈ modelSquare, d ≤ |(gTau p).det|) →
              CapInductionHeight gTau U Z c e0 z →
              CapInductionFlow gTau U G Z d c e0 kappa z Y W →
              |hessianQuotient gTau z 0-q0| ≤ 1/(100*L) →
              (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
                ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
                  testMetric gStar q0 (L*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                    metricApproximationAccuracy tau) →
              ∀ ds : List (Fin 2), ds.length ≤ n → ∀ t : ℝ, |t| ≤ L*r →
                |iteratedCoordPartial ds z (inverseShearCoordinates q0 (boxPoint t (-r)))| ≤ C := by
  obtain ⟨r,hr,hrhalf,hLr,hrsmall,hmetric⟩ :=
    exists_actual_finite_cap_metric_budgets (e0 := e0) (kappa := kappa)
      hgStar hV hSV hG hZ hd hc hL hq0
  refine ⟨r,hr,hrhalf,hLr,hrsmall,?_⟩
  intro n
  obtain ⟨Bmetric,hBmetric,hlocal⟩ := hmetric n 0
  let R := lowerCutRectangle L r hL hr hrhalf hLr
  let J : CapMetricJetBudget (-r/2) := fun _ _ => Bmetric
  obtain ⟨C,hC,hheight⟩ := uniform_finite_varying_lowerCap_pointwise
    G Z d c e0 kappa hG hZ hd hc J n R (fun _ _ => hBmetric)
  refine ⟨C,hC,?_⟩
  intro N delta hdelta
  filter_upwards [hlocal N delta hdelta] with tau htau
  intro gTau U W z Y hgTau hU hg4 hdet hh hf hcenter happrox ds hds t ht
  have hrequests : FiniteCapMetricJets gTau Y J (lowerCapPointwiseRequests n R) :=
    (htau.2 gTau U W z Y hgTau hU hh hf hcenter happrox).1 R
  have hbound := hheight gTau U z Y W hgTau hU (hf.squareSubset.trans hf.domainSubset)
    hg4 hdet hh hf hrequests
  have hp : inverseShearCoordinates q0 (boxPoint t (-r)) ∈ R.image Y :=
    actual_lower_cut_in_cap_image hh hf hG hZ hd hc hL hr hrhalf hLr hq0 hcenter hrsmall ht
  exact hbound ds hds _ hp

end SmoothLocal.Pulse

end

end OAI
