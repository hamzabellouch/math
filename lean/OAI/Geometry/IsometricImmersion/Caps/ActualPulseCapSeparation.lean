import OAI.Geometry.IsometricImmersion.Caps.PulseCapSeparation
import OAI.Geometry.IsometricImmersion.Darboux.QSegmentDomain

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted
open SmoothLocal.HighEquation

theorem metric_jets_eq_on_actual_qJetSegment
    {g h : MetricField} {p : Coord} (heq : g =ᶠ[𝓝 p] h)
    (z0 z : Coord → ℝ) (sigma : ℝ) (n : ℕ) (i j : Fin 2) :
    iteratedFDeriv ℝ n (fun v => g v i j) (statePoint (qHeightJetSegment z0 z sigma p)) =
      iteratedFDeriv ℝ n (fun v => h v i j) (statePoint (qHeightJetSegment z0 z sigma p)) := by
  rw [statePoint_qHeightJetSegment]
  exact ((metric_coeff_eventuallyEq heq i j).iteratedFDeriv ℝ n).self_of_nhds

theorem exists_uniform_actual_pulse_cap_exclusion
    {G Z d c e0 kappa q0 L : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hL : 0 < L) (hq0 : |q0| ≤ 1/20) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ L*r ≤ 1/20 ∧
      ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
        ∀ᶠ tau : ℝ in atTop, 1 ≤ tau ∧
          ∀ (g gStar : MetricField) (U W : Set Coord) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
            CapInductionHeight g U Z c e0 z → CapInductionFlow g U G Z d c e0 kappa z Y W →
            |hessianQuotient g z 0-q0| ≤ 1/(100*L) →
            ∀ R : LowerCapRectangle (-r/2), ∀ p ∈ R.image Y,
              testMetric gStar q0 (L*r/16) N delta tau =ᶠ[𝓝 p] gStar ∧
              ∀ (z0 : Coord → ℝ) (sigma : ℝ) (n : ℕ) (i j : Fin 2),
                iteratedFDeriv ℝ n (fun v => testMetric gStar q0 (L*r/16) N delta tau v i j)
                  (statePoint (qHeightJetSegment z0 z sigma p)) =
                iteratedFDeriv ℝ n (fun v => gStar v i j)
                  (statePoint (qHeightJetSegment z0 z sigma p)) := by
  let M := heightQuotientJetBound G Z d c
  have hM : 0 ≤ M := heightQuotientJetBound_nonneg hG hZ hd hc
  obtain ⟨r,hr,hrhalf,hLr,hrsmall⟩ := exists_sectionFour_radius hM hL
  refine ⟨r,hr,hrhalf,hLr,?_⟩
  intro N delta hdelta
  filter_upwards [pulse_width_eventually hr delta] with tau htau
  refine ⟨htau.1,?_⟩
  intro g gStar U W z Y hh hf hcenter R p hp
  have hpartial (v : Coord) (hv : v ∈ modelSquare) (i : Fin 2) :
      |coordPartial i (hessianQuotient g z) v| ≤ M := hf.quotientBound [i] (by norm_num) v hv
  have hLrpos : 0 < L*r := mul_pos hL hr
  have heq := testMetric_eventuallyEq_on_lower_cap hf.quotientSmooth hf.domainOpen hf.squareSubset
    hf.continuous hf.range hf.start hf.ode hh.quotient hM hL hr hpartial hq0 hcenter
    (by linarith : L*r < 2) (by positivity : 0 < L*r/16) (by linarith : L*r/16 ≤ L*r)
    hrsmall hdelta (by linarith [htau.1] : 0 < tau) htau.2 gStar N R hp
  refine ⟨heq,?_⟩
  intro z0 sigma n i j
  exact metric_jets_eq_on_actual_qJetSegment heq z0 z sigma n i j

end SmoothLocal.Pulse

end

end OAI
