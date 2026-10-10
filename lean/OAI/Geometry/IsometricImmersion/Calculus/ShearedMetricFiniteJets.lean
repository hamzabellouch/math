import OAI.Geometry.IsometricImmersion.Pulses.OffPulseMetricBounds
import OAI.Geometry.IsometricImmersion.Calculus.ShearMetricJets

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted
open SmoothLocal.HighEquation SmoothLocal.Hyperbolic

theorem exists_uniform_off_pulse_sheared_metric_bounds
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {q0 L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hrhalf : r < 1/2)
    (hLr : L*r ≤ 1/20) (hq0 : |q0| ≤ 1/20) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
      ∀ tau : ℕ, 1 ≤ tau → m ≤ tau →
      ∀ (gTau : MetricField) (U : Set Coord), SmoothPositiveOn gTau U → IsOpen U → modelSquare ⊆ U →
      (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
          testMetric gStar q0 (L*r/16) N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau) →
      ∀ i j : Fin 2, CoordinateBound (fun p => metricInShearCoordinates gTau q0 p i j)
        {p | |p 0| ≤ L*r ∧ p 1 ∈ Icc (-r) (-delta/(tau : ℝ))} m B := by
  obtain ⟨B,hB,hjets⟩ := exists_uniform_off_pulse_metric_jets hgStar hV hSV
    hL hr hrhalf hLr hq0 m
  refine ⟨shearedMetricCoordinateBudget B q0 m,
    shearedMetricCoordinateBudget_nonneg q0 m hB,?_⟩
  intro N delta hd tau htau hmtau gTau U hgTau hU hSU happrox
  let T : Set Coord := {p | |p 0| ≤ L*r ∧ p 1 ∈ Icc (-r) (-delta/(tau : ℝ))}
  let S : Set Coord := inverseShearCoordinates q0 '' T
  have htr : (0 : ℝ) < tau := zero_lt_one.trans_le (by exact_mod_cast htau)
  have ht0 : -delta/(tau : ℝ) < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hd) htr
  have hpS (p : Coord) (hp : p ∈ T) : inverseShearCoordinates q0 p ∈ modelSquare := by
    apply sectionFourClosedSlab_mem_shearedModelSquare hr hrhalf hLr hq0
    exact ⟨hp.1,abs_le.mpr ⟨hp.2.1,(hp.2.2.trans ht0.le).trans hr.le⟩⟩
  have hsub : S ⊆ U := by
    rintro y ⟨p,hp,rfl⟩
    exact hSU (hpS p hp)
  have hb (i j : Fin 2) : CoordinateBound (fun p => gTau p i j) S m B := by
    apply coordinateBound_of_frechet_bounds (hgTau.1 i j) hU hsub
    intro k hk y hy
    obtain ⟨p,hp,rfl⟩ := hy
    have he : ![p 0,p 1] = p := by ext a; fin_cases a <;> rfl
    simpa only [he] using hjets N delta hd tau htau hmtau gTau U hgTau hU hSU happrox
      (p 0) (p 1) hp.1 hp.2 i j k hk
  have hs := metric_coordinate_bound_inverse_shear hgTau hU hsub hB hb q0
  intro i j ds hds p hp
  exact hs i j ds hds p ⟨p,hp,rfl⟩

end SmoothLocal.Pulse

end

end OAI
