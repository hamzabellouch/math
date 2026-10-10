import OAI.Probability.BenjaminiSchramm.PeakBandSecondMoment
import OAI.Probability.BenjaminiSchramm.WeightedMomentCauchy

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma peakDownBandCount_le_full_count (a : V → ℝ) (l u : ℝ) (ω : Set E) (x : V) :
    G.peakDownBandCount a l u ω x ≤
      restrictedLayerCount G.ends Set.univ Set.univ ω x := by
  apply ENNReal.tsum_le_tsum
  intro y
  by_cases h : l < G.orbitAdjustedHeight a y x ∧ G.orbitAdjustedHeight a y x ≤ u ∧
      ω ∈ strictHeightPeakConnection G.ends (G.orbitAdjustedHeight a y) y x
  · have hc := Percolation.conn_symm G.ends ω h.2.2.1
    simp only [peakUpBandTransport,ite_eq_left h,Set.mem_univ,true_and,Set.inter_univ,
      ite_eq_left hc,le_refl]
  · rw [peakUpBandTransport,ite_eq_right h]
    exact bot_le

variable [Countable V] [Countable E]

theorem weighted_peakDownBandCount_cauchy
    (O : G.OrbitRepresentatives) (a : V → ℝ) (l u : ℝ) (p : unitInterval)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hrow : ∀ x, (∑' y, G.law p {ω | Percolation.Conn G.ends ω x y}) ≤ C)
    (hsecond : ∀ x ∈ O.roots, (∫⁻ ω, (G.peakDownBandCount a l u ω x)^2 ∂G.law p) ≠ ⊤) :
    (∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω, G.peakDownBandCount a l u ω x ∂G.law p))^2 ≤
      (∑ x ∈ O.roots, ENNReal.ofReal (a x)*G.law p {ω | 0 < G.peakDownBandCount a l u ω x})*
        (∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω, (G.peakDownBandCount a l u ω x)^2 ∂G.law p)) := by
  apply weighted_lintegral_support_cauchy (G.law p) O.roots _ _ _
    (fun _ _ => ENNReal.ofReal_ne_top)
    (fun x _ => measurableSet_lt measurable_const (G.measurable_peakDownBandCount a l u x))
    (fun x _ => G.measurable_peakDownBandCount a l u x)
    (fun x _ ω hω => le_antisymm (le_of_not_gt hω) bot_le)
    (fun _ _ => measure_ne_top _ _) _ hsecond
  intro x _
  apply ne_top_of_le_ne_top hC
  exact (lintegral_mono fun ω => G.peakDownBandCount_le_full_count a l u ω x).trans
    (restrictedLayerCount_expectation_le_row_bound G.ends p C hrow _ _ x)

theorem peakDownBandCount_probability_lower_of_moments
    (O : G.OrbitRepresentatives) (a : V → ℝ) (l u : ℝ) (p : unitInterval)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hrow : ∀ x, (∑' y, G.law p {ω | Percolation.Conn G.ends ω x y}) ≤ C)
    (c D t : ℝ) (hc : 0 < c) (hD : 0 < D) (ht : 0 < t)
    (hlower : ENNReal.ofReal (c*t) ≤
      ∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω, G.peakDownBandCount a l u ω x ∂G.law p))
    (hsecond : ∀ x ∈ O.roots, (∫⁻ ω, (G.peakDownBandCount a l u ω x)^2 ∂G.law p) ≠ ⊤)
    (hupper : (∑ x ∈ O.roots, ENNReal.ofReal (a x)*
      (∫⁻ ω, (G.peakDownBandCount a l u ω x)^2 ∂G.law p)) ≤ ENNReal.ofReal (D*t)) :
    ENNReal.ofReal (c^2/D*t) ≤
      ∑ x ∈ O.roots, ENNReal.ofReal (a x)*G.law p {ω | 0 < G.peakDownBandCount a l u ω x} := by
  let Q := ∑ x ∈ O.roots, ENNReal.ofReal (a x)*G.law p {ω | 0 < G.peakDownBandCount a l u ω x}
  have hQ : Q ≠ ⊤ := ENNReal.sum_ne_top.mpr fun x _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hh := (pow_le_pow_left' hlower 2).trans
    ((G.weighted_peakDownBandCount_cauchy O a l u p C hC hrow hsecond).trans (mul_le_mul' le_rfl hupper))
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top hQ ENNReal.ofReal_ne_top) hh
  rw [ENNReal.toReal_pow,ENNReal.toReal_ofReal (mul_nonneg hc.le ht.le),
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (mul_nonneg hD.le ht.le)] at hreal
  have he : c^2*t ≤ Q.toReal*D := (mul_le_mul_iff_right₀ ht).mp (by nlinarith)
  apply ENNReal.ofReal_le_of_le_toReal
  calc
    c^2/D*t = (c^2*t)/D := by ring
    _ ≤ Q.toReal := (div_le_iff₀ hD).mpr he

end CriticalPercolation.BondGraph

end

end OAI
