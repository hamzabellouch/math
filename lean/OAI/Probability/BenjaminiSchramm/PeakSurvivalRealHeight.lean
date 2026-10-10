import OAI.Probability.BenjaminiSchramm.PeakConditionalLayers
import OAI.Probability.BenjaminiSchramm.WeightedPeakSlabComparison

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma positive_peakDownBandCount_subset_fullPeakDownHit
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (l u ell : ℝ) (hell : ell ≤ l) (x : V) :
    {ω | 0 < G.peakDownBandCount a l u ω x} ⊆ G.fullPeakDownHit a ell x := by
  intro ω hω
  change 0 < G.peakDownBandCount a l u ω x at hω
  have he : ∃ y, l < G.orbitAdjustedHeight a y x ∧ G.orbitAdjustedHeight a y x ≤ u ∧
      ω ∈ strictHeightPeakConnection G.ends (G.orbitAdjustedHeight a y) y x := by
    by_contra hn
    have hz : G.peakDownBandCount a l u ω x=0 := ENNReal.tsum_eq_zero.mpr fun y =>
      ite_eq_right (fun hy => hn ⟨y,hy⟩)
    rw [hz] at hω
    exact lt_irrefl _ hω
  obtain ⟨y,hylo,_hyhi,hxy,hpeak⟩ := he
  refine ⟨⟨Percolation.conn_refl G.ends ω x,?_⟩,y,?_,?_⟩
  · intro z hxz hzx
    have hz := hpeak z hxz hzx
    rw [G.orbitAdjustedHeight_change_base hc hl a y x z] at hz
    rw [G.orbitAdjustedHeight_self]
    linarith
  · change G.orbitAdjustedHeight a x y ≤ -ell
    rw [G.orbitAdjustedHeight_reverse hc hl a x y] at hylo
    linarith
  · simpa only [Set.inter_univ] using Percolation.conn_symm G.ends ω hxy

lemma peakSurvivalProbability_le_fullPeakDownProbability
    (O : G.OrbitRepresentatives) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R : ℝ) (p : unitInterval) (n : ℕ) (ell : ℝ)
    (hell : ell ≤ R*((n : ℝ)+1)) :
    G.peakSurvivalProbability O a R p n ≤ G.fullPeakDownProbability O a p ell := by
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_mul' le_rfl (measure_mono
    (G.positive_peakDownBandCount_subset_fullPeakDownHit hc hl a _ _ ell hell x))

theorem full_peak_survival_real_lower
    (O : G.OrbitRepresentatives) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R : ℝ) (hR : 0 < R) (p : unitInterval)
    (c b : ℝ) (hcpos : 0 < c) (hb : 0 ≤ b)
    (hsurv : ∀ n : ℕ, 0 < n → ENNReal.ofReal (c*Real.exp (-b*n)) ≤
      G.peakSurvivalProbability O a R p n) (ell : ℝ) (hell : 0 < ell) :
    ENNReal.ofReal ((c*Real.exp (-2*b))*Real.exp (-(b/R)*ell)) ≤
      G.fullPeakDownProbability O a p ell := by
  let n : ℕ := ⌈ell/R⌉₊+1
  have hnpos : 0 < n := Nat.zero_lt_succ _
  have hnlo : ell ≤ R*(n : ℝ) := by
    have hh := (div_le_iff₀ hR).mp (Nat.le_ceil (ell/R))
    dsimp [n]
    push_cast
    nlinarith
  have hnhi : (n : ℝ) ≤ ell/R+2 := by
    have hh := (Nat.ceil_lt_add_one (div_nonneg hell.le hR.le)).le
    dsimp [n]
    push_cast
    linarith
  have he : (c*Real.exp (-2*b))*Real.exp (-(b/R)*ell) = c*Real.exp (-b*(ell/R+2)) := by
    rw [mul_assoc,←Real.exp_add]
    congr 2
    ring
  calc
    _ ≤ ENNReal.ofReal (c*Real.exp (-b*n)) := by
      apply ENNReal.ofReal_le_ofReal
      rw [he]
      apply mul_le_mul_of_nonneg_left _ hcpos.le
      apply Real.exp_le_exp.mpr
      nlinarith
    _ ≤ G.peakSurvivalProbability O a R p n := hsurv n hnpos
    _ ≤ _ := G.peakSurvivalProbability_le_fullPeakDownProbability O hc hl a R p n ell (by nlinarith)

end CriticalPercolation.BondGraph

end

end OAI
