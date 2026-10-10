import OAI.Probability.BenjaminiSchramm.PeakLayerCost
import OAI.Probability.BenjaminiSchramm.PeakSprinklingCost

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma exponential_continuation_cost_summable (g : ℕ → ℝ) (C a : ℝ)
    (hg : ∀ l, 0 ≤ g l) (hC : 0 ≤ C) (hb : ∀ l, g l ≤ C)
    (ha : 0 < a) (n : ℕ) :
    Summable (fun l => g l*Real.exp (-a*max ((l : ℝ)-n) 0)) := by
  simp_rw [exponential_continuation_weight]
  exact (geometric_continuation_cost_bound g C (Real.exp (-a)) hg hC hb
    (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)) n).1

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem peakSurvivalCostMoment_bound (O : G.OrbitRepresentatives) (a : V → ℝ)
    (R : ℝ) (p : unitInterval) (g : ℕ → ℝ) (hg : ∀ l, 0 ≤ g l)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀) (hgb : ∀ l, g l ≤ C₀)
    (A C : ℝ) (hA : 0 < A) (hC : 0 ≤ C) (n : ℕ)
    (hprofile : ∀ l : ℕ, G.peakSurvivalLayerMoment O a R p n l ≤
      G.peakSurvivalProbability O a R p n *
        ENNReal.ofReal (C*Real.exp (-A*max ((l : ℝ)-n) 0))) :
    (∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω,
      {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x}.indicator
        (fun η => G.downwardLayerCost a R g η x) ω ∂G.law p)) ≤
      G.peakSurvivalProbability O a R p n *
        ENNReal.ofReal (C*(∑' l, g l*Real.exp (-A*max ((l : ℝ)-n) 0))) := by
  rw [G.peakSurvivalCostMoment_eq]
  let P := G.peakSurvivalProbability O a R p n
  let f : ℕ → ℝ := fun l => g l*Real.exp (-A*max ((l : ℝ)-n) 0)
  have hf : ∀ l, 0 ≤ f l := fun l => mul_nonneg (hg l) (Real.exp_nonneg _)
  have hs : Summable f := exponential_continuation_cost_summable g C₀ A hg hC₀ hgb hA n
  have he (l : ℕ) : ENNReal.ofReal (g l)*(P*ENNReal.ofReal
      (C*Real.exp (-A*max ((l : ℝ)-n) 0)))=(P*ENNReal.ofReal C)*ENNReal.ofReal (f l) := by
    rw [ENNReal.ofReal_mul hC,show f l=g l*Real.exp (-A*max ((l : ℝ)-n) 0) from rfl,
      ENNReal.ofReal_mul (hg l)]
    ring
  calc
    _ ≤ ∑' l, ENNReal.ofReal (g l)*(P*ENNReal.ofReal
        (C*Real.exp (-A*max ((l : ℝ)-n) 0))) :=
      ENNReal.tsum_le_tsum fun l => mul_le_mul' le_rfl (hprofile l)
    _ = (P*ENNReal.ofReal C)*(∑' l, ENNReal.ofReal (f l)) := by
      simp_rw [he]
      exact ENNReal.tsum_mul_left
    _ = _ := by
      rw [←ENNReal.ofReal_tsum_of_nonneg hf hs,mul_assoc,←ENNReal.ofReal_mul hC]

end CriticalPercolation.BondGraph

end

end OAI
