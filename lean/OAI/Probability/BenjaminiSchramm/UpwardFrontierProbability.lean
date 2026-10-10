import OAI.Probability.BenjaminiSchramm.IntegerFrontierCrossing
import OAI.Probability.BenjaminiSchramm.SubcriticalUpperSecondMoment

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def supAdjustedFrontierProbability (a : V → ℝ) (R : ℝ) (p : unitInterval) (n : ℕ) : ℝ≥0∞ :=
  ⨆ x, ⨆ u : ℝ, G.law p {ω | 0 < frontierCount G.ends
    (Percolation.internalEdges G.ends {v | G.adjustedLayerIndex a R u x v < (n : ℤ)}) Set.univ ω x}

omit [Countable V] [Countable E] in
lemma supAdjustedFrontierProbability_le_one (a : V → ℝ) (R : ℝ) (p : unitInterval) (n : ℕ) :
    G.supAdjustedFrontierProbability a R p n ≤ 1 := by
  apply iSup_le
  intro x
  apply iSup_le
  intro u
  exact prob_le_one

theorem adjusted_frontier_probability_lower
    (a : V → ℝ) (R : ℝ) (p : unitInterval) (β A : ℝ) (hA : 0 < A)
    (hlower : ∀ n : ℕ, ENNReal.ofReal (Real.exp (-β*n)) ≤ G.supAdjustedUpLayerMoment a R p n)
    (hsecond : ∀ (n : ℕ) (x : V) (u : ℝ),
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | G.adjustedLayerIndex a R u x v ≤ (n : ℤ)})
        {v | G.adjustedLayerIndex a R u x v=(n : ℤ)} ω x)^2 ∂G.law p) ≤
          ENNReal.ofReal (A*Real.exp (-β*n))) (n : ℕ) (hn : 0 < n) :
    ENNReal.ofReal (Real.exp (-β*n)/A) ≤ G.supAdjustedFrontierProbability a R p n := by
  let P := G.supAdjustedFrontierProbability a R p n
  let t := Real.exp (-β*n)
  have ht : 0 < t := Real.exp_pos _
  have hP : P ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    (G.supAdjustedFrontierProbability_le_one a R p n)
  have hsq : (G.supAdjustedUpLayerMoment a R p n)^2 ≤ P*ENNReal.ofReal (A*t) := by
    apply ennreal_iSup_square_le
    intro x
    apply ennreal_iSup_square_le
    intro u
    let f := G.adjustedLayerIndex a R u x
    have hfx : f x < (n : ℤ) := by
      simp only [f,G.adjustedLayerIndex_self]
      exact_mod_cast hn
    have hprob := integer_upper_layer_hit_frontier_probability G.ends f (n : ℤ) x hfx p
    have hsup : G.law p {ω | 0 < frontierCount G.ends
        (Percolation.internalEdges G.ends {v | f v < (n : ℤ)}) Set.univ ω x} ≤ P :=
      le_iSup_of_le x (le_iSup_of_le u le_rfl)
    exact (restrictedLayerCount_moment_cauchy G.ends _ _ p x).trans
      (mul_le_mul' (hprob.trans hsup) (hsecond n x u))
  have hlo : (ENNReal.ofReal t)^2 ≤ P*ENNReal.ofReal (A*t) :=
    (pow_le_pow_left' (hlower n) 2).trans hsq
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top hP ENNReal.ofReal_ne_top) hlo
  rw [ENNReal.toReal_pow,ENNReal.toReal_mul,ENNReal.toReal_ofReal ht.le,
    ENNReal.toReal_ofReal (mul_nonneg hA.le ht.le)] at hreal
  have hc : t ≤ P.toReal*A := (mul_le_mul_iff_right₀ ht).mp (by nlinarith)
  apply ENNReal.ofReal_le_of_le_toReal
  exact (div_le_iff₀ hA).mpr (by nlinarith)

end CriticalPercolation.BondGraph

end

end OAI
