import OAI.Probability.InvariantIsing.Gaussian.GaussianGramLowerBound
import OAI.Probability.InvariantIsing.Gaussian.GaussianGramNormBound

namespace OAI

/-! Deterministic transport of the two singular-value edge errors to Gram spectral excess. -/
noncomputable section
open scoped Topology
namespace InvariantIsing

lemma gaussianGram_singular_bounds {n m : ℕ}
    (z : EuclideanSpace ℝ (Fin (n+1) × Fin m)) (i : Fin (n+1)) :
    (gaussianPatternSingularMin (gaussianPatternTranspose (n+1) m z)/Real.sqrt (n+1))^2 ≤
      gaussianPatternEigenvalues z i ∧
    gaussianPatternEigenvalues z i ≤ (gaussianPatternSingularMax z/Real.sqrt (n+1))^2 := by
  have hs : (Real.sqrt (n+1))^2 = (n+1 : ℝ) := Real.sq_sqrt (by positivity)
  constructor
  · simpa only [div_pow,hs,Nat.cast_succ,Nat.cast_add,Nat.cast_one] using
      gaussianPatternEigenvalues_lower_singular (Nat.succ_pos n) z i
  · have h := (le_abs_self (gaussianPatternEigenvalues z i)).trans
      (gaussianPatternEigenvalues_abs_le (Nat.succ_pos n) z i)
    simpa only [div_pow,hs,Nat.cast_succ,Nat.cast_add,Nat.cast_one] using h

lemma squared_lower_edge_bound (L b : ℝ) (hL : 0 ≤ L) (hb : 0 ≤ b) :
    L^2-2*L*max (L-b) 0 ≤ b^2 := by
  by_cases h : L ≤ b
  · rw [max_eq_right (sub_nonpos.mpr h)]
    nlinarith
  · rw [max_eq_left (by linarith : 0 ≤ L-b)]
    nlinarith [sq_nonneg (L-b)]

lemma gaussianGram_spectralExcess_bound {n m : ℕ}
    (z : EuclideanSpace ℝ (Fin (n+1) × Fin m)) (L U : ℝ) (hL : 0 ≤ L) (hU : 0 ≤ U) :
    spectralExcess (gaussianPatternEigenvalues z) (L^2) (U^2) ≤
      (U+max (gaussianPatternSingularMax z/Real.sqrt (n+1)-U) 0)^2-U^2 +
        2*L*max (L-gaussianPatternSingularMin (gaussianPatternTranspose (n+1) m z)/Real.sqrt (n+1)) 0 := by
  let a := gaussianPatternSingularMax z/Real.sqrt (n+1)
  let b := gaussianPatternSingularMin (gaussianPatternTranspose (n+1) m z)/Real.sqrt (n+1)
  let du := max (a-U) 0
  let dl := max (L-b) 0
  have ha : 0 ≤ a := div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hb : 0 ≤ b := div_nonneg (gaussianPatternSingularMin_nonneg (Nat.succ_pos n) _)
    (Real.sqrt_nonneg _)
  have hdu : 0 ≤ du := le_max_right _ _
  have hdl : 0 ≤ dl := le_max_right _ _
  have hu : 0 ≤ (U+du)^2-U^2 := by nlinarith
  have hl : 0 ≤ 2*L*dl := by positivity
  apply spectralExcess_le _ _ _ _ (add_nonneg hu hl)
  intro i
  have hbounds := gaussianGram_singular_bounds z i
  change b^2 ≤ gaussianPatternEigenvalues z i ∧ gaussianPatternEigenvalues z i ≤ a^2 at hbounds
  have hblo := squared_lower_edge_bound L b hL hb
  have hau : a ≤ U+du := by dsimp only [du]; linarith [le_max_left (a-U) 0]
  constructor
  · change L^2-2*L*dl ≤ b^2 at hblo
    linarith [hbounds.1]
  · nlinarith [hbounds.2]

end InvariantIsing

end

end OAI
