import OAI.NumberTheory.TwoPoint.Circuits.CircuitDepthSwitching
import OAI.NumberTheory.TwoPoint.Circuits.CircuitRestrictionDecay

namespace OAI

/-! Quantitative Fourier concentration obtained from the proved switching
estimate. All parameters remain explicit for the fixed-depth application. -/

namespace TwoPointCorrelations

open scoped Classical

theorem fourier_tail_le_small_tree_failure {n : ℕ} (f : BooleanCube n → Bool)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (r D : ℕ)
    (hr : 2 * (r : ℝ) ≤ p * (D + 1)) (hD : 8 ≤ p * (D + 1)) :
    cubeAverage (fun x => ((if f x then (1 : ℝ) else 0) -
      walshTruncation (fun y => if f y then 1 else 0) D x) ^ 2) ≤
      2 * (restrictionLaw n p hp hp1).probability
        (fun ρ => ¬ HasSmallDecisionTree (fun x => f (ρ.apply x)) r) := by
  have hf (x) : (if f x then (1 : ℝ) else 0) = 0 ∨
      (if f x then (1 : ℝ) else 0) = 1 := by cases f x <;> simp
  apply (fourier_tail_le_degree_failure _ hf p hp hp1 r D hr hD).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [FiniteLaw.probability, restrictionLaw_average]
  apply FiniteLaw.average_mono
  intro mask
  apply cubeAverage_mono
  intro y
  by_cases h : HasSmallDecisionTree
      (fun x => f ((partialAssignmentOfMask mask y).apply x)) r
  · obtain ⟨T, hT, he⟩ := h
    have hd : WalshDegreeLE
        (fun x => if f (restrictCube (sampledCoordinates mask) y x) then (1 : ℝ) else 0) r := by
      have hi : (fun x => if f (restrictCube (sampledCoordinates mask) y x)
          then (1 : ℝ) else 0) = T.indicator := by
        funext x
        simp only [BooleanDecisionTree.indicator, he, partialAssignmentOfMask_apply]
      rw [hi]
      exact T.indicator_degree.mono hT
    simp only [hd, ite_true]
    split_ifs <;> norm_num
  · simp only [h, not_false_eq_true, ite_true]
    split_ifs <;> norm_num

theorem AC0Circuit.fourier_tail_switching {n : ℕ} (c : AC0Circuit n)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p < 1) (r : ℕ) (hr : 1 ≤ r)
    (hq : ((3 * (2 * r + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p)) ≤ 1 / 2)
    (d D : ℕ) (hc : c.depth ≤ d)
    (hDr : 2 * (r : ℝ) ≤ p ^ d * (D + 1)) (hD : 8 ≤ p ^ d * (D + 1)) :
    cubeAverage (fun x => (c.indicator x - walshTruncation c.indicator D x) ^ 2) ≤
      4 * (c.size : ℝ) *
        (((3 * (2 * r + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p))) ^ (r + 1) := by
  have hf := fourier_tail_le_small_tree_failure c.eval (p ^ d) (pow_nonneg hp _)
    (pow_le_one₀ hp hp1.le) r D hDr hD
  apply hf.trans
  have hh := c.restriction_shallow p hp hp1 r hr hq d hc
  have hmul := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 2 by norm_num)
  convert hmul using 1
  ring

end TwoPointCorrelations

end OAI
