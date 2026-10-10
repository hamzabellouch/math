import OAI.Geometry.HeilbronnTriangle.ProportionalPairs

namespace OAI


noncomputable section

namespace Problem355.UniformLiftPairs

open Finset ProportionalPairs

def collisionFraction (U V : Finset NatColumn) : ℝ := by
  classical
  exact (((U ×ˢ V).filter fun p => project p.1 = project p.2).card : ℝ) /
    ((U.card : ℝ) * (V.card : ℝ))

theorem averaged_collision_fraction_le
    {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hmass : ∑ ω, w ω = 1)
    (N Q L : ℕ) (hQ : 0 < Q) (hL : 0 < L) (hN : N = Q * L)
    (U V : Ω → Finset NatColumn)
    (hU : ∀ ω, U ω ⊆ columnBox N) (hV : ∀ ω, V ω ⊆ columnBox N)
    (hUc : ∀ ω, (U ω).card = L ^ 3) (hVc : ∀ ω, (V ω).card = L ^ 3) :
    (∑ ω, w ω * collisionFraction (U ω) (V ω)) ≤
      8 * (Q : ℝ) ^ 6 / (N : ℝ) ^ 3 := by
  classical
  calc
    (∑ ω, w ω * collisionFraction (U ω) (V ω)) ≤
        ∑ ω, w ω * (8 * (Q : ℝ) ^ 6 / (N : ℝ) ^ 3) := by
      apply Finset.sum_le_sum
      intro ω hω
      apply mul_le_mul_of_nonneg_left _ (hw ω)
      exact uniform_collision_fraction_le N Q L hQ hL hN
        (U ω) (V ω) (hU ω) (hV ω) (hUc ω) (hVc ω)
    _ = 8 * (Q : ℝ) ^ 6 / (N : ℝ) ^ 3 := by
      rw [← Finset.sum_mul, hmass, one_mul]

theorem weighted_collision_bound
    {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (w : Ω → ℝ) (p : Ω → Ξ → ℝ) (event : Ω → Ξ → Prop)
    [DecidableRel event] (B : ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hmass : ∑ ω, w ω = 1)
    (hconditional : ∀ ω, (∑ x, if event ω x then p ω x else 0) ≤ B) :
    (∑ ω, ∑ x, if event ω x then w ω * p ω x else 0) ≤ B := by
  calc
    (∑ ω, ∑ x, if event ω x then w ω * p ω x else 0) =
        ∑ ω, w ω * (∑ x, if event ω x then p ω x else 0) := by
      apply Finset.sum_congr rfl
      intro ω hω
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      split_ifs <;> simp
    _ ≤ ∑ ω, w ω * B := by
      exact Finset.sum_le_sum fun ω _ =>
        mul_le_mul_of_nonneg_left (hconditional ω) (hw ω)
    _ = B := by rw [← Finset.sum_mul, hmass, one_mul]

end Problem355.UniformLiftPairs

end

end OAI
