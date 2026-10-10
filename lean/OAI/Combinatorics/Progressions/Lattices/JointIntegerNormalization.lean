import OAI.Combinatorics.Progressions.Sampling.JointGridAccuracy

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem jointIntegerImageMass_total {D : Type*} [Fintype D] [DecidableEq D]
    {X J : D → Type*} [∀ d, Fintype (X d)] [∀ d, Fintype (J d)] [∀ d, DecidableEq (J d)]
    (p : ∀ d, FiniteProbabilityWeights (X d)) (Y : ∀ d, X d → J d → ℤ)
    (H : D → ℝ) (K : D → ℕ) [∀ d, NeZero (K d)] (hH : ∀ d, 0 ≤ H d)
    (center : ∀ d, J d → ℤ)
    (hY : ∀ d x, (p d).weight x ≠ 0 → ∀ j, |(Y d x j : ℝ) - center d j| ≤ H d * K d) :
    (∑ r : ∀ d, J d → ZMod ((2 * commonSupportRadius H + 1) * K d),
      finiteImageMass (FiniteProbabilityWeights.pi p) (fun x d => Y d (x d))
        (fun d => centeredGridRepresentative (commonSupportRadius H) (K d) (center d) (r d))) = 1 := by
  have hK (d) : 0 < K d := Nat.pos_of_ne_zero (NeZero.ne (K d))
  let scale := ∏ d, (K d : ℝ) ^ Fintype.card (J d)
  have hp : 0 < scale := Finset.prod_pos (fun d _ => pow_pos (by exact_mod_cast hK d) _)
  have he : scale * (∑ r : ∀ d, J d → ZMod ((2 * commonSupportRadius H + 1) * K d),
      finiteImageMass (FiniteProbabilityWeights.pi p) (fun x d => Y d (x d))
        (fun d => centeredGridRepresentative (commonSupportRadius H) (K d) (center d) (r d))) = scale := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ r : ∀ d, J d → ZMod ((2 * commonSupportRadius H + 1) * K d), ∏ d,
          integerGridDensity (p d) (Y d) (K d) ((2 * commonSupportRadius H + 1) * K d)
            (centeredGridRepresentative (commonSupportRadius H) (K d) (center d) (r d)) := by
        apply Finset.sum_congr rfl
        intro r _
        exact jointImageMass_at_representatives p Y H K hK hH center hY r
      _ = scale := jointGridDensity_total p Y _ K center
  exact (mul_left_cancel₀ hp.ne' (he.trans (mul_one scale).symm))

theorem commonTorusFactor_uniform {D : Type*} [Fintype D] (H : D → ℝ)
    {C : ℝ} (hH : ∀ d, 0 ≤ H d) (hC : ∀ d, H d ≤ C) :
    ((2 * commonSupportRadius H + 1 : ℕ) : ℝ) ≤ 2 * Fintype.card D * C + 3 := by
  have h := commonSupportRadius_uniform H hH hC
  push_cast
  linarith

end Erdos3

end

end OAI
