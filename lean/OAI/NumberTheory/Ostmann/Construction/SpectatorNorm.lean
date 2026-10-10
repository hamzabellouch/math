import Mathlib.Algebra.Order.BigOperators.Group.Finset
import OAI.NumberTheory.Ostmann.Tree.RationalTreeLeaves

namespace OAI

/-! # Absolute spectator correlations for the norm comparison -/

namespace Ostmann

open scoped BigOperators

/-- The same second-moment bound on both factors controls their absolute
correlation. This form avoids introducing a square-root loss. -/
theorem uniform_absolute_pair_le {A : Type*} [Fintype A] [Nonempty A]
    (F G : A → ℂ) (B : ℝ)
    (hF : (∑ x, ‖F x‖ ^ 2) / (Fintype.card A : ℝ) ≤ B)
    (hG : (∑ x, ‖G x‖ ^ 2) / (Fintype.card A : ℝ) ≤ B) :
    (∑ x, ‖F x * star (G x)‖) / (Fintype.card A : ℝ) ≤ B := by
  have hpoint (x : A) : 2 * ‖F x * star (G x)‖ ≤ ‖F x‖ ^ 2 + ‖G x‖ ^ 2 := by
    rw [norm_mul, norm_star]
    nlinarith [sq_nonneg (‖F x‖ - ‖G x‖)]
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset A)) => hpoint x)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have hc : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hc).mpr
  have hF' := (div_le_iff₀ hc).mp hF
  have hG' := (div_le_iff₀ hc).mp hG
  linarith

theorem rationalTree_absolute_pair_le {p : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (D₁ D₂ : (ZMod p)ˣ) {n : ℕ} {C₁ C₂ : (ZMod p)ˣ}
    (T₁ : RationalTreeData (ZMod p)ˣ n C₁)
    (T₂ : RationalTreeData (ZMod p)ˣ n C₂)
    (XL₁ XR₁ XL₂ XR₂ : (ZMod p)ˣ) (c₁ c₂ : TreeLeafTuple Bool n) :
    (∑ x : TreeLeafTuple (ZMod p)ˣ n,
      ‖rationalTreeAmplitude g D₁ T₁ XL₁ XR₁ c₁ x *
        star (rationalTreeAmplitude g D₂ T₂ XL₂ XR₂ c₂ x)‖) /
      (Fintype.card (TreeLeafTuple (ZMod p)ˣ n) : ℝ) ≤ (3 : ℝ) ^ (2 ^ n) := by
  have : Nonempty (TreeLeafTuple (ZMod p)ˣ n) := Fintype.card_pos_iff.mp (by
    rw [card_treeLeafTuple]
    exact pow_pos Fintype.card_pos _)
  exact uniform_absolute_pair_le _ _ _
    (rationalTreeAmplitude_l2_bound hp g hg henergy D₁ T₁ XL₁ XR₁ c₁)
    (rationalTreeAmplitude_l2_bound hp g hg henergy D₂ T₂ XL₂ XR₂ c₂)

end Ostmann

end OAI
