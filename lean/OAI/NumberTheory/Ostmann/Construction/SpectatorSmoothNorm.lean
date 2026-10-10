import OAI.NumberTheory.Ostmann.Construction.SpectatorProductNorm

namespace OAI

/-! # Integrating the smooth amplitude together with all spectator diagrams -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def smoothSpectatorAverage {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (n : ℕ)
    (g : ∀ i, ZMod (p i) → ℂ) (d e : ∀ i, SpectatorDiagram (p i) n)
    (Ξ : (∀ i, TreeLeafTuple (ZMod (p i))ˣ n) → ℂ) : ℝ :=
  (Fintype.card (∀ i, TreeLeafTuple (ZMod (p i))ˣ n) : ℝ)⁻¹ *
    ∑ x : ∀ i, TreeLeafTuple (ZMod (p i))ˣ n,
      ‖Ξ x * ∏ i, ((d i).value (g i) (x i) * star ((e i).value (g i) (x i)))‖

theorem smoothSpectatorAverage_nonneg {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (n : ℕ)
    (g : ∀ i, ZMod (p i) → ℂ) (d e : ∀ i, SpectatorDiagram (p i) n)
    (Ξ : (∀ i, TreeLeafTuple (ZMod (p i))ˣ n) → ℂ) :
    0 ≤ smoothSpectatorAverage p n g d e Ξ :=
  mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun _ _ => norm_nonneg _)

theorem smoothSpectatorAverage_le {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (n : ℕ)
    (hp : ∀ i, 3 ≤ p i) (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (henergy : ∀ i, (∑ x : ZMod (p i), ‖g i x‖ ^ 2) ≤ (p i : ℝ))
    (d e : ∀ i, SpectatorDiagram (p i) n)
    (Ξ : (∀ i, TreeLeafTuple (ZMod (p i))ˣ n) → ℂ)
    (E : ℝ) (hE : 0 ≤ E) (hΞ : ∀ x, ‖Ξ x‖ ≤ E) :
    smoothSpectatorAverage p n g d e Ξ ≤ E * (3 : ℝ) ^ (2 ^ n * Fintype.card I) := by
  unfold smoothSpectatorAverage
  calc
    _ ≤ (Fintype.card (∀ i, TreeLeafTuple (ZMod (p i))ˣ n) : ℝ)⁻¹ *
        ∑ x : ∀ i, TreeLeafTuple (ZMod (p i))ˣ n,
          E * ∏ i, ‖(d i).value (g i) (x i) * star ((e i).value (g i) (x i))‖ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      apply Finset.sum_le_sum
      intro x _
      rw [norm_mul, norm_prod]
      exact mul_le_mul_of_nonneg_right (hΞ x) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = E * ((Fintype.card (∀ i, TreeLeafTuple (ZMod (p i))ˣ n) : ℝ)⁻¹ *
        ∑ x : ∀ i, TreeLeafTuple (ZMod (p i))ˣ n,
          ∏ i, ‖(d i).value (g i) (x i) * star ((e i).value (g i) (x i))‖) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (spectator_product_absolute_le p n hp g hg henergy d e) hE

end Ostmann

end OAI
