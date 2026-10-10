import OAI.NumberTheory.Ostmann.Arithmetic.MovingSeparatedAverageNorm
import OAI.NumberTheory.Ostmann.Arithmetic.HarmonicPairIntegral

namespace OAI

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem continuous_pageGiantWeight (P : PublishedProgressionInput) (Q q a : ℕ) :
    Continuous (pageGiantWeight P Q q a) := by
  unfold pageGiantWeight pageMultiplier
  fun_prop

theorem continuous_correctedPrimePairAverage (P : PublishedProgressionInput) (Q q : ℕ)
    [NeZero q] (c : ℕ → ℕ → ℂ) :
    Continuous (Function.uncurry (correctedPrimePairAverage P Q q c)) := by
  unfold correctedPrimePairAverage Function.uncurry
  apply continuous_const.mul
  apply continuous_finsetSum
  intro z _
  exact ((continuous_const.mul ((continuous_pageGiantWeight P Q q _).comp continuous_fst)).mul
    ((continuous_pageGiantWeight P Q q _).comp continuous_snd))

theorem correctedPrimePairAverage_norm_le (P : PublishedProgressionInput) (Q q : ℕ)
    [NeZero q] (c : ℕ → ℕ → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hc : ∀ a : (ZMod q)ˣ, ∀ b : (ZMod q)ˣ,
      ‖c (a : ZMod q).val (b : ZMod q).val‖ ≤ A)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ‖correctedPrimePairAverage P Q q c x y‖ ≤ 4 * A := by
  have hcard : (Fintype.card ((ZMod q)ˣ × (ZMod q)ˣ) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hpoint (z : (ZMod q)ˣ × (ZMod q)ˣ) :
      ‖c (z.1 : ZMod q).val (z.2 : ZMod q).val *
        pageGiantWeight P Q q (z.1 : ZMod q).val x *
        pageGiantWeight P Q q (z.2 : ZMod q).val y‖ ≤ 4 * A := by
    simp only [norm_mul]
    calc
      _ ≤ A * 2 * 2 :=
        mul_le_mul (mul_le_mul (hc z.1 z.2) (pageGiantWeight_norm_le_two P Q q _ x hx)
          (norm_nonneg _) hA) (pageGiantWeight_norm_le_two P Q q _ y hy)
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  unfold correctedPrimePairAverage
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card ((ZMod q)ˣ × (ZMod q)ˣ) : ℝ)⁻¹ * ∑ _z : (ZMod q)ˣ × (ZMod q)ˣ, 4 * A :=
      mul_le_mul_of_nonneg_left
        ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun z _ => hpoint z))) (by positivity)
    _ = 4 * A := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

/-- The finite external average may have a different CRT modulus for every
assignment. Its pointwise arithmetic bound passes through both giant cells. -/
theorem prime_pair_haar_sum_norm {A : Type*} [Fintype A]
    (P : PublishedProgressionInput) (Q : ℕ) (q : A → ℕ) [∀ a, NeZero (q a)]
    (c : A → ℕ → ℕ → ℂ) (H : A → ℝ → ℝ → ℂ)
    (hH : ∀ a, Measurable (Function.uncurry (H a)))
    (K B : A → ℝ) (hK : ∀ a, 0 ≤ K a) (hB : ∀ a, 0 ≤ B a)
    (hbound : ∀ a x y, ‖H a x y‖ ≤ K a)
    (hc : ∀ a, ∀ z : (ZMod (q a))ˣ, ∀ w : (ZMod (q a))ˣ,
      ‖c a (z : ZMod (q a)).val (w : ZMod (q a)).val‖ ≤ B a)
    (u v r s C : ℝ) (hu : 1 ≤ u) (hr : 1 ≤ r)
    (huv : u ≤ v) (hrs : r ≤ s) (hv : v ≤ u + 1) (hs : s ≤ r + 1)
    (hC : 0 ≤ C) (w : A → ℂ)
    (hmean : ∀ x ∈ Set.Ioc u v, ∀ y ∈ Set.Ioc r s,
      ‖∑ a, w a * (H a x y * correctedPrimePairAverage P Q (q a) (c a) x y)‖ ≤ C) :
    ‖∑ a, w a * ∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
      H a x y * correctedPrimePairAverage P Q (q a) (c a) x y / ((x : ℂ) * (y : ℂ))‖ ≤
      C / (u * r) := by
  apply finite_harmonic_pair_sum_norm u v r s C hu hr huv hrs hv hs hC w
    (fun a x y => H a x y * correctedPrimePairAverage P Q (q a) (c a) x y)
    (fun a => (hH a).mul (continuous_correctedPrimePairAverage P Q (q a) (c a)).measurable)
    (fun a => K a * (4 * B a)) (fun a => mul_nonneg (hK a) (mul_nonneg (by norm_num) (hB a))) _ hmean
  intro a x hx y hy
  rw [norm_mul]
  exact mul_le_mul (hbound a x y)
    (correctedPrimePairAverage_norm_le P Q (q a) (c a) (B a) (hB a) (hc a) x y
      (by linarith [hx.1]) (by linarith [hy.1])) (norm_nonneg _) (hK a)

end Ostmann

end OAI
