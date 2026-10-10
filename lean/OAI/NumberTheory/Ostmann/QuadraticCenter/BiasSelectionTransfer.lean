import OAI.NumberTheory.Ostmann.QuadraticCenter.BiasSelectionWindows

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Ostmann.Characters Ostmann.Preliminaries Filter
open scoped BigOperators

instance primeUpToFactPrime {Q : ℕ} (p : PrimeUpTo Q) : Fact p.val.Prime :=
  ⟨primeUpTo_prime p⟩

lemma quadratic_support_complex_mean {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (t : ZMod p) :
    (∑ r ∈ S, quadraticCharacter p (r - t)) / (S.card : ℂ) =
      (quadraticResidueMean S t : ℂ) := by
  rw [← translatedMean_quadratic_eq_real]
  unfold translatedMean
  ring

theorem eventually_quadratic_window_errors (d : Decomposition) :
    ∀ᶠ X : ℕ in atTop, ∀ t : (p : PrimeUpTo (collisionScale 4 X)) → ZMod p.val,
      (∑ p : PrimeUpTo (collisionScale 4 X), (Real.log p.val / p.val) *
        (integerQuadraticMean (positiveIntegerWindow d.A X) p.val ((t p).val : ℤ) -
          quadraticResidueMean (d.residueSupport p.val) (t p)) ^ 2) ≤
        collisionConstant 4 * Real.log (Real.log (X : ℝ)) ∧
      (∑ p : PrimeUpTo (collisionScale 4 X), (Real.log p.val / p.val) *
        (integerQuadraticMean (negativeIntegerWindow d.B X) p.val ((t p).val : ℤ) -
          quadraticResidueMean (d.residueSupport p.val)ᶜ (t p)) ^ 2) ≤
        collisionConstant 4 * Real.log (Real.log (X : ℝ)) := by
  classical
  filter_upwards [eventually_upperWindow_A_test_stability d,
    eventually_upperWindow_neg_B_test_stability d] with X hA hD
  intro t
  let f : (p : PrimeUpTo (collisionScale 4 X)) → ZMod p.val → ℂ :=
    fun p r => quadraticCharacter p.val (r - t p)
  have hf : ∀ p, ∑ r, ‖f p r‖ ^ 2 ≤ p.val := fun p =>
    probability_test_norm_le_of_norm_le_one p.val (f p)
      (fun r => norm_quadraticCharacter_le_one (r - t p))
  have ha := hA f hf
  have hd := hD f hf
  dsimp only [f] at ha hd
  constructor
  · simpa only [positive_window_complex_mean, quadratic_support_complex_mean,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs] using ha
  · simpa only [negative_window_complex_mean, quadratic_support_complex_mean,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hd

lemma oriented_empirical_pair {δ σ s t a b : ℝ} {ε : ℤ}
    (hδ : 0 < δ) (hlo : 1 / 3 ≤ σ) (hhi : σ ≤ 2 / 3)
    (hrel : σ * s + (1 - σ) * t = 0)
    (hε : ε = 1 ∨ ε = -1) (hbias : δ ≤ (ε : ℝ) * s)
    (ha : |a - s| ≤ δ / 8) (hb : |b - t| ≤ δ / 8) :
    δ / 4 ≤ (ε : ℝ) * a ∧ (ε : ℝ) * b ≤ -δ / 4 := by
  have heabs : |(ε : ℝ)| = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hrel' : σ * ((ε : ℝ) * s) + (1 - σ) * ((ε : ℝ) * t) = 0 := by
    calc
      _ = (ε : ℝ) * (σ * s + (1 - σ) * t) := by ring
      _ = 0 := by rw [hrel, mul_zero]
  have hσ0 : 0 ≤ σ := by linarith
  have hσ1 : 0 < 1 - σ := by linarith
  have hprod := mul_nonneg (sub_nonneg.mpr hlo) hδ.le
  have hprod2 := mul_le_mul_of_nonneg_left hbias hσ0
  have hv : (ε : ℝ) * t ≤ -δ / 2 := by
    apply (mul_le_mul_iff_right₀ hσ1).mp
    nlinarith only [hrel', hprod, hprod2]
  have ha' : |(ε : ℝ) * (a - s)| ≤ δ / 8 := by
    rwa [abs_mul, heabs, one_mul]
  have hb' : |(ε : ℝ) * (b - t)| ≤ δ / 8 := by
    rwa [abs_mul, heabs, one_mul]
  have hla := (abs_le.mp ha').1
  have hub := (abs_le.mp hb').2
  constructor <;> nlinarith

end Ostmann.QuadraticCenter

end

end OAI
