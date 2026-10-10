import OAI.NumberTheory.Ostmann.QuadraticCenter.MomentTransfer
import OAI.NumberTheory.Ostmann.QuadraticCenter.WalshTensor

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem real_character_moment_le_energy {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (R : Finset β) (χ : β → Finset ι → ℝ) (b : Finset ι → ℝ)
    {l : ℕ} (hl : 1 ≤ l) (Y E : ℝ) (hY : 0 ≤ Y)
    (hcor : ∀ f : Fin (2 * l) → Finset ι,
      |∑ m ∈ R, ∏ j, χ m (f j)| ≤
        Y * (if ∀ i, Even (∑ j, if i ∈ f j then 1 else 0) then 1 else 0) + E) :
    (∑ m ∈ R, (∑ s, b s * χ m s) ^ (2 * l)) ≤
      Y * (∑ s, ((((2 * l : ℕ) : ℝ) ^ 2) ^ s.card) * b s ^ 2) ^ l +
      E * (∑ s, |b s|) ^ (2 * l) := by
  have ht := real_moment_le_sign_moment_of_correlations R χ
    (fun s i => if i ∈ s then 1 else 0) b (2 * l) Y E hcor
  have hw := walsh_even_moment_le_weighted_energy (fun s => |b s|) hl
  simp only [sq_abs] at hw
  exact ht.trans (add_le_add (mul_le_mul_of_nonneg_left hw hY) le_rfl)

theorem complex_even_norm_le_parts (z : ℂ) (l : ℕ) :
    ‖z‖ ^ (2 * l) ≤
      (2 : ℝ) ^ (l - 1) * (z.re ^ (2 * l) + z.im ^ (2 * l)) := by
  rw [pow_mul, Complex.sq_norm, Complex.normSq_apply]
  have h := add_pow_le (sq_nonneg z.re) (sq_nonneg z.im) l
  simpa only [← pow_two, ← pow_mul] using h

end Ostmann.QuadraticCenter

end OAI
