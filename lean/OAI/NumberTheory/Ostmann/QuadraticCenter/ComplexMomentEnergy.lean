import OAI.NumberTheory.Ostmann.QuadraticCenter.MomentEnergy

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem real_character_moment_le_energy_of_coeff_bound
    {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (R : Finset β) (χ : β → Finset ι → ℝ) (b B : Finset ι → ℝ)
    {l : ℕ} (hl : 1 ≤ l) (Y E : ℝ) (hY : 0 ≤ Y) (hE : 0 ≤ E)
    (hB : ∀ s, |b s| ≤ B s)
    (hcor : ∀ f : Fin (2 * l) → Finset ι,
      |∑ m ∈ R, ∏ j, χ m (f j)| ≤
        Y * (if ∀ i, Even (∑ j, if i ∈ f j then 1 else 0) then 1 else 0) + E) :
    (∑ m ∈ R, (∑ s, b s * χ m s) ^ (2 * l)) ≤
      Y * (∑ s, ((((2 * l : ℕ) : ℝ) ^ 2) ^ s.card) * B s ^ 2) ^ l +
      E * (∑ s, B s) ^ (2 * l) := by
  have ht := real_character_moment_le_energy R χ b hl Y E hY hcor
  apply ht.trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ hY
    apply pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => by positivity))
    apply Finset.sum_le_sum
    intro s hs
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [sq_abs] using
      pow_le_pow_left₀ (abs_nonneg (b s)) (hB s) 2
  · apply mul_le_mul_of_nonneg_left _ hE
    apply pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    exact Finset.sum_le_sum (fun s _ => hB s)

theorem complex_character_moment_le_energy
    {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (R : Finset β) (χ : β → Finset ι → ℝ) (b : Finset ι → ℂ)
    {l : ℕ} (hl : 1 ≤ l) (Y E : ℝ) (hY : 0 ≤ Y) (hE : 0 ≤ E)
    (hcor : ∀ f : Fin (2 * l) → Finset ι,
      |∑ m ∈ R, ∏ j, χ m (f j)| ≤
        Y * (if ∀ i, Even (∑ j, if i ∈ f j then 1 else 0) then 1 else 0) + E) :
    (∑ m ∈ R, ‖∑ s, b s * (χ m s : ℂ)‖ ^ (2 * l)) ≤
      (2 : ℝ) ^ l *
        (Y * (∑ s, ((((2 * l : ℕ) : ℝ) ^ 2) ^ s.card) * ‖b s‖ ^ 2) ^ l +
          E * (∑ s, ‖b s‖) ^ (2 * l)) := by
  have hr := real_character_moment_le_energy_of_coeff_bound R χ
    (fun s => (b s).re) (fun s => ‖b s‖) hl Y E hY hE
    (fun s => Complex.abs_re_le_norm (b s)) hcor
  have hi := real_character_moment_le_energy_of_coeff_bound R χ
    (fun s => (b s).im) (fun s => ‖b s‖) hl Y E hY hE
    (fun s => Complex.abs_im_le_norm (b s)) hcor
  have hp : (∑ m ∈ R, ‖∑ s, b s * (χ m s : ℂ)‖ ^ (2 * l)) ≤
      (2 : ℝ) ^ (l - 1) *
        ((∑ m ∈ R, (∑ s, (b s).re * χ m s) ^ (2 * l)) +
          (∑ m ∈ R, (∑ s, (b s).im * χ m s) ^ (2 * l))) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro m hm
    simpa only [Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, zero_add,
      ← mul_add] using complex_even_norm_le_parts (∑ s, b s * (χ m s : ℂ)) l
  have htwo : (2 : ℝ) ^ l = (2 : ℝ) ^ (l - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel hl]
  rw [htwo]
  nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (l - 1))
    (add_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hi))]

end Ostmann.QuadraticCenter

end OAI
