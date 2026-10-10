import OAI.NumberTheory.JointDickman.Analysis.ShortMellinDyadicEnergy
import OAI.NumberTheory.JointDickman.Counting.ShortWindowEnergy

namespace OAI

/-! # Restoring integers excluded from the typical prime-factor set -/
namespace JointDickman
open Finset MeasureTheory PublishedInputs

noncomputable def restrictArithmetic (S : ℕ → Prop) [DecidablePred S]
    (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if S n then f n else 0, by simp⟩

theorem restrictArithmetic_norm_le (S : ℕ → Prop) [DecidablePred S]
    (f : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (n : ℕ) :
    ‖restrictArithmetic S f n‖ ≤ 1 := by
  change ‖if S n then f n else 0‖ ≤ 1
  split_ifs
  · exact hf n
  · norm_num

lemma complexShortAverage_sub (f g : ArithmeticFunction ℂ) (H x : ℝ) :
    complexShortAverage (f - g) H x = complexShortAverage f H x - complexShortAverage g H x := by
  change ((∑ n ∈ Ioc ⌊x⌋₊ ⌊x + H⌋₊, (f n - g n)) / (H : ℂ)) = _
  rw [sum_sub_distrib, sub_div]
  rfl

/-- Removing an arbitrary exceptional set costs its ordinary counting
density, uniformly in the short-window length. -/
theorem shortAverage_restrict_energy (S : ℕ → Prop) [DecidablePred S]
    (f : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    {X H : ℝ} (hX : 0 < X) (hH : 1 ≤ H) (hHX : H ≤ X) :
    (1 / X) * (∫ x in X..2 * X, ‖complexShortAverage f H x‖ ^ 2) ≤
      2 * ((1 / X) * (∫ x in X..2 * X, ‖complexShortAverage (restrictArithmetic S f) H x‖ ^ 2)) +
        4 * (((range (⌊3 * X⌋₊ + 1)).filter fun n => ¬S n).card : ℝ) / X := by
  let g := restrictArithmetic S f
  let E : ℕ → ℝ := fun n => if S n then 0 else 1
  have hE (n : ℕ) : ‖(f - g) n‖ ^ 2 ≤ E n := by
    change ‖f n - (if S n then f n else 0)‖ ^ 2 ≤ (if S n then 0 else 1)
    by_cases hn : S n
    · simp [hn]
    · have hh := pow_le_pow_left₀ (norm_nonneg (f n)) (hf n) 2
      simpa [hn] using hh
  have hbad := complexShortAverage_energy_le_prefix (f - g) E hE hH hX hHX
  have hcount : (∑ n ∈ range (⌊3 * X⌋₊ + 1), E n) =
      (((range (⌊3 * X⌋₊ + 1)).filter fun n => ¬S n).card : ℝ) := by
    rw [← sum_boole (fun n => ¬S n)]
    apply sum_congr rfl
    intro n _
    by_cases hn : S n <;> simp [E, hn]
  rw [hcount] at hbad
  have hpoint (x : ℝ) : ‖complexShortAverage f H x‖ ^ 2 ≤
      2 * ‖complexShortAverage g H x‖ ^ 2 + 2 * ‖complexShortAverage (f - g) H x‖ ^ 2 := by
    have hh := norm_add_le (complexShortAverage g H x) (complexShortAverage (f - g) H x)
    rw [complexShortAverage_sub, add_sub_cancel] at hh
    rw [complexShortAverage_sub]
    have h1 := norm_nonneg (complexShortAverage g H x)
    have h2 := norm_nonneg (complexShortAverage f H x - complexShortAverage g H x)
    have h3 := norm_nonneg (complexShortAverage f H x)
    nlinarith [sq_nonneg (‖complexShortAverage g H x‖ - ‖complexShortAverage f H x - complexShortAverage g H x‖)]
  have hH0 : 0 < H := by linarith
  have hi := intervalIntegral.integral_mono (by linarith : X ≤ 2 * X)
    (complexShortAverage_sq_integrable_any f hH0 X (2 * X))
    (((complexShortAverage_sq_integrable_any g hH0 X (2 * X)).const_mul 2).add
      ((complexShortAverage_sq_integrable_any (f - g) hH0 X (2 * X)).const_mul 2)) hpoint
  rw [intervalIntegral.integral_add
    ((complexShortAverage_sq_integrable_any g hH0 X (2 * X)).const_mul 2)
    ((complexShortAverage_sq_integrable_any (f - g) hH0 X (2 * X)).const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  have hs := mul_le_mul_of_nonneg_left hi (show 0 ≤ 1 / X by positivity)
  dsimp only [g] at hs hbad
  simp only [div_eq_mul_inv] at hs hbad ⊢
  nlinarith only [hs, hbad]

/-- This is the analytic transfer used after the multiscale estimate for the
literal typical coefficient. No multiplicativity is assumed of the cutoff. -/
theorem shortAverage_typical_dyadic_energy (η : ℝ) (hη : 0 < η) (hηhalf : η < 1/2)
    (m : ℕ) (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ℕ → Prop) [DecidablePred S]
      (f : ArithmeticFunction ℂ), (∀ n, ‖f n‖ ≤ 1) →
      ∀ X H : ℝ, 0 < X → 1 ≤ H → H ≤ X → ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      (∀ T : ℝ, 1 ≤ T →
        (∫ t in -T..T, ‖mellinPolynomial (Ioc ⌊X⌋₊ ⌊4 * X⌋₊)
          (restrictArithmetic S f) t‖ ^ 2) ≤ A + B * T) →
      (1 / X) * (∫ x in X..2 * X, ‖complexShortAverage f H x‖ ^ 2) ≤
        C * (A + B * X / H) +
          4 * (3 / (m : ℝ) + 11 / H + H / X + 1 / X + 16 * η) ^ 2 +
          4 * (((range (⌊3 * X⌋₊ + 1)).filter fun n => ¬S n).card : ℝ) / X := by
  obtain ⟨C, hC, hbound⟩ := shortAverage_dyadic_energy η hη hηhalf m hm
  refine ⟨2 * C, by positivity, ?_⟩
  intro S _ f hf X H hX hH hHX A B hA hB hspectral
  have hh := hbound (restrictArithmetic S f) (restrictArithmetic_norm_le S f hf)
    X H hX hH hHX A B hA hB hspectral
  have ht := shortAverage_restrict_energy S f hf hX hH hHX
  nlinarith

end JointDickman

end OAI
