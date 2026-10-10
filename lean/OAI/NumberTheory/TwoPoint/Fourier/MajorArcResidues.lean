import OAI.NumberTheory.TwoPoint.Fourier.MajorArcCharacters
import OAI.NumberTheory.TwoPoint.Bounds.ResidueExpansion
import OAI.NumberTheory.TwoPoint.Bounds.DilatedWindows

namespace OAI

/-! Gcd reduction of a typical-set progression, including nonunit classes.
The removed gcd avoids the prime bands, so the typical mask is unchanged.
The resulting windows are literal character twists at the divided scale. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical ComplexConjugate

lemma major_arc_typical_dilation {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ)
    (hF : ∀ a b, 0 < a → 0 < b → F (a * b) = F a * F b)
    {d : ℕ} (hd : 0 < d) (havoid : mrtPrimeAvoids (J.biUnion P) d)
    {q : ℕ} (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : 0 < n) :
    mrtTypicalCoefficient J P F n * dilate d (naturalCharacter χ) n =
      F d * dilationSequence d (mrtTypicalCoefficient J P (twistByCharacter F χ)) n := by
  by_cases hdn : d ∣ n
  · have hm : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd
    have he : n = d * (n / d) := (Nat.mul_div_cancel' hdn).symm
    have ht := mrtTypical_mul_of_avoids J P hP havoid (n / d)
    simp only [dilate, dilationSequence, ite_eq_left hdn, naturalCharacter]
    unfold mrtTypicalCoefficient twistByCharacter
    rw [he] at ⊢
    rw [Nat.mul_div_cancel_left _ hd, ht, hF d (n / d) hd hm]
    split_ifs <;> simp [mul_assoc]
  · simp [dilate, dilationSequence, hdn]

/-- The original residue `b` is unrestricted; the reduced character modulus
is `q / gcd b q`, and this also covers reduced modulus one. -/
lemma major_arc_typical_residue_identity {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ)
    (hF : ∀ a b, 0 < a → 0 < b → F (a * b) = F a * F b)
    (q b : ℕ) (hq : 0 < q)
    (havoid : mrtPrimeAvoids (J.biUnion P) (b.gcd q))
    {n : ℕ} (hn : 0 < n) :
    (if n % q = b % q then mrtTypicalCoefficient J P F n else 0) =
      F (b.gcd q) * ((q / b.gcd q).totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ (q / b.gcd q),
          conj (naturalCharacter χ (b / b.gcd q)) *
            dilationSequence (b.gcd q)
              (mrtTypicalCoefficient J P (twistByCharacter F χ)) n := by
  have h := congrArg (fun z : ℂ => mrtTypicalCoefficient J P F n * z)
    (residue_indicator_eq_character_dilations q b n hq)
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [h, ← mul_assoc]
  simp only [mul_sum]
  apply sum_congr rfl
  intro χ _
  have hd := Nat.gcd_pos_of_pos_right b hq
  have hh := major_arc_typical_dilation J P hP F hF hd havoid χ hn
  calc
    _ = ((q / b.gcd q).totient : ℂ)⁻¹ *
        conj (naturalCharacter χ (b / b.gcd q)) *
        (mrtTypicalCoefficient J P F n * dilate (b.gcd q) (naturalCharacter χ) n) := by ring
    _ = _ := by rw [hh]; ring

lemma major_arc_typical_residue_window {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ)
    (hF : ∀ a b, 0 < a → 0 < b → F (a * b) = F a * F b)
    (q b v H : ℕ) (hq : 0 < q)
    (havoid : mrtPrimeAvoids (J.biUnion P) (b.gcd q)) :
    (∑ n ∈ Icc (v + 1) (v + H),
      if n % q = b % q then mrtTypicalCoefficient J P F n else 0) =
      F (b.gcd q) * ((q / b.gcd q).totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ (q / b.gcd q),
          conj (naturalCharacter χ (b / b.gcd q)) *
            shortExponentialSum
              (dilationSequence (b.gcd q)
                (mrtTypicalCoefficient J P (twistByCharacter F χ))) H 0 v := by
  have he0 (n : ℕ) : additiveCharacter 0 n = 1 := by simp [additiveCharacter]
  simp_rw [shortExponentialSum_at_nat, he0, mul_one]
  have hi (n : ℕ) (hn : n ∈ Icc (v + 1) (v + H)) :=
    major_arc_typical_residue_identity J P hP F hF q b hq havoid
      (show 0 < n by have := (mem_Icc.mp hn).1; omega)
  rw [sum_congr rfl hi, ← mul_sum, sum_comm]
  congr 1
  apply sum_congr rfl
  intro χ _
  rw [mul_sum]

lemma major_arc_typical_residue_window_norm {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ)
    (hF : ∀ a b, 0 < a → 0 < b → F (a * b) = F a * F b)
    (hFb : OneBounded F) (q b v H : ℕ) (hq : 0 < q)
    (havoid : mrtPrimeAvoids (J.biUnion P) (b.gcd q)) :
    ‖∑ n ∈ Icc (v + 1) (v + H),
      if n % q = b % q then mrtTypicalCoefficient J P F n else 0‖ ≤
      ((q / b.gcd q).totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ (q / b.gcd q),
          ‖shortExponentialSum
            (dilationSequence (b.gcd q)
              (mrtTypicalCoefficient J P (twistByCharacter F χ))) H 0 v‖ := by
  rw [major_arc_typical_residue_window J P hP F hF q b v H hq havoid,
    mul_assoc, norm_mul, norm_mul, norm_inv, Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_right
    (hFb _ (Nat.gcd_pos_of_pos_right b hq)) (by positivity)).trans
  rw [one_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro χ _
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

lemma major_arc_dilation_average (F : ℕ → ℂ) (hF : OneBounded F)
    (d X H : ℕ) (hd : 0 < d) :
    (∑ v ∈ range X, ‖shortExponentialSum (dilationSequence d F) H 0 v‖) ≤
      (d : ℝ) * shortExponentialIntegral F (X / d + 1) (H / d + 1) 0 + X := by
  calc
    _ ≤ ∑ v ∈ range X, (‖shortWindowSum F (H / d + 1) 0 (v / d)‖ + 1) := by
      apply sum_le_sum
      intro v _
      simpa using norm_shortExponentialSum_dilation_le F hF d H v hd 0
    _ = (∑ v ∈ range X, ‖shortWindowSum F (H / d + 1) 0 (v / d)‖) + X := by
      rw [sum_add_distrib]
      simp
    _ ≤ (d : ℝ) * (∑ m ∈ range (X / d + 1),
        ‖shortWindowSum F (H / d + 1) 0 m‖) + X :=
      add_le_add (quotient_sample_sum_le _ (fun _ => norm_nonneg _) d X hd) le_rfl
    _ = _ := by
      rw [shortExponentialIntegral_eq_sum]
      simp_rw [norm_shortExponentialSum_eq_window]

/-- Averaging all original origins costs the gcd exactly once. The only
rounding error is one endpoint per origin. -/
theorem major_arc_typical_residue_average {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ)
    (hF : ∀ a b, 0 < a → 0 < b → F (a * b) = F a * F b)
    (hFb : OneBounded F) (q b X H : ℕ) (hq : 0 < q)
    (havoid : mrtPrimeAvoids (J.biUnion P) (b.gcd q)) :
    (∑ v ∈ range X, ‖∑ n ∈ Icc (v + 1) (v + H),
      if n % q = b % q then mrtTypicalCoefficient J P F n else 0‖) ≤
      ((q / b.gcd q).totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ (q / b.gcd q),
          ((b.gcd q : ℝ) * shortExponentialIntegral
            (mrtTypicalCoefficient J P (twistByCharacter F χ))
            (X / b.gcd q + 1) (H / b.gcd q + 1) 0 + X) := by
  calc
    _ ≤ ∑ v ∈ range X, ((q / b.gcd q).totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ (q / b.gcd q),
          ‖shortExponentialSum (dilationSequence (b.gcd q)
            (mrtTypicalCoefficient J P (twistByCharacter F χ))) H 0 v‖ :=
      sum_le_sum (fun v _ =>
        major_arc_typical_residue_window_norm J P hP F hF hFb q b v H hq havoid)
    _ = ((q / b.gcd q).totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ (q / b.gcd q),
          ∑ v ∈ range X, ‖shortExponentialSum (dilationSequence (b.gcd q)
            (mrtTypicalCoefficient J P (twistByCharacter F χ))) H 0 v‖ := by
      rw [← mul_sum, sum_comm]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum
      intro χ _
      exact major_arc_dilation_average _
        (mrtTypicalCoefficient_oneBounded J P _ (hFb.twistByCharacter χ))
        _ X H (Nat.gcd_pos_of_pos_right b hq)

end TwoPointCorrelations

end OAI
