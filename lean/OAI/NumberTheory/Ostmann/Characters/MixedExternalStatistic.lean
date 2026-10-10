import OAI.NumberTheory.Ostmann.Characters.MixedBulkSymmetrization

namespace OAI

/-! # The original statistic is unchanged by bulk symmetrization -/

namespace Ostmann
open scoped Classical BigOperators

theorem mixedExternalAverage_sum {B A J : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v r w center : ℝ)
    (T : Finset J) (F : J → ℤ → (B → A) → ℝ → ℝ → ℂ) :
    mixedExternalAverage ν N u v r w center (fun s y x z => ∑ j ∈ T, F j s y x z) =
      ∑ j ∈ T, mixedExternalAverage ν N u v r w center (F j) := by
  simp only [mixedExternalAverage_finite, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem mixedExternalAverage_const_mul {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v r w center : ℝ)
    (c : ℂ) (F : ℤ → (B → A) → ℝ → ℝ → ℂ) :
    mixedExternalAverage ν N u v r w center (fun s y x z => c * F s y x z) =
      c * mixedExternalAverage ν N u v r w center F := by
  simp only [mixedExternalAverage_finite, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem mixedBulkSymmetrize_statistic {B A : Type*} [Fintype B] [Fintype A]
    (n m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (ν : B → A → ℝ) (hν : ∀ j k, ν (slot j) = ν (slot k))
    (N : ℕ) (u v r w center : ℝ)
    (F H : ℤ → (B → A) → ℝ → ℝ → ℂ)
    (hH : ∀ e s y x z, H s (selectedBulkSample slot e y) x z = H s y x z) :
    mixedExternalAverage ν N u v r w center
      (fun s y x z => H s y x z * mixedBulkSymmetrize n m slot F s y x z) =
    mixedExternalAverage ν N u v r w center (fun s y x z => H s y x z * F s y x z) := by
  let J := Equiv.Perm (TreeLeafIndex n × Fin m)
  have hc : (Fintype.card J : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := J)
  have he (e : J) : mixedExternalAverage ν N u v r w center
      (fun s y x z => H s y x z * F s (selectedBulkSample slot e⁻¹ y) x z) =
      mixedExternalAverage ν N u v r w center (fun s y x z => H s y x z * F s y x z) := by
    have h := mixedExternalAverage_selectedBulkSample slot e⁻¹ ν hν N u v r w center
      (fun s y x z => H s y x z * F s y x z)
    simpa only [hH] using h
  have hpoint : (fun s y x z => H s y x z * mixedBulkSymmetrize n m slot F s y x z) =
      (fun s y x z => (Fintype.card J : ℂ)⁻¹ * ∑ e : J,
        H s y x z * F s (selectedBulkSample slot e⁻¹ y) x z) := by
    funext s y x z
    simp only [mixedBulkSymmetrize, finiteFamilyAverage, ← Finset.mul_sum]
    ring
  rw [hpoint, mixedExternalAverage_const_mul, mixedExternalAverage_sum]
  simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem mixedExternalAverage_weighted_cauchy {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (hν : ∀ b a, 0 ≤ ν b a)
    (N : ℕ) (u v r w center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) (W : ℤ → (B → A) → ℝ → ℝ → ℝ)
    (hW : ∀ s y x z, 0 ≤ W s y x z) :
    ‖mixedExternalAverage ν N u v r w center (fun s y x z => F s y x z * W s y x z)‖ ^ 2 ≤
      (mixedExternalAverage ν N u v r w center (fun s y x z => (W s y x z : ℂ))).re *
      (mixedExternalAverage ν N u v r w center
        (fun s y x z => (‖F s y x z‖ ^ 2 : ℂ) * W s y x z)).re := by
  let ρ := fun x : MixedExternalPoint B A N u v r w =>
    mixedExternalPrior ν N u v r w center x *
      W x.1.val x.2.1 (Real.log x.2.2.2.val) (Real.log x.2.2.1.val)
  let f := fun x : MixedExternalPoint B A N u v r w =>
    F x.1.val x.2.1 (Real.log x.2.2.2.val) (Real.log x.2.2.1.val)
  have hρ (x) : 0 ≤ ρ x := mul_nonneg
    (mixedExternalPrior_nonneg ν hν N u v r w center x) (hW _ _ _ _)
  have he (x) : Real.sqrt (ρ x) ^ 2 = ρ x := Real.sq_sqrt (hρ x)
  have hprod (x) : (Real.sqrt (ρ x) : ℂ) * ((Real.sqrt (ρ x) : ℂ) * f x) =
      (ρ x : ℂ) * f x := by
    rw [← mul_assoc, ← pow_two, ← Complex.ofReal_pow, he]
  have hc := complex_pairing_sq_le (fun x => (Real.sqrt (ρ x) : ℂ))
    (fun x => (Real.sqrt (ρ x) : ℂ) * f x)
  simp only [hprod, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, he] at hc
  simp only [mixedExternalAverage_finite, Complex.re_sum, Complex.mul_re,
    ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
    sub_zero]
  convert hc using 1
  · congr 2
    apply Finset.sum_congr rfl
    intro x _
    dsimp [ρ, f]
    push_cast
    ring
  · apply congrArg₂ (· * ·)
    · rfl
    · apply Finset.sum_congr rfl
      intro x _
      dsimp [ρ, f]
      ring

theorem mixedBulkSymmetrize_statistic_cauchy {B A : Type*} [Fintype B] [Fintype A]
    (n m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (ν : B → A → ℝ) (hν : ∀ b a, 0 ≤ ν b a)
    (hidentical : ∀ j k, ν (slot j) = ν (slot k))
    (N : ℕ) (u v r w center : ℝ)
    (F H : ℤ → (B → A) → ℝ → ℝ → ℂ)
    (hH : ∀ e s y x z, H s (selectedBulkSample slot e y) x z = H s y x z)
    (W : ℝ → ℝ → ℝ) (hW : ∀ x z, 0 ≤ W x z) :
    ‖mixedExternalAverage ν N u v r w center
      (fun s y x z => (H s y x z * F s y x z) * W x z)‖ ^ 2 ≤
    (mixedExternalAverage ν N u v r w center (fun _ _ x z => (W x z : ℂ))).re *
    (mixedExternalAverage ν N u v r w center (fun s y x z =>
      (‖mixedBulkSymmetrize n m slot F s y x z‖ ^ 2 : ℂ) *
        ((W x z : ℂ) * (‖H s y x z‖ ^ 2 : ℝ)))).re := by
  have hs := mixedBulkSymmetrize_statistic n m slot ν hidentical N u v r w center
    F (fun s y x z => H s y x z * W x z) (fun e s y x z => by rw [hH])
  have hm : mixedExternalAverage ν N u v r w center
      (fun s y x z => (H s y x z * F s y x z) * W x z) =
    mixedExternalAverage ν N u v r w center (fun s y x z =>
      (H s y x z * mixedBulkSymmetrize n m slot F s y x z) * W x z) := by
    calc
      _ = mixedExternalAverage ν N u v r w center
          (fun s y x z => (H s y x z * W x z) * F s y x z) := by
        congr 1; funext s y x z; ring
      _ = _ := by
        rw [← hs]
        congr 1; funext s y x z; ring
  rw [hm]
  have hc := mixedExternalAverage_weighted_cauchy ν hν N u v r w center
    (fun s y x z => H s y x z * mixedBulkSymmetrize n m slot F s y x z)
    (fun _ _ x z => W x z) (fun _ _ x z => hW x z)
  have heq : (fun s y x z =>
      (‖mixedBulkSymmetrize n m slot F s y x z‖ ^ 2 : ℂ) *
        ((W x z : ℂ) * (‖H s y x z‖ ^ 2 : ℝ))) =
      (fun s y x z => (‖H s y x z * mixedBulkSymmetrize n m slot F s y x z‖ ^ 2 : ℂ) * W x z) := by
    funext s y x z
    simp only [norm_mul, mul_pow, Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  rw [heq]
  exact hc

end Ostmann

end OAI
