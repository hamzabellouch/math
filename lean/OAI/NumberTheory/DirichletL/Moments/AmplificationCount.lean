import OAI.NumberTheory.DirichletL.Moments.AmplificationGlobal
import OAI.NumberTheory.DirichletL.CenteredExceptionalCount

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationCount
open UniqueFactorizationMonoid CenteredExceptionalCount
local notation "O" => ActualEisensteinCubic.O

theorem primeDivisors_product_dvd (S : Finset (Ideal O))
    (hP : ∀ P ∈ S, Prime P) (I : Ideal O) (hd : ∀ P ∈ S, P ∣ I) :
    (∏ P ∈ S, P) ∣ I := by
  apply Finset.prod_dvd_of_coprime _ hd
  intro P hPS Q hQS hPQ
  let : P.IsMaximal := (Ideal.isPrime_of_prime (hP P hPS)).isMaximal (hP P hPS).ne_zero
  let : Q.IsMaximal := (Ideal.isPrime_of_prime (hP Q hQS)).isMaximal (hP Q hQS).ne_zero
  exact Ideal.isCoprime_of_isMaximal hPQ

theorem large_prime_divisor_count (S : Finset (Ideal O)) (hP : ∀ P ∈ S, Prime P)
    (I : Ideal O) (hI : I ≠ 0) (hd : ∀ P ∈ S, P ∣ I)
    (Z ℓ B : ℝ) (hZ : 1 < Z) (hℓ : 0 < ℓ)
    (hlower : ∀ P ∈ S, Z^ℓ ≤ (Ideal.absNorm P : ℝ))
    (hupper : (Ideal.absNorm I : ℝ) ≤ Z^B) : (S.card : ℝ) ≤ B/ℓ := by
  have hpow : Z ^ (ℓ * (S.card : ℝ)) ≤ Z^B := by
    calc
      _ = (Z^ℓ)^S.card := Real.rpow_mul_natCast (zero_lt_one.trans hZ).le ℓ S.card
      _ = ∏ _P ∈ S, Z^ℓ := (Finset.prod_const _).symm
      _ ≤ ∏ P ∈ S, (Ideal.absNorm P : ℝ) := Finset.prod_le_prod₀
        (fun _ _ => Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hlower
      _ = (Ideal.absNorm (∏ P ∈ S, P) : ℝ) := by simp only [map_prod,Nat.cast_prod]
      _ ≤ (Ideal.absNorm I : ℝ) := norm_le_of_dvd hI (primeDivisors_product_dvd S hP I hd)
      _ ≤ _ := hupper
  have he := (Real.rpow_le_rpow_left_iff hZ).mp hpow
  apply (le_div_iff₀ hℓ).mpr
  simpa only [mul_comm] using he

theorem indexed_large_prime_divisor_count {α : Type*} (S : Finset α) (P : α → Ideal O)
    (hinj : Set.InjOn P S) (hp : ∀ i ∈ S, Prime (P i))
    (I : Ideal O) (hI : I ≠ 0) (hd : ∀ i ∈ S, P i ∣ I)
    (Z ℓ B : ℝ) (hZ : 1 < Z) (hℓ : 0 < ℓ)
    (hlower : ∀ i ∈ S, Z^ℓ ≤ (Ideal.absNorm (P i) : ℝ))
    (hupper : (Ideal.absNorm I : ℝ) ≤ Z^B) : (S.card : ℝ) ≤ B/ℓ := by
  have hb := large_prime_divisor_count (S.image P) (by
      intro Q hQ
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
      exact hp i hi) I hI (by
      intro Q hQ
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
      exact hd i hi) Z ℓ B hZ hℓ (by
      intro Q hQ
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
      exact hlower i hi) hupper
  simpa only [Finset.card_image_of_injOn hinj] using hb

theorem amplified_row_fiber_count (F : Finset (O × O)) (y : O) (hy : y ≠ 0)
    (hprime : ∀ x ∈ F, Prime x.2)
    (hprimary : ∀ x ∈ F, ConcretePrimeRowBridge.goodLambda^2 ∣ x.2-1)
    (hrow : ∀ x ∈ F, x.2^6*x.1 = y)
    (Z ℓ B : ℝ) (hZ : 1 < Z) (hℓ : 0 < ℓ)
    (hlower : ∀ x ∈ F, Z^ℓ ≤ (Ideal.absNorm (Ideal.span {x.2}) : ℝ))
    (hupper : (Ideal.absNorm (Ideal.span {y}) : ℝ) ≤ Z^B) : (F.card : ℝ) ≤ B/ℓ := by
  apply indexed_large_prime_divisor_count F (fun x => Ideal.span {x.2}) ?_
    (fun x hx => CubicEisenstein.gaussPrimeIdeal_prime x.2 (hprime x hx))
    (Ideal.span {y}) (Ideal.span_singleton_eq_bot.not.mpr hy) ?_ Z ℓ B hZ hℓ hlower hupper
  · intro x hx z hz heq
    have hp : x.2 = z.2 := by
      rw [← CompletedGauss.primaryGenerator_span x.2 (hprime x hx).ne_zero (hprimary x hx),
        ← CompletedGauss.primaryGenerator_span z.2 (hprime z hz).ne_zero (hprimary z hz)]
      exact congrArg CompletedGauss.primaryGenerator heq
    have hh : x.1 = z.1 := by
      apply mul_left_cancel₀ (pow_ne_zero 6 (hprime x hx).ne_zero)
      rw [hrow x hx,hp,hrow z hz]
    exact Prod.ext hh hp
  · intro x hx
    rw [Ideal.dvd_iff_le,Ideal.span_singleton_le_span_singleton,← hrow x hx]
    exact (dvd_pow_self x.2 (by decide : 6 ≠ 0)).trans (dvd_mul_right _ _)

theorem positive_pushforward_bound {α β : Type*} [DecidableEq β]
    (S : Finset α) (f : α → β) (g : β → ℝ) (C : ℝ)
    (hg : ∀ y ∈ S.image f, 0 ≤ g y)
    (hf : ∀ y ∈ S.image f, ((S.filter (fun x => f x = y)).card : ℝ) ≤ C) :
    (∑ x ∈ S, g (f x)) ≤ C * ∑ y ∈ S.image f, g y := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem f hx)]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  calc
    _ = ((S.filter (fun x => f x = y)).card : ℝ) * g y := by
      rw [← nsmul_eq_mul,← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hf y hy) (hg y hy)

end SevenEighths.CenteredMomentAmplificationCount

end

end OAI
