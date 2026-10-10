import OAI.NumberTheory.DirichletL.Foundation
import OAI.NumberTheory.DirichletL.Moments.Basic

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentMask
open ActualEisensteinCubic IdealMobiusDivisorSum
open UniqueFactorizationMonoid

theorem ideal_coprime_mobius (I R : Ideal O) (hR : R ≠ 0) :
    (if IsCoprime I R then (1 : ℂ) else 0) =
      ∑ D ∈ idealDivisors R, if D ∣ I then (moebius D : ℂ) else 0 := by
  let G : Ideal O := R ⊔ I
  have hG : G ≠ 0 := by
    intro hz
    apply hR
    apply le_antisymm _ bot_le
    exact le_sup_left.trans_eq hz
  have hdiv : (idealDivisors R).filter (fun D => D ∣ I) = idealDivisors G := by
    ext D
    simp only [Finset.mem_filter, mem_idealDivisors hR, mem_idealDivisors hG,
      Ideal.dvd_iff_le, G, sup_le_iff]
  rw [← Finset.sum_filter, hdiv, sum_moebius_divisors G hG]
  simp only [Ideal.isCoprime_iff_sup_eq, G, sup_comm]

theorem tsum_ideal_divisible (D : Ideal O) (hD : D ≠ 0) (f : Ideal O → ℂ) :
    (∑' I : Ideal O, if D ∣ I then f I else 0) =
      ∑' J : Ideal O, f (D * J) := by
  let F : Ideal O → ℂ := fun I => if D ∣ I then f I else 0
  have hrange : Function.support F ⊆ Set.range (fun J : Ideal O => D * J) := by
    intro I hI
    have hd : D ∣ I := by
      by_contra hn
      exact hI (by simp only [F, ite_eq_right hn])
    obtain ⟨J, hJ⟩ := hd
    exact ⟨J, hJ.symm⟩
  have ht := (mul_right_injective₀ hD).tsum_eq hrange
  calc
    _ = ∑' J : Ideal O, F (D * J) := ht.symm
    _ = _ := by
      apply tsum_congr
      intro J
      simp only [F, dvd_mul_right, ite_true]

theorem masked_ideal_sum_eq (R : Ideal O) (hR : R ≠ 0)
    (f : Ideal O → ℂ) (hf : Summable f) :
    (∑' I : Ideal O, (if IsCoprime I R then (1 : ℂ) else 0) * f I) =
      ∑ D ∈ idealDivisors R, (moebius D : ℂ) * ∑' J : Ideal O, f (D * J) := by
  have hterm (I : Ideal O) : (if IsCoprime I R then (1 : ℂ) else 0) * f I =
      ∑ D ∈ idealDivisors R, (moebius D : ℂ) * (if D ∣ I then f I else 0) := by
    rw [ideal_coprime_mobius I R hR, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro D _
    by_cases h : D ∣ I <;> simp only [h, ite_true, ite_false, zero_mul, mul_zero]
  have hsum (D : Ideal O) :
      Summable (fun I : Ideal O => (moebius D : ℂ) * (if D ∣ I then f I else 0)) := by
    have h := (hf.indicator {I : Ideal O | D ∣ I}).mul_left (moebius D : ℂ)
    simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using h
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum (fun D _ => hsum D)]
  apply Finset.sum_congr rfl
  intro D hD
  rw [tsum_mul_left, tsum_ideal_divisible D (ne_zero_of_dvd_ne_zero hR
    ((mem_idealDivisors hR).mp hD))]

theorem annular_ideal_sum_summable (χ : Ideal O → ℂ) (W : ℝ → ℂ)
    (b X : ℝ) (hX : 0 < X) (hs : Function.support W ⊆ Set.Iic b) :
    Summable (fun I : Ideal O => χ I * W ((Ideal.absNorm I : ℝ) / X)) := by
  apply summable_of_hasFiniteSupport
  apply (Ideal.finite_setOfPred_absNorm_le (S := O) (Nat.ceil (b * X))).subset
  intro I hI
  have hw : W ((Ideal.absNorm I : ℝ) / X) ≠ 0 := by
    intro hz
    exact hI (by simp only [hz, mul_zero])
  have hn : (Ideal.absNorm I : ℝ) ≤ b * X := (div_le_iff₀ hX).mp (hs hw)
  exact_mod_cast hn.trans (Nat.le_ceil (b * X))

theorem masked_plain_ideal_sum (R : Ideal O) (hR : R ≠ 0)
    (χ : Ideal O →* ℂ) (W : ℝ → ℂ) (b X : ℝ) (hX : 0 < X)
    (hs : Function.support W ⊆ Set.Iic b) :
    (∑' I : Ideal O, (if IsCoprime I R then (1 : ℂ) else 0) *
        (χ I * W ((Ideal.absNorm I : ℝ) / X))) =
      ∑ D ∈ idealDivisors R, (moebius D : ℂ) * χ D *
        ∑' J : Ideal O, χ J * W ((Ideal.absNorm J : ℝ) / (X / Ideal.absNorm D)) := by
  rw [masked_ideal_sum_eq R hR _ (annular_ideal_sum_summable χ W b X hX hs)]
  apply Finset.sum_congr rfl
  intro D hD
  have hD0 : D ≠ 0 := ne_zero_of_dvd_ne_zero hR ((mem_idealDivisors hR).mp hD)
  have hnD : (Ideal.absNorm D : ℝ) ≠ 0 := by
    exact_mod_cast (show Ideal.absNorm D ≠ 0 by
      intro hz
      exact hD0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hterms (J : Ideal O) :
      χ (D * J) * W ((Ideal.absNorm (D * J) : ℝ) / X) =
        χ D * (χ J * W ((Ideal.absNorm J : ℝ) / (X / Ideal.absNorm D))) := by
    rw [map_mul, map_mul, Nat.cast_mul]
    have harg : (Ideal.absNorm D : ℝ) * Ideal.absNorm J / X =
        (Ideal.absNorm J : ℝ) / (X / Ideal.absNorm D) := by field_simp
    rw [harg]
    ring
  simp_rw [hterms]
  rw [tsum_mul_left]
  ring

theorem polynomial_mask_divisor_bound (ε B : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ R : Ideal O, R ≠ 0 →
      (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ((idealDivisors R).card : ℝ) ≤ C * Z ^ ε := by
  let δ := ε / (B + 1)
  have hden : 0 < B + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨C, hC, hcount⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨C, hC, ?_⟩
  intro Z hZ R hR hnorm
  have hexp : B * δ ≤ ε := by
    dsimp only [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  calc
    _ ≤ C * (Ideal.absNorm R : ℝ) ^ δ := hcount R hR
    _ ≤ C * (Z ^ B) ^ δ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hnorm hδ.le) hC.le
    _ = C * Z ^ (B * δ) := by rw [← Real.rpow_mul (by linarith : 0 ≤ Z)]
    _ ≤ C * Z ^ ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ hexp) hC.le

end SevenEighths.CenteredMomentMask
end

end OAI
