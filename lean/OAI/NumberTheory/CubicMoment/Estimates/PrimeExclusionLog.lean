import OAI.NumberTheory.CubicMoment.Estimates.PrimeExclusion
import OAI.NumberTheory.CubicMoment.Estimates.PrimeBinGeometry

namespace OAI

/-! The logarithmic, rather than merely subpower, number of prime
exclusions. This is necessary when the free prime is exp(sqrt(log X)). -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem primary_prime_divisor_card_log (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (e : Eisenstein) (he : e ≠ 0) :
    ((S.filter (fun p => p ∣ e)).card:ℝ) ≤ Real.log (norm e)/Real.log 2 := by
  let T := S.filter (fun p => p ∣ e)
  have hp (p : Eisenstein) (hp : p ∈ T) : primaryPrime p :=
    hS p (Finset.mem_filter.mp hp).1
  have hd : (∏ p ∈ T, p) ∣ e := by
    apply Finset.prod_dvd_of_coprime
    · intro p hpT q hqT hpq
      exact primaryPrimes_isCoprime (hp p hpT) (hp q hqT) hpq
    · intro p hpT
      exact (Finset.mem_filter.mp hpT).2
  have hprod : (2:ℝ)^T.card ≤ norm e := by
    calc
      _ = ∏ _p ∈ T, (2:ℝ) := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ T, norm p := Finset.prod_le_prod₀ (fun _ _ => by norm_num)
        (fun p hpT => primaryPrime_norm_ge_two (hp p hpT))
      _ = norm (∏ p ∈ T, p) := (norm_finset_prod _ _).symm
      _ ≤ norm e := norm_le_of_dvd_nonzero he hd
  have hn : 0 < norm e := zero_lt_one.trans_le (one_le_norm he)
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mpr
  exact (Real.pow_le_iff_le_log (by norm_num : (0:ℝ) < 2) hn).mp hprod

theorem prime_exclusion_logarithmic (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (e : Eisenstein) (he : e ≠ 0)
    (w : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M) (hw : ∀ p ∈ S, ‖w p‖ ≤ M) :
    ‖(∑ p ∈ S, w p)-(∑ p ∈ S with IsCoprime p e, w p)‖ ≤
      M*(Real.log (norm e)/Real.log 2) := by
  have hsub : S.filter (fun p => ¬IsCoprime p e) ⊆ S.filter (fun p => p ∣ e) := by
    intro p hp
    obtain ⟨hpS,hp⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨hpS,?_⟩
    by_contra hn
    exact hp ((hS p hpS).2.irreducible.coprime_iff_not_dvd.mpr hn)
  exact (prime_exclusion_difference S e w hw).trans
    (mul_le_mul_of_nonneg_left ((Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (primary_prime_divisor_card_log S hS e he)) hM)

theorem prime_exclusion_polynomial_norm (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (e : Eisenstein) (he : e ≠ 0)
    (w : Eisenstein → ℂ) {M X d : ℝ} (hM : 0 ≤ M) (hX : 0 < X)
    (heX : norm e ≤ X^d) (hw : ∀ p ∈ S, ‖w p‖ ≤ M) :
    ‖(∑ p ∈ S, w p)-(∑ p ∈ S with IsCoprime p e, w p)‖ ≤
      (M*d/Real.log 2)*Real.log X := by
  have hn : 0 < norm e := zero_lt_one.trans_le (one_le_norm he)
  have hl := Real.log_le_log hn heX
  rw [Real.log_rpow hX] at hl
  apply (prime_exclusion_logarithmic S hS e he w hM hw).trans
  calc
    _ ≤ M*((d*Real.log X)/Real.log 2) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hl (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))) hM
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
