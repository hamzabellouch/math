import OAI.NumberTheory.TwoPoint.Halasz.HalaszUnitCorrection
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.Prime.Int

namespace OAI

/-! Logarithmic majorization of the absolute constant-one correction.
Only its bound by two on positive prime powers is used. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def halaszPrimePowerLog (n : ℕ) : ℝ :=
  if IsPrimePow n then 2 * Real.log n else 0

lemma halaszPrimePowerLog_nonneg (n : ℕ) : 0 ≤ halaszPrimePowerLog n := by
  unfold halaszPrimePowerLog
  split_ifs with h
  · exact mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast h.one_lt.le))
  · exact le_rfl

lemma halasz_log_factorization (n : ℕ) (hn : n ≠ 0) :
    Real.log n = ∑ p ∈ n.factorization.support, Real.log ((p ^ n.factorization p : ℕ) : ℝ) := by
  have he := Nat.prod_factorization_pow_eq_self hn
  calc
    _ = Real.log ((n.factorization.prod (fun p k => p ^ k) : ℕ) : ℝ) := by rw [he]
    _ = Real.log (∏ p ∈ n.factorization.support, ((p ^ n.factorization p : ℕ) : ℝ)) := by
      simp only [Finsupp.prod, Nat.cast_prod]
    _ = _ := Real.log_prod (fun p hp => by
      exact_mod_cast pow_ne_zero (n.factorization p) (Nat.prime_of_mem_primeFactors
        (by simpa only [Nat.support_factorization] using hp)).ne_zero)

lemma halasz_unit_correction_log_bound (F : ℕ → ℂ) (hF : OneBounded F) (n : ℕ) :
    ‖halaszUnitCorrection F n‖ * Real.log n ≤
      ∑ d ∈ n.divisors, halaszPrimePowerLog d * ‖halaszUnitCorrection F (n / d)‖ := by
  by_cases hn : n = 0
  · subst n
    simp
  let S := n.factorization.support
  let v := fun p => p ^ n.factorization p
  have hp (p : ℕ) (h : p ∈ S) : p.Prime :=
    Nat.prime_of_mem_primeFactors (by simpa only [S, Nat.support_factorization] using h)
  have hk (p : ℕ) (h : p ∈ S) : 0 < n.factorization p :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp h)
  have hpower (p : ℕ) (h : p ∈ S) : IsPrimePow (v p) :=
    ⟨p, n.factorization p, (hp p h).prime, hk p h, rfl⟩
  have hvpos (p : ℕ) (h : p ∈ S) : 0 < v p := pow_pos (hp p h).pos _
  have hnorm (p : ℕ) (h : p ∈ S) :
      ‖halaszUnitCorrection F n‖ ≤ 2 * ‖halaszUnitCorrection F (n / v p)‖ := by
    have hquot : 0 < n / v p := Nat.ordCompl_pos p hn
    have hcop := (Nat.coprime_ordCompl (hp p h) hn).pow_left (n.factorization p)
    have he := fromPrimePowers_multiplicative (halaszUnitCorrectionLocal F)
      (v p) (n / v p) (hvpos p h) hquot hcop
    change halaszUnitCorrection F (v p * (n / v p)) =
      halaszUnitCorrection F (v p) * halaszUnitCorrection F (n / v p) at he
    rw [Nat.mul_div_cancel' (Nat.ordProj_dvd n p)] at he
    rw [he, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (by rw [halasz_unit_correction_prime_pow F (hp p h)];
          exact halasz_unit_correction_local_bound F hF (hp p h) (hk p h)) (norm_nonneg _)
  have hinj : Set.InjOn v (S : Set ℕ) := by
    intro p hpS q hqS he
    exact ((hp p hpS).pow_inj' (hp q hqS) (hk p hpS).ne' (hk q hqS).ne' he).1
  have hsub : S.image v ⊆ n.divisors.filter IsPrimePow := by
    intro d hd
    obtain ⟨p, hpS, rfl⟩ := mem_image.mp hd
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.ordProj_dvd n p, hn⟩, hpower p hpS⟩
  calc
    _ = ∑ p ∈ S, ‖halaszUnitCorrection F n‖ * Real.log (v p) := by
      rw [halasz_log_factorization n hn, mul_sum]
    _ ≤ ∑ p ∈ S, halaszPrimePowerLog (v p) * ‖halaszUnitCorrection F (n / v p)‖ := by
      apply sum_le_sum
      intro p hpS
      rw [halaszPrimePowerLog, ite_eq_left (hpower p hpS)]
      have hl : 0 ≤ Real.log (v p : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (hpower p hpS).one_lt.le)
      nlinarith [mul_le_mul_of_nonneg_right (hnorm p hpS) hl]
    _ = ∑ d ∈ S.image v, halaszPrimePowerLog d * ‖halaszUnitCorrection F (n / d)‖ :=
      (sum_image (f := fun d : ℕ => halaszPrimePowerLog d * ‖halaszUnitCorrection F (n / d)‖) hinj).symm
    _ ≤ ∑ d ∈ n.divisors.filter IsPrimePow,
        halaszPrimePowerLog d * ‖halaszUnitCorrection F (n / d)‖ :=
      sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => mul_nonneg
        (halaszPrimePowerLog_nonneg d) (norm_nonneg _))
    _ = _ := by
      rw [sum_filter]
      apply sum_congr rfl
      intro d _
      by_cases hd : IsPrimePow d <;> simp [halaszPrimePowerLog, hd]

end TwoPointCorrelations

end OAI
