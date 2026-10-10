import OAI.NumberTheory.TwoPoint.Bounds.LocalExpansion

namespace OAI

/-! The elementary p²-periodic majorant from the qualitative analytic
transfer. Prime powers of exponent at least two are left unrestricted. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def primeDefectLocal (f : ℕ → ℂ) (p n : ℕ) : ℝ :=
  if p ∣ n ∧ ¬p ^ 2 ∣ n then ‖f p‖ else 1

noncomputable def primeDefectMajorant (f : ℕ → ℂ) (P : Finset ℕ) (n : ℕ) : ℝ :=
  ∏ p ∈ P, primeDefectLocal f p n

lemma primeDefectLocal_nonneg (f : ℕ → ℂ) (p n : ℕ) : 0 ≤ primeDefectLocal f p n := by
  unfold primeDefectLocal
  split_ifs <;> positivity

lemma primeDefectLocal_le_one {f : ℕ → ℂ} (hf : OneBounded f)
    {p : ℕ} (hp : p.Prime) (n : ℕ) : primeDefectLocal f p n ≤ 1 := by
  unfold primeDefectLocal
  split_ifs
  · exact hf p hp.pos
  · exact le_rfl

lemma primeDefectMajorant_nonneg (f : ℕ → ℂ) (P : Finset ℕ) (n : ℕ) :
    0 ≤ primeDefectMajorant f P n :=
  prod_nonneg (fun p _ => primeDefectLocal_nonneg f p n)

lemma primeDefectMajorant_le_one {f : ℕ → ℂ} (hf : OneBounded f)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    primeDefectMajorant f P n ≤ 1 :=
  prod_le_one₀ (fun p _ => primeDefectLocal_nonneg f p n)
    (fun p hp => primeDefectLocal_le_one hf (hP p hp) n)

lemma prime_valuation_one_iff {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    (p ∣ n ∧ ¬p ^ 2 ∣ n) ↔ n.factorization p = 1 := by
  rw [hp.dvd_iff_one_le_factorization hn.ne', hp.pow_dvd_iff_le_factorization hn.ne']
  omega

lemma norm_le_primeDefectMajorant {f : ℕ → ℂ}
    (hfm : Multiplicative f) (hf1 : f 1 = 1) (hf : OneBounded f)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) (hn : 0 < n) :
    ‖f n‖ ≤ primeDefectMajorant f P n := by
  have he : f n = (∏ p ∈ P, f (p ^ n.factorization p)) *
      ∏ p ∈ n.primeFactors \ P, f (p ^ n.factorization p) := by
    rw [← fromPrimePowers_reconstruct f hfm hf1 hn]
    exact fromPrimePowers_split _ P (by intro p; simp [hf1]) n
  have hout : (∏ p ∈ n.primeFactors \ P, ‖f (p ^ n.factorization p)‖) ≤ 1 := by
    apply prod_le_one₀ (fun _ _ => norm_nonneg _)
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors (mem_sdiff.mp hp).1
    exact hf _ (pow_pos hprime.pos _)
  rw [he, norm_mul, norm_prod, norm_prod]
  calc
    _ ≤ (∏ p ∈ P, ‖f (p ^ n.factorization p)‖) * 1 :=
      mul_le_mul_of_nonneg_left hout (prod_nonneg (fun _ _ => norm_nonneg _))
    _ = ∏ p ∈ P, ‖f (p ^ n.factorization p)‖ := mul_one _
    _ ≤ primeDefectMajorant f P n := by
      apply prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro p hp
      unfold primeDefectLocal
      split_ifs with hv
      · rw [(prime_valuation_one_iff (hP p hp) hn).mp hv, pow_one]
      · exact hf _ (pow_pos (hP p hp).pos _)

lemma primeDefectLocal_formula (f : ℕ → ℂ) (p n : ℕ) :
    primeDefectLocal f p n = 1 - (1 - ‖f p‖) *
      ((if p ∣ n then (1 : ℝ) else 0) - (if p ^ 2 ∣ n then (1 : ℝ) else 0)) := by
  have hp : p ∣ p ^ 2 := by simp [pow_two]
  by_cases hpn : p ∣ n
  · by_cases hp2n : p ^ 2 ∣ n <;> simp [primeDefectLocal, hpn, hp2n]
  · have hp2n : ¬p ^ 2 ∣ n := fun hh => hpn (hp.trans hh)
    simp [primeDefectLocal, hpn, hp2n]

lemma primeDefectLocal_mod (f : ℕ → ℂ) (p n : ℕ) :
    primeDefectLocal f p (n % p ^ 2) = primeDefectLocal f p n := by
  unfold primeDefectLocal
  have hp : p ∣ p ^ 2 := by simp [pow_two]
  simp only [Nat.dvd_mod_iff hp, Nat.dvd_mod_iff (dvd_refl (p ^ 2))]

lemma primeDefectLocal_periodic (f : ℕ → ℂ) (p : ℕ) :
    Function.Periodic (primeDefectLocal f p) (p ^ 2) := by
  intro n
  rw [← primeDefectLocal_mod f p (n + p ^ 2), Nat.add_mod_right,
    primeDefectLocal_mod]

end TwoPointCorrelations

end OAI
