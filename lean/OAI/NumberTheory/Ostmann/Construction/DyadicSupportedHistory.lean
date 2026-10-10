import OAI.NumberTheory.Ostmann.Arithmetic.SupportedHistoryCancellation
import OAI.NumberTheory.Ostmann.Construction.HarmonicBlockRecombination
import OAI.NumberTheory.Ostmann.Construction.DyadicPrimeRange

namespace OAI

/-! # The supported one-sided estimate over the entire long-prime range -/

namespace Ostmann

open scoped BigOperators Classical

def boundedDyadicIndex (E p : ℕ) : Fin (Nat.log 2 E + 1) :=
  ⟨min (Nat.log 2 p) (Nat.log 2 E), by omega⟩

theorem boundedDyadicIndex_eq (E p : ℕ) (hp : p ≤ E) :
    (boundedDyadicIndex E p : ℕ) = Nat.log 2 p :=
  min_eq_left (Nat.log_mono_right hp)

theorem dyadic_progression_padding (a M : ℕ) (ha : 0 < a) (hM : 0 < M) (hMa : M ≤ a) :
    a < (a / M + 1) * M ∧ (((a / M + 1) * M : ℕ) : ℝ) / a ≤ 2 := by
  have hdiv := Nat.mod_add_div a M
  have hmod := Nat.mod_lt a hM
  have hmul := Nat.div_mul_le_self a M
  constructor
  · nlinarith
  · apply (div_le_iff₀ (by exact_mod_cast ha : (0 : ℝ) < a)).mpr
    have hn : (a / M + 1) * M ≤ 2 * a := by nlinarith
    exact_mod_cast hn

/-- Every sharp support condition is retained. The loss for all long-prime
dyadic pieces is only their count, and the original normalizing mass remains. -/
theorem dyadic_supported_history_bound {σ I : Type*} [Fintype I] {n : ℕ}
    (P Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (χ : ∀ q : Q, DirichletCharacter ℂ (q : ℕ)) (hnonprincipal : ∀ q, χ q ≠ 1)
    (A E M : ℕ) [NeZero M] (hA : 0 < A) (hMA : M ≤ A)
    (hM : ∀ q : Q, M.Coprime (q : ℕ))
    (hlow : ∀ p ∈ P, 2 * A ≤ p) (hhigh : ∀ p ∈ P, p ≤ E)
    (b : ℝ) (hb : 0 < b) (hbQ : ∀ q ∈ Q, b ≤ (q : ℝ))
    (hPmass : 0 < ∑ p ∈ P, (p : ℝ)⁻¹) (hQmass : 0 < ∑ q ∈ Q, (q : ℝ)⁻¹)
    (N : Q → I → MvPolynomial σ ℤ) (d : Q → I → ℤ) (s : Q → I → ℕ)
    (fixed : Q → σ → ℤ) (coord : σ)
    (hd : ∀ q j, d q j ≠ 0) (hdiv : ∀ q j, d q j * s q j ∣ (M : ℤ))
    (F : Q → Fin n → ClippedPolynomialFactor) (B : ℝ) (D Bq : ℕ)
    (hB : 0 ≤ B) (hbudget : ∀ q, smoothPolynomialBudget (F q) ≤ B)
    (hdegree : ∀ q, (∑ j, (F q j).polynomial.natDegree) ≤ D)
    (hBq : ∀ q : Q, (q : ℕ) ≤ Bq)
    (U : ℕ → ℂ) (V : Q → ℂ) (hU : ∀ p ∈ P, ‖U p‖ ≤ 1) (hV : ∀ q, ‖V q‖ ≤ 1) :
    ‖∑ p : P, (primeSubsetPrior P P p : ℂ) *
      (U p * ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) * V q *
        (χ q ((p : ℕ) : ZMod (q : ℕ)) *
          supportedHistoryAmplitude (N q) (d q) (s q) (fixed q) coord (F q) (p : ℕ)))‖ ^ 2 ≤
      ((Nat.log 2 E + 1 : ℕ) : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
        (((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * b⁻¹) * (2 * B ^ 2) +
          (M : ℝ) * ((3 ^ (2 * (3 * D)) : ℕ) * (2 * (A : ℝ)⁻¹ * B ^ 2)) * (Bq : ℝ) ^ 2) := by
  classical
  let G (p : ℕ) : ℂ := U p * ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) * V q *
    (χ q (p : ZMod (q : ℕ)) *
      supportedHistoryAmplitude (N q) (d q) (s q) (fixed q) coord (F q) p)
  have hc := harmonic_partition_bound P (boundedDyadicIndex E) G
      (((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * b⁻¹) * (2 * B ^ 2) +
        (M : ℝ) * ((3 ^ (2 * (3 * D)) : ℕ) * (2 * (A : ℝ)⁻¹ * B ^ 2)) * (Bq : ℝ) ^ 2)
      hPmass
  simp only [Fintype.card_fin] at hc
  apply hc
  intro j
  let S : Finset ℕ := @Finset.filter ℕ (fun p => boundedDyadicIndex E p = j)
    (fun _ => Classical.propDecidable _) P
  have hmem (p : ℕ) : p ∈ S ↔ p ∈ P ∧ boundedDyadicIndex E p = j := by
    simp only [S, Finset.mem_filter]
  change ‖∑ p ∈ S, ((p : ℝ)⁻¹ : ℂ) * G p‖ ^ 2 ≤
    (∑ p ∈ S, (p : ℝ)⁻¹) *
      (((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * b⁻¹) * (2 * B ^ 2) +
        (M : ℝ) * ((3 ^ (2 * (3 * D)) : ℕ) * (2 * (A : ℝ)⁻¹ * B ^ 2)) * (Bq : ℝ) ^ 2)
  by_cases hS : S.Nonempty
  · have hpos (p : ℕ) (hp : p ∈ S) : 0 < p := by
      have := hlow p ((hmem p).mp hp).1
      omega
    have hm : 0 < ∑ p ∈ S, (p : ℝ)⁻¹ := by
      apply Finset.sum_pos (fun p hp => inv_pos.mpr (by exact_mod_cast hpos p hp)) hS
    let a : ℕ := 2 ^ (j : ℕ)
    have ha : 0 < a := pow_pos (by norm_num) _
    have hr (p : ℕ) (hp : p ∈ S) : a ≤ p ∧ p < 2 * a := by
      have hmp := (hmem p).mp hp
      have he : Nat.log 2 p = (j : ℕ) := by
        rw [← boundedDyadicIndex_eq E p (hhigh p hmp.1), hmp.2]
      constructor
      · simpa only [he] using Nat.pow_log_le_self 2 (Nat.ne_of_gt (hpos p hp))
      · simpa only [he, pow_succ, mul_comm] using
          Nat.lt_pow_succ_log_self (b := 2) (by norm_num) p
    have hAa : A ≤ a := by
      obtain ⟨p, hp⟩ := hS
      have := (hr p hp).2
      have := hlow p ((hmem p).mp hp).1
      omega
    have hpad := dyadic_progression_padding a M ha (NeZero.pos M) (hMA.trans hAa)
    have hlocal := harmonic_supported_history_bound S Q hprime χ hnonprincipal
      a M (a / M + 1) ha hM (fun p hp => (hr p hp).1)
      (fun p hp => by have := (hr p hp).2; omega)
      b hb hbQ hm hQmass N d s fixed coord hd hdiv F B D Bq hB hbudget hdegree hBq
      (fun p => U p) V (fun p => hU p ((hmem p).mp p.property).1) hV
    apply harmonic_raw_of_mean_bound S G _ hm
    apply hlocal.trans
    have hi : (a : ℝ)⁻¹ ≤ (A : ℝ)⁻¹ :=
      inv_anti₀ (by exact_mod_cast hA) (by exact_mod_cast hAa)
    gcongr
    exact hpad.2
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [he, Finset.sum_empty, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_mul]
    exact le_rfl

end Ostmann

end OAI
