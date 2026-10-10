import OAI.NumberTheory.JointDickman.Arithmetic.PrimePresencePhase
import OAI.NumberTheory.JointDickman.Amplification.FiniteWeightAverages

namespace OAI

/-! # Exact oscillatory expansion of a fixed finite-prime weight -/
namespace JointDickman
open Finset TwoPointCorrelations
open scoped Classical

lemma finitePrimeDivisorCount_mul_invariant (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {d : ℕ} (hd : ∀ p ∈ P, ¬p ∣ d) (n : ℕ) :
    finitePrimeDivisorCount P (d*n) = finitePrimeDivisorCount P n := by
  unfold finitePrimeDivisorCount
  apply sum_congr rfl
  intro p hp
  simp only [(hP p hp).dvd_mul, hd p hp, false_or]

/-- No limiting estimate is used: the fixed weight becomes finitely many
rescaled prefix sums, with the original prime-count denominator retained. -/
theorem finite_weight_count_phase_expansion (E P : Finset ℕ)
    (hE : ∀ p ∈ E, p.Prime) (hP : ∀ p ∈ P, p.Prime)
    (hdis : Disjoint E P) (w : ℕ → ℝ) (F : ℕ → ℂ)
    (hF : ∀ D ∈ E.powerset, ∀ n : ℕ, 0 < n →
      F ((∏ p ∈ D, p)*n) = F n) (t : ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, (F n*(finitePrimeWeight E w n:ℂ)*halaszPowerPhase t n)/
      ((finitePrimeDivisorCount P n:ℂ)+1)) =
    ∑ D ∈ E.powerset, ((∏ p ∈ D, (w p-1):ℝ):ℂ)*
      halaszPowerPhase t (∏ p ∈ D, (p:ℝ))*
      ∑ n ∈ Icc 1 (N/(∏ p ∈ D, p)),
        (F n*halaszPowerPhase t n)/((finitePrimeDivisorCount P n:ℂ)+1) := by
  have he n (hn : n ∈ Icc 1 N) : (finitePrimeWeight E w n:ℂ) =
      ∑ D ∈ E.powerset, if (∏ p ∈ D, p) ∣ n then
        ((∏ p ∈ D, (w p-1):ℝ):ℂ) else 0 := by
    rw [finitePrimeWeight_expansion hE w (by have := (mem_Icc.mp hn).1; omega)]
    simp only [Complex.ofReal_sum, Complex.ofReal_mul]
    apply sum_congr rfl
    intro D _
    split_ifs <;> simp
  trans ∑ n ∈ Icc 1 N,
    (F n*(∑ D ∈ E.powerset, if (∏ p ∈ D, p) ∣ n then
      ((∏ p ∈ D, (w p-1):ℝ):ℂ) else 0)*halaszPowerPhase t n)/
        ((finitePrimeDivisorCount P n:ℂ)+1)
  · apply sum_congr rfl
    intro n hn
    rw [he n hn]
  simp only [mul_sum, sum_mul, sum_div]
  rw [sum_comm]
  apply sum_congr rfl
  intro D hD
  let d := ∏ p ∈ D, p
  have hd : 0 < d := prod_pos (fun p hp => (hE p (mem_powerset.mp hD hp)).pos)
  have hnot : ∀ p ∈ P, ¬p ∣ d := by
    intro p hp hpd
    obtain ⟨q,hq,hpq⟩ := ((hP p hp).prime.dvd_finsetProd_iff id).mp hpd
    have heq : p=q := ((Nat.dvd_prime (hE q (mem_powerset.mp hD hq))).mp hpq).resolve_left
      (hP p hp).ne_one
    exact (disjoint_left.mp hdis (mem_powerset.mp hD hq) (heq ▸ hp))
  have hs : (∑ n ∈ Icc 1 N,
      F n*(if d ∣ n then ((∏ p ∈ D, (w p-1):ℝ):ℂ) else 0)*halaszPowerPhase t n /
        ((finitePrimeDivisorCount P n:ℂ)+1)) =
      ∑ n ∈ Icc 1 N, if d ∣ n then
        ((∏ p ∈ D, (w p-1):ℝ):ℂ)*
          (F n*halaszPowerPhase t n / ((finitePrimeDivisorCount P n:ℂ)+1)) else 0 := by
    apply sum_congr rfl
    intro n _
    split_ifs <;> ring
  rw [hs,sum_Icc_dvd_reindex hd]
  apply sum_congr rfl
  intro n hn
  have hn0 : 0 < n := (mem_Icc.mp hn).1
  rw [hF D hD n hn0,finitePrimeDivisorCount_mul_invariant P hP hnot,
    Nat.cast_mul,halasz_power_phase_mul t _ _ (by exact_mod_cast hd)
      (by exact_mod_cast hn0),Nat.cast_prod]
  ring

end JointDickman

end OAI
