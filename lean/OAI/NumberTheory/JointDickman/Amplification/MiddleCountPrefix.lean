import OAI.NumberTheory.JointDickman.Arithmetic.RoughMiddleFrequency
import OAI.NumberTheory.TwoPointCorrelations.MRTCountMask

namespace OAI

/-! # Middle-frequency cancellation with the literal prime-count denominator -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Topology Classical

lemma prime_divisor_count_prime_pow_outside (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {p : ℕ} (hp : p.Prime) (hpP : p ∉ P) (k : ℕ) :
    finitePrimeDivisorCount P (p^k) = 0 := by
  unfold finitePrimeDivisorCount
  apply sum_eq_zero
  intro q hq
  apply ite_eq_right
  intro hd
  have hqp : q ∣ p := (hP q hq).dvd_of_dvd_pow hd
  have he : q = p := ((Nat.dvd_prime hp).mp hqp).resolve_left (hP q hq).ne_one
  exact hpP (he ▸ hq)

theorem middle_frequency_count_prefix {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (F : ℕ → ℂ) (P : Finset ℕ),
      F 1 = 1 → Multiplicative F → OneBounded F →
      (∀ p k : ℕ, p.Prime → (p:ℝ) ≤ (N:ℝ)^c → p^k ≤ N → F (p^k) = 1) →
      (∀ p ∈ P, p.Prime ∧ (N:ℝ)^c < (p:ℝ)) →
      ∀ t : ℝ, (Real.log N)^((1:ℝ)/16) ≤ |t| → |t| ≤ 4*(Real.log N)^8 →
      ‖∑ n ∈ Icc 1 N, (F n*halaszPowerPhase t n)/
        ((finitePrimeDivisorCount P n:ℂ)+1)‖/(N:ℝ) ≤ ε := by
  filter_upwards [rough_middle_frequency_small_primes hc hc1 hε,eventually_ge_atTop 1]
    with N hN hN1
  intro F P hF1 hFm hFb hsmall hP t htlo hthi
  have hNp : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  apply (div_le_iff₀ hNp).mpr
  apply mrt_reciprocal_count_polynomial_bound
  intro u hu hu1
  let G := mrtCountMaskedCoefficient F P u
  have hG1 : G 1 = 1 := by
    simp only [G,mrtCountMaskedCoefficient,hF1,mrtCountMask_one P (fun p hp => (hP p hp).1),
      Complex.ofReal_one,mul_one]
  have hGm : Multiplicative G := hFm.mrtCountMaskedCoefficient P (fun p hp => (hP p hp).1) u
  have hGb : OneBounded G := hFb.mrtCountMaskedCoefficient P hu hu1
  have hGl : ∀ p k : ℕ, p.Prime → (p:ℝ) ≤ (N:ℝ)^c → p^k ≤ N → G (p^k) = 1 := by
    intro p k hp hpc hpk
    have hpP : p ∉ P := fun h => (not_lt_of_ge hpc) (hP p h).2
    simp only [G,mrtCountMaskedCoefficient,mrtCountMask,
      prime_divisor_count_prime_pow_outside P (fun p hp => (hP p hp).1) hp hpP k,
      pow_zero,Complex.ofReal_one,mul_one,hsmall p k hp hpc hpk]
  have hb := (div_le_iff₀ hNp).mp (hN G hG1 hGm hGb hGl t htlo hthi)
  convert hb using 1
  congr 1
  unfold halaszPhaseMean
  apply sum_congr rfl
  intro n _
  dsimp [G,mrtCountMaskedCoefficient]
  ring

end JointDickman

end OAI
