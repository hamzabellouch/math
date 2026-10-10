import OAI.NumberTheory.JointDickman.Arithmetic.PrimeSubsetCount
import OAI.NumberTheory.JointDickman.Arithmetic.RepeatedPrimeDensity

namespace OAI

/-! # Only boundedly many large primes can occur in the generating expansion -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem bounded_largePrimeSubsets_eventually (J : ℕ) (hJ : 0 < J) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ D ∈ boundedPrimeSubsets (allLargeBinPrimes J x) ⌊A*x⌋₊,
      D.card ≤ J := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hroot := (tendsto_rpow_atTop (div_pos zero_lt_one hJr)).eventually
    (eventually_gt_atTop A)
  filter_upwards [hroot,eventually_gt_atTop (1 : ℝ)] with x hxA hx D hD
  obtain ⟨hDP,hDN⟩ := mem_filter.mp hD
  have hDP := mem_powerset.mp hDP
  let q : ℝ := x^((1 : ℝ)/J)
  have hq : 1 ≤ q := Real.one_le_rpow hx.le (by positivity)
  have hpow : q^D.card ≤ (∏ p ∈ D, p : ℕ) := by
    rw [← prod_const]
    push_cast
    apply prod_le_prod₀ (fun _ _ => by positivity)
    intro p hp
    have hl := (mem_Ioc.mp (mem_filter.mp (hDP hp)).1).1
    exact (Nat.lt_of_floor_lt hl).le
  have hN : ((∏ p ∈ D, p : ℕ) : ℝ) ≤ A*x := by
    have hn : 0 < ⌊A*x⌋₊ := by
      have hp : 0 < ∏ p ∈ D, p := prod_pos (fun p hp =>
        (mem_filter.mp (hDP hp)).2.pos)
      omega
    exact (by exact_mod_cast hDN : ((∏ p ∈ D, p : ℕ) : ℝ) ≤ (⌊A*x⌋₊ : ℝ)).trans
      (Nat.floor_le (zero_le_one.trans (Nat.floor_pos.mp hn)))
  have hqJ : q^J = x := by
    simpa only [q,one_div] using Real.rpow_inv_natCast_pow (by linarith : 0 ≤ x) (by omega : J ≠ 0)
  by_contra hcard
  have hmon := pow_le_pow_right₀ hq (show J+1 ≤ D.card by omega)
  have hbig : A*x < q^(J+1) := by
    rw [pow_succ,hqJ]
    dsimp [q] at hxA ⊢
    nlinarith
  linarith

theorem generating_coefficient_le_one (z : ℕ → ℝ) (hz : ∀ p, 0 ≤ z p ∧ z p ≤ 1)
    (D : Finset ℕ) : |∏ p ∈ D, (z p-1)| ≤ 1 := by
  rw [abs_prod]
  exact prod_le_one₀ (fun _ _ => abs_nonneg _) (fun p _ => by
    rw [abs_le]
    constructor <;> linarith [(hz p).1,(hz p).2])

end JointDickman

end OAI
