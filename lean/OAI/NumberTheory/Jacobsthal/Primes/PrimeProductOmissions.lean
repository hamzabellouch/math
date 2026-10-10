import Mathlib.Data.Nat.Totient
import OAI.NumberTheory.Jacobsthal.Primes.HighPrimeRemoval
import OAI.NumberTheory.Jacobsthal.Sieve.ResidueCountDifference

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosPrimeInputs.PrimeProductOmissions

open _root_.Finset
open NumberTheoryLean.LargePrimeDeletion SubsetPrimeSieve MertensStrong

noncomputable def reducedPrimes (z q : ℕ) : Finset ℕ := cutoffPrimes z \ q.primeFactors

lemma factor_bounds {p : ℕ} (hp : p.Prime) :
    0 < 1 - (p : ℝ)⁻¹ ∧ 1 - (p : ℝ)⁻¹ ≤ 1 := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  exact ⟨sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1), sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg _))⟩

lemma totient_euler (q : ℕ) : (q.totient : ℝ) = (q : ℝ) * euler q.primeFactors := by
  unfold euler
  have h := congrArg (fun r : ℚ => (r : ℝ)) (Nat.totient_eq_mul_prod_factors q)
  push_cast at h
  exact h

theorem euler_omissions_le (P : Finset ℕ) (q : ℕ) (hq : 0 < q)
    (hP : ∀ p ∈ P, p.Prime) : euler (P \ q.primeFactors) ≤ euler P * q / q.totient := by
  have hQ : ∀ p ∈ q.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hsmall : euler q.primeFactors ≤ euler (P ∩ q.primeFactors) := by
    apply prod_le_prod_of_subset_of_le_one₀ inter_subset_right
    · intro p hp
      exact (factor_bounds (hQ p hp)).1.le
    · intro p hp _
      exact (factor_bounds (hQ p hp)).2
  have hdiff : P \ (P ∩ q.primeFactors) = P \ q.primeFactors := by
    ext p
    simp
  have hprod : euler (P \ q.primeFactors) * euler (P ∩ q.primeFactors) = euler P := by
    unfold euler
    rw [← hdiff]
    exact prod_sdiff inter_subset_left
  have he : euler (P \ q.primeFactors) * euler q.primeFactors ≤ euler P :=
    (mul_le_mul_of_nonneg_left hsmall
      (euler_pos (fun p hp => hP p (mem_sdiff.mp hp).1)).le).trans_eq hprod
  have hqR : 0 < (q:ℝ) := by exact_mod_cast hq
  have htR : 0 < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  apply (le_div_iff₀ htR).mpr
  rw [totient_euler q]
  nlinarith [mul_le_mul_of_nonneg_right he hqR.le]

lemma cutoff_euler_eq (x : ℝ) : euler (cutoffPrimes ⌊x⌋₊) = primeProduct x := by
  have hs : cutoffPrimes ⌊x⌋₊ = (Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
    ext p
    simp only [mem_cutoffPrimes,mem_filter,mem_Ioc]
    constructor
    · rintro ⟨hp,hle⟩
      exact ⟨⟨hp.pos,hle⟩,hp⟩
    · rintro ⟨⟨_,hle⟩,hp⟩
      exact ⟨hp,hle⟩
  unfold euler primeProduct
  rw [hs]
  simp only [one_div]

theorem prime_product_upper : ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
    ∀ x : ℝ, x₀ ≤ x → primeProduct x ≤ C / Real.log x := by
  obtain ⟨c,K,x₀,hc,hK,hx₀,h⟩ := prime_product_strong
  refine ⟨(K+1)*Real.exp (-Real.eulerMascheroniConstant),x₀,by positivity,hx₀,?_⟩
  intro x hx
  have hx1 : 1 < x := by linarith [hx₀.trans hx]
  have hl := Real.log_pos hx1
  have hd : Real.exp (-c * Real.sqrt (Real.log x)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have := Real.sqrt_nonneg (Real.log x)
    nlinarith)
  have hh := (abs_le.mp (h x hx)).2
  have hu : primeProduct x / (Real.exp (-Real.eulerMascheroniConstant) / Real.log x) ≤ K+1 := by
    nlinarith [mul_le_mul_of_nonneg_left hd hK.le]
  have hmul := (div_le_iff₀ (div_pos (Real.exp_pos _) hl)).mp hu
  simpa only [mul_div_assoc] using hmul

theorem reduced_product_upper : ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
    ∀ x : ℝ, x₀ ≤ x → ∀ q : ℕ, 0 < q →
      euler (reducedPrimes ⌊x⌋₊ q) ≤ C * ((q : ℝ) / q.totient) / Real.log x := by
  obtain ⟨C,x₀,hC,hx₀,h⟩ := prime_product_upper
  refine ⟨C,x₀,hC,hx₀,?_⟩
  intro x hx q hq
  have ht0 : 0 ≤ (q.totient : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ euler (cutoffPrimes ⌊x⌋₊) * q / q.totient :=
      euler_omissions_le _ q hq (fun p hp => (mem_cutoffPrimes.mp hp).1)
    _ = primeProduct x * q / q.totient := by rw [cutoff_euler_eq]
    _ ≤ (C / Real.log x) * q / q.totient := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (h x hx) (Nat.cast_nonneg _)) ht0
    _ = _ := by ring

end ErdosPrimeInputs.PrimeProductOmissions

end

end Erdos970

end OAI
