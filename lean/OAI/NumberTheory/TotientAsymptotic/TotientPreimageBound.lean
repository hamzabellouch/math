import OAI.NumberTheory.TotientAsymptotic.TotientRatioLogLog

namespace OAI

/-! Concrete preimage bounds for the finite totient counting reductions. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma prime_le_shift_square {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p ≤ (p-1)^2 := by
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  have he : p-1+1=p := by omega
  nlinarith

lemma radical_le_twice_shift_product_square (n : ℕ) :
    (∏ p ∈ n.primeFactors,p) ≤ 2*(∏ p ∈ n.primeFactors,(p-1))^2 := by
  let E := n.primeFactors.erase 2
  have hprod : (∏ p ∈ E,p) ≤ (∏ p ∈ E,(p-1))^2 := by
    rw [← Finset.prod_pow]
    apply Finset.prod_le_prod
    intro p hp
    exact prime_le_shift_square (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp))
      (Finset.mem_erase.mp hp).1
  by_cases h2 : 2 ∈ n.primeFactors
  · have hrad := Finset.mul_prod_erase n.primeFactors (fun p : ℕ => p) h2
    have hshift := Finset.mul_prod_erase n.primeFactors (fun p : ℕ => p-1) h2
    norm_num only [Nat.reduceSub,one_mul] at hshift
    rw [← hrad,← hshift]
    exact Nat.mul_le_mul_left 2 hprod
  · have hE : E=n.primeFactors := Finset.erase_eq_of_notMem h2
    rw [hE] at hprod
    omega

lemma totient_preimage_quadratic {n : ℕ} (hn : 0 < n) : n ≤ 2*n.totient^2 := by
  let r := ∏ p ∈ n.primeFactors,p
  let s := ∏ p ∈ n.primeFactors,(p-1)
  have hr : 0 < r := Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  have hs : 0 < s := Finset.prod_pos (fun p hp => by have := (Nat.prime_of_mem_primeFactors hp).two_le; omega)
  obtain ⟨w,hw⟩ := n.prod_primeFactors_dvd
  change n=r*w at hw
  have hw0 : 0 < w := by nlinarith
  have he := Nat.totient_mul_prod_primeFactors n
  change n.totient*r=n*s at he
  have hφ : n.totient=w*s := by
    apply Nat.eq_of_mul_eq_mul_left hr
    rw [Nat.mul_comm r n.totient,he,hw]
    ring
  have hrad : r ≤ 2*s^2 := radical_le_twice_shift_product_square n
  rw [hφ,hw]
  nlinarith [Nat.mul_le_mul_right w hrad,show w ≤ w^2 by nlinarith]

end TotientAsymptotic

end

end OAI
