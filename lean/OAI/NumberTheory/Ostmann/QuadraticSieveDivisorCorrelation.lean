import OAI.NumberTheory.Ostmann.QuadraticSieveGcdSeparationProduct
import OAI.NumberTheory.Ostmann.QuadraticSieveLeadingArithmetic

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped ArithmeticFunction.Moebius

theorem divisor_sum_eq_Icc (q L : ℕ) (hq : 0 < q) (hL : q ≤ L) (F : ℕ → ℂ) :
    (∑ d ∈ q.divisors, F d) = ∑ d ∈ Finset.Icc 1 L, if d ∣ q then F d else 0 := by
  classical
  have he : q.divisors = (Finset.Icc 1 L).filter (fun d => d ∣ q) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro hd
      exact ⟨⟨Nat.pos_of_mem_divisors hd, (Nat.le_of_dvd hq (Nat.mem_divisors.mp hd).1).trans hL⟩,
        (Nat.mem_divisors.mp hd).1⟩
    · intro hd
      exact Nat.mem_divisors.mpr ⟨hd.2,hq.ne'⟩
  rw [he, Finset.sum_filter]

theorem coprime_divisor_correlation_exchange (S T : Finset ℕ) (a b : ℕ → ℂ)
    (N : ℕ) (m : ℤ) (F : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) (hT : ∀ t ∈ T, 0 < t ∧ t ≤ N) :
    (∑ n ∈ S, ∑ t ∈ T, if Nat.Coprime n t then
      a n * b t * (jacobiSym m (n * t) : ℂ) * (∑ d ∈ (n * t).divisors, F d) else 0) =
      ∑ d ∈ Finset.Icc 1 (N ^ 2), F d * coprimeProductDivisorJacobiRow S T a b d m := by
  classical
  have heq (n : ℕ) (hn : n ∈ S) (t : ℕ) (ht : t ∈ T) :
      (if Nat.Coprime n t then
        a n * b t * (jacobiSym m (n * t) : ℂ) * (∑ d ∈ (n * t).divisors, F d) else 0) =
      ∑ d ∈ Finset.Icc 1 (N ^ 2), F d *
        (if Nat.Coprime n t ∧ d ∣ n * t then a n * b t * (jacobiSym m (n * t) : ℂ) else 0) := by
    rw [divisor_sum_eq_Icc (n * t) (N ^ 2) (Nat.mul_pos (hS n hn).1 (hT t ht).1)
      (by simpa only [pow_two] using Nat.mul_le_mul (hS n hn).2 (hT t ht).2)]
    by_cases hc : Nat.Coprime n t
    · rw [ite_eq_left hc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdiv : d ∣ n * t
      · rw [ite_eq_left hdiv, ite_eq_left (show Nat.Coprime n t ∧ d ∣ n * t from ⟨hc,hdiv⟩)]
        ring
      · rw [ite_eq_right hdiv, ite_eq_right (show ¬(Nat.Coprime n t ∧ d ∣ n * t) from fun h => hdiv h.2)]
        ring
    · simp [hc]
  have hleft := Finset.sum_congr rfl (fun n hn => Finset.sum_congr rfl (fun t ht => heq n hn t ht))
  rw [hleft]
  unfold coprimeProductDivisorJacobiRow
  simp only [Finset.mul_sum]
  calc
    _ = ∑ n ∈ S, ∑ d ∈ Finset.Icc 1 (N ^ 2), ∑ t ∈ T, F d *
        (if Nat.Coprime n t ∧ d ∣ n * t then a n * b t * (jacobiSym m (n * t) : ℂ) else 0) :=
      Finset.sum_congr rfl (fun n hn => Finset.sum_comm)
    _ = _ := Finset.sum_comm

theorem coprime_fixed_divisor_correlation_exchange (S T : Finset ℕ) (a b : ℕ → ℂ)
    (N R : ℕ) (m : ℤ) (F : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N ∧ Nat.Coprime R n)
    (hT : ∀ t ∈ T, 0 < t ∧ t ≤ N ∧ Nat.Coprime R t) :
    (∑ n ∈ S, ∑ t ∈ T, if Nat.Coprime n t then
      a n * b t * (jacobiSym m (n * t) : ℂ) *
        (∑ d ∈ (R * (n * t)).divisors, (μ d : ℂ) * F d) else 0) =
      ∑ r ∈ R.divisors, ∑ d ∈ Finset.Icc 1 (N ^ 2),
        (μ r : ℂ) * (μ d : ℂ) * F (r * d) * coprimeProductDivisorJacobiRow S T a b d m := by
  classical
  have heq (n : ℕ) (hn : n ∈ S) (t : ℕ) (ht : t ∈ T) :
      (∑ d ∈ (R * (n * t)).divisors, (μ d : ℂ) * F d) =
      ∑ d ∈ (n * t).divisors, ∑ r ∈ R.divisors, (μ r : ℂ) * (μ d : ℂ) * F (r * d) := by
    have hc := (hS n hn).2.2.mul_right (hT t ht).2.2
    rw [sum_divisors_coprime_product hc, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro r hr
    have hrd := hc.of_dvd (Nat.mem_divisors.mp hr).1 (Nat.mem_divisors.mp hd).1
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hrd, Int.cast_mul]
  have hleft := Finset.sum_congr rfl (fun n hn => Finset.sum_congr rfl (fun t ht =>
    congrArg (fun z : ℂ => if Nat.Coprime n t then a n * b t * (jacobiSym m (n * t) : ℂ) * z else 0)
      (heq n hn t ht)))
  rw [hleft]
  rw [coprime_divisor_correlation_exchange S T a b N m
    (fun d => ∑ r ∈ R.divisors, (μ r : ℂ) * (μ d : ℂ) * F (r * d))
    (fun n hn => ⟨(hS n hn).1,(hS n hn).2.1⟩)
    (fun t ht => ⟨(hT t ht).1,(hT t ht).2.1⟩)]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

end Ostmann.QuadraticSieve

end OAI
