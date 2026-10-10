import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinarySmoothRough

def smoothPart (S : Finset ℕ) (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => p ∈ S), p ^ n.factorization p

def roughPart (S : Finset ℕ) (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => p ∉ S), p ^ n.factorization p

lemma parts_mul (S : Finset ℕ) {n : ℕ} (hn : n ≠ 0) :
    smoothPart S n * roughPart S n = n := by
  rw [smoothPart, roughPart, prod_filter_mul_prod_filter_not]
  exact (Nat.prod_primeFactors_pow_factorization hn).symm

lemma parts_coprime (S : Finset ℕ) (n : ℕ) :
    (smoothPart S n).Coprime (roughPart S n) := by
  apply Nat.Coprime.prod_left
  intro p hp
  apply Nat.Coprime.prod_right
  intro q hq
  apply Nat.Coprime.pow
  apply (Nat.coprime_primes (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)
    (Nat.prime_of_mem_primeFactors (mem_filter.mp hq).1)).mpr
  intro he
  exact (mem_filter.mp hq).2 (he ▸ (mem_filter.mp hp).2)

lemma smoothPart_mem (S : Finset ℕ) (n : ℕ) :
    smoothPart S n ∈ Nat.factoredNumbers S := by
  unfold smoothPart
  have hbase (p : ℕ) (hp : p ∈ n.primeFactors.filter (fun p => p∈S)) :
      p^n.factorization p ∈ Nat.factoredNumbers S := by
    rw [Nat.mem_factoredNumbers']
    intro q hq hdiv
    have he := (Nat.prime_dvd_prime_iff_eq hq
      (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)).mp (hq.dvd_of_dvd_pow hdiv)
    exact he ▸ (mem_filter.mp hp).2
  generalize (n.primeFactors.filter (fun p => p∈S)) = A at hbase ⊢
  induction A using Finset.induction_on with
  | empty => simp [Nat.mem_factoredNumbers]
  | @insert p A hp hA =>
    rw [prod_insert hp]
    exact Nat.mul_mem_factoredNumbers (hbase p (mem_insert_self _ _))
      (hA (fun q hq => hbase q (mem_insert_of_mem hq)))

lemma roughPart_coprime_prime (S : Finset ℕ) (n : ℕ) {p : ℕ}
    (hp : Nat.Prime p) (hpin : p ∈ S) : (roughPart S n).Coprime p := by
  apply Nat.Coprime.prod_left
  intro q hq
  apply Nat.Coprime.pow_left
  apply (Nat.coprime_primes (Nat.prime_of_mem_primeFactors (mem_filter.mp hq).1) hp).mpr
  intro he
  exact (mem_filter.mp hq).2 (he ▸ hpin)

lemma roughPart_coprime_product (S : Finset ℕ) (n : ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) :
    (roughPart S n).Coprime (∏ p ∈ S, p) := by
  exact Nat.Coprime.prod_right (fun p hp => roughPart_coprime_prime S n (hS p hp) hp)

lemma smooth_coprime_rough {S : Finset ℕ} {m r : ℕ}
    (hm : m ∈ Nat.factoredNumbers S) (hr : ∀ p ∈ S, Nat.Prime p → ¬p∣r) :
    m.Coprime r := by
  apply Nat.coprime_of_dvd
  intro p hp hpm
  exact hr p ((Nat.mem_factoredNumbers'.mp hm) p hp hpm) hp

lemma factorization_unique {S : Finset ℕ} {m r m' r' : ℕ}
    (hm : m ∈ Nat.factoredNumbers S) (hm' : m' ∈ Nat.factoredNumbers S)
    (hr : ∀ p ∈ S, Nat.Prime p → ¬p∣r) (hr' : ∀ p ∈ S, Nat.Prime p → ¬p∣r')
    (he : m*r = m'*r') : m = m' := by
  have hmr' := smooth_coprime_rough hm hr'
  have hm'r := smooth_coprime_rough hm' hr
  apply Nat.dvd_antisymm
  · exact hmr'.dvd_of_dvd_mul_right (he ▸ dvd_mul_right m r)
  · exact hm'r.dvd_of_dvd_mul_right (he.symm ▸ dvd_mul_right m' r')

lemma parts_pos (S : Finset ℕ) {n : ℕ} (hn : 0<n) :
    0 < smoothPart S n ∧ 0 < roughPart S n := by
  have he := parts_mul S hn.ne'
  have hh : 0 < smoothPart S n * roughPart S n := by rw [he]; exact hn
  exact ⟨Nat.pos_of_ne_zero (by intro h; simp [h] at hh),
    Nat.pos_of_ne_zero (by intro h; simp [h] at hh)⟩

lemma multiplicative_factorization (f : ℕ → ℂ)
    (hm : ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → f (m*n)=f m*f n)
    (S : Finset ℕ) {n : ℕ} (hn : 0<n) :
    f n = f (smoothPart S n) * f (roughPart S n) := by
  have hp := parts_pos S hn
  calc
    f n = f (smoothPart S n * roughPart S n) := congrArg f (parts_mul S hn.ne').symm
    _ = _ := hm _ _ hp.1 hp.2 (parts_coprime S n)

end OrdinarySmoothRough

end

end OAI
