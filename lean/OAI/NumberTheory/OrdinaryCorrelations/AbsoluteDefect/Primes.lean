import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.InverseCubeSummable
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Kernel
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BoundaryBudget

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
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory

namespace OrdinaryCorrelations.SourcePrimeBoxSieve
open Classical Finset
open SourceBoxSieve SourceRoughSieveLocal SourceBonferroni

abbrev Primes (K : ℕ) := ↥((K+1).primesBelow)

instance prime_nonzero {K : ℕ} (p : Primes K) : NeZero p.val :=
  ⟨(Nat.prime_of_mem_primesBelow p.property).ne_zero⟩

lemma primes_coprime (K : ℕ) : Pairwise (Function.onFun Nat.Coprime (fun p : Primes K => p.val)) := by
  intro p q hpq
  apply (Nat.prime_of_mem_primesBelow p.property).coprime_iff_not_dvd.mpr
  intro hd
  have he := (Nat.prime_of_mem_primesBelow q.property).eq_one_or_self_of_dvd _ hd
  rcases he with h | h
  · exact (Nat.prime_of_mem_primesBelow p.property).ne_one h
  · exact hpq (Subtype.ext h)

lemma primes_two (K : ℕ) (p : Primes K) : 2 ≤ p.val :=
  (Nat.prime_of_mem_primesBelow p.property).two_le

lemma primes_le (K : ℕ) (p : Primes K) : p.val ≤ K := by
  have := (Nat.mem_primesBelow.mp p.property).1
  omega

lemma primes_eq_filter (K : ℕ) : (K+1).primesBelow = (Finset.Icc 0 K).filter Nat.Prime := by
  ext p
  simp only [Nat.mem_primesBelow,Finset.mem_filter,Finset.mem_Icc,Nat.zero_le,true_and]
  constructor
  · rintro ⟨h,hp⟩
    exact ⟨(by omega),hp⟩
  · rintro ⟨h,hp⟩
    exact ⟨(by omega),hp⟩

lemma local_sum_bound (K : ℕ) (hK : 2 ≤ K) :
    (∑ p : Primes K, badDensity p.val) ≤
      4*Real.log 4*(Real.log (Real.log (K:ℝ))-SourcePrimeReciprocal.primitive 2) := by
  calc
    _ ≤ ∑ p : Primes K, 4/(p.val:ℝ) := Finset.sum_le_sum (fun p _ => (badDensity_bounds (primes_two K p)).2.2.2)
    _ = 4*∑ p ∈ (K+1).primesBelow, (p:ℝ)⁻¹ := by
      simp only [div_eq_mul_inv,← Finset.mul_sum]
      rw [Finset.sum_coe_sort ((K+1).primesBelow) (fun p : ℕ => (p:ℝ)⁻¹)]
    _ ≤ 4*(Real.log 4*(Real.log (Real.log (K:ℝ))-SourcePrimeReciprocal.primitive 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      have h := SourcePrimeReciprocal.reciprocal_bound (b := (K:ℝ)) (by exact_mod_cast hK)
      simpa only [Nat.floor_natCast,← primes_eq_filter] using h
    _ = _ := by ring

lemma local_product_bound (K : ℕ) (hK : 1 ≤ K) :
    (∏ p : Primes K, (1-badDensity p.val)) ≤
      Real.exp (∑' n : ℕ, (n:ℝ)⁻¹^3) * (Real.log (K+1:ℕ))⁻¹^4 := by
  have he : (∏ p : Primes K, (1-badDensity p.val)) =
      ∏ p ∈ (K+1).primesBelow, (1-4/(p:ℝ)+6/(p:ℝ)^2-3/(p:ℝ)^3) := by
    calc
      _ = ∏ p : Primes K, (1-4/(p.val:ℝ)+6/(p.val:ℝ)^2-3/(p.val:ℝ)^3) := by
        apply Finset.prod_congr rfl
        intro p _
        rw [badDensity_formula]
        ring
      _ = _ := Finset.prod_coe_sort ((K+1).primesBelow) (fun p : ℕ => (1-4/(p:ℝ)+6/(p:ℝ)^2-3/(p:ℝ)^3))
  rw [he]
  exact SourceSieveEulerProduct.prime_four_product K hK

theorem prime_box_sieve (K : ℕ) (hK : 2 ≤ K) (a N : ℕ) (hN : 0 < N) (r : ℕ) :
    density (fun p : Primes K => p.val) a N ≤
      Real.exp (∑' n : ℕ, (n:ℝ)⁻¹^3) * (Real.log (K+1:ℕ))⁻¹^4 +
      Real.exp (8*Real.log 4*(Real.log (Real.log (K:ℝ))-SourcePrimeReciprocal.primitive 2)) /
        (2:ℝ)^(2*r+1) +
      3*(2*r+1:ℕ)*(((Fintype.card (Primes K):ℝ)+1)*K)^(2*r)/N := by
  have h := finite_box_sieve (fun p : Primes K => p.val) (primes_coprime K) (primes_two K) a N hN r
  apply h.trans
  apply _root_.add_le_add
  · apply _root_.add_le_add (local_product_bound K (by omega))
    calc
      _ ≤ Real.exp (2*∑ p : Primes K, badDensity p.val)/(2:ℝ)^(2*r+1) :=
        elementary_le_exp univ _ (fun p _ => (badDensity_bounds (primes_two K p)).1.le) _
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply Real.exp_le_exp.mpr
        have := local_sum_bound K hK
        linarith
  · exact boundary_budget (fun p : Primes K => p.val) (K:ℝ) (by exact_mod_cast (show 1 ≤ K by omega))
      (fun p => by exact_mod_cast primes_le K p) N hN (2*r)

end OrdinaryCorrelations.SourcePrimeBoxSieve

end

end OAI
