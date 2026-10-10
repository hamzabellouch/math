import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimitiveTwoLower

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
open Classical Finset Real Filter
open SourceRoughSieveLocal SourceBoxSieve SourceBonferroni

lemma source_product_small (L : ℝ) (hL : 0 < L) (K : ℕ) (hK : 1 ≤ K)
    (hKy : Real.exp (L^(99/100:ℝ)) ≤ (K+1:ℕ)) :
    (∏ p : Primes K, (1-badDensity p.val)) ≤
      Real.exp (∑' n : ℕ, (n:ℝ)⁻¹^3) * L^(-99/25:ℝ) := by
  have ht : 0 < L^(99/100:ℝ) := Real.rpow_pos_of_pos hL _
  have hl : L^(99/100:ℝ) ≤ Real.log (K+1:ℕ) := by
    have h := Real.log_le_log (Real.exp_pos _) hKy
    rwa [Real.log_exp] at h
  have he : ((L^(99/100:ℝ))⁻¹)^4 = L^(-99/25:ℝ) := by
    simp only [Real.rpow_def_of_pos hL]
    rw [← Real.exp_neg,← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  exact (local_product_bound K hK).trans
    (mul_le_mul_of_nonneg_left (by rw [← he]; exact pow_le_pow_left₀ (by positivity) (inv_anti₀ ht hl) 4)
      (Real.exp_pos _).le)

theorem eventual_rough_box : ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
    ∀ a N : ℕ, (1/2:ℝ)*Real.exp (L^(199/200:ℝ)) ≤ N →
      density (fun p : Primes ⌊Real.exp (L^(99/100:ℝ))⌋₊ => p.val) a N ≤
        C*L^(-99/25:ℝ) := by
  refine ⟨Real.exp (∑' n : ℕ, (n:ℝ)⁻¹^3)+2,by positivity,?_⟩
  filter_upwards [eventually_boundary_margin,Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ),
    eventually_ge_atTop (2:ℝ)] with L hm hlog hL
  intro a N hD
  let K := ⌊Real.exp (L^(99/100:ℝ))⌋₊
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hN : 0 < N := by
    have hp : 0 < (1/2:ℝ)*Real.exp (L^(199/200:ℝ)) := by positivity
    exact_mod_cast (lt_of_lt_of_le hp hD)
  have ht : 1 ≤ L^(99/100:ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hK : 2 ≤ K := by
    apply Nat.le_floor
    have h := Real.add_one_le_exp (L^(99/100:ℝ))
    norm_num
    linarith
  have hKy : (K:ℝ) ≤ Real.exp (L^(99/100:ℝ)) := Nat.floor_le (Real.exp_pos _).le
  have hKy' : Real.exp (L^(99/100:ℝ)) ≤ (K+1:ℕ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using (Nat.lt_floor_add_one (Real.exp (L^(99/100:ℝ)))).le
  have hprod := source_product_small L hLp K (by omega) hKy'
  have hsum := source_local_sum L (by linarith) hlog K hK hKy
  let r := ⌈500*Real.log L⌉₊
  have hk : 1000*Real.log L ≤ (2*r+1:ℕ) := by
    have hh := Nat.le_ceil (500*Real.log L)
    dsimp [r]
    push_cast
    linarith
  have htail := coarse_source_tail univ (fun p : Primes K => badDensity p.val)
    (fun p _ => (badDensity_bounds (primes_two K p)).1.le) L hL1 hsum (2*r+1) hk
  have hboundary := (boundary_budget (fun p : Primes K => p.val) (K:ℝ)
    (by exact_mod_cast (show 1≤K by omega)) (fun p => by exact_mod_cast primes_le K p)
    N hN (2*r)).trans (source_boundary_small L hL1 hlog hm K N hN hKy hD)
  have h := (finite_box_sieve (fun p : Primes K => p.val) (primes_coprime K)
    (primes_two K) a N hN r).trans (_root_.add_le_add (_root_.add_le_add hprod htail) hboundary)
  have herr : L^(-100:ℝ) ≤ L^(-99/25:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  change density (fun p : Primes K => p.val) a N ≤ _
  calc
    _ ≤ _ := h
    _ ≤ _ := by nlinarith

end OrdinaryCorrelations.SourcePrimeBoxSieve

end

end OAI
