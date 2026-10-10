import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Event

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

namespace OrdinaryCorrelations.SourceBoxSieve
open Classical Finset
open SourceBonferroni SourceRoughSieveLocal
variable {ι : Type*} [Fintype ι]

lemma boundary_budget (s : ι → ℕ) (Y : ℝ) (hY : 1 ≤ Y)
    (hs : ∀ i, (s i : ℝ) ≤ Y) (N : ℕ) (hN : 0 < N) (R : ℕ) :
    (∑ k ∈ range (R+1), ∑ t ∈ (univ : Finset ι).powersetCard k,
      3 * ((∏ i ∈ t, s i : ℕ):ℝ) / N) ≤
      3 * (R+1:ℕ) * (((Fintype.card ι : ℝ)+1)*Y)^R / N := by
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hcard (k : ℕ) : ((univ : Finset ι).powersetCard k).card ≤ (Fintype.card ι+1)^k := by
    rw [Finset.card_powersetCard,Finset.card_univ]
    exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.le_succ _) _)
  have hbase : (1:ℝ) ≤ ((Fintype.card ι : ℝ)+1)*Y := by
    nlinarith [show (0:ℝ) ≤ (Fintype.card ι : ℝ) by positivity]
  have hk (k : ℕ) (hk : k ≤ R) :
      (∑ t ∈ (univ : Finset ι).powersetCard k, 3*((∏ i ∈ t,s i:ℕ):ℝ)/N) ≤
        3 * (((Fintype.card ι : ℝ)+1)*Y)^R / N := by
    calc
      _ ≤ ∑ _t ∈ (univ : Finset ι).powersetCard k, 3*Y^k/N := by
        apply Finset.sum_le_sum
        intro t ht
        have hp : ((∏ i ∈ t, s i : ℕ):ℝ) ≤ Y^k := by
          rw [Nat.cast_prod]
          calc
            _ ≤ ∏ _i ∈ t, Y := Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => hs i)
            _ = _ := by rw [Finset.prod_const,(Finset.mem_powersetCard.mp ht).2]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) hNp.le
      _ = (((univ : Finset ι).powersetCard k).card:ℝ) * (3*Y^k/N) := by simp
      _ ≤ ((Fintype.card ι+1:ℕ):ℝ)^k * (3*Y^k/N) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast hcard k
      _ = 3 * (((Fintype.card ι : ℝ)+1)*Y)^k / N := by
        simp only [Nat.cast_add,Nat.cast_one,mul_pow]
        ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase hk) (by norm_num)) hNp.le
  calc
    _ ≤ ∑ _k ∈ range (R+1), 3 * (((Fintype.card ι : ℝ)+1)*Y)^R/N :=
      Finset.sum_le_sum (fun k hk' => hk k (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk')))
    _ = _ := by simp; ring

theorem finite_box_sieve_source_scale (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hc : Pairwise (Function.onFun Nat.Coprime s)) (hs : ∀ i, 2 ≤ s i)
    (Y : ℝ) (hY : 1 ≤ Y) (hsY : ∀ i, (s i : ℝ) ≤ Y)
    (a N : ℕ) (hN : 0 < N) (L : ℝ) (hL : 1 ≤ L)
    (hS : (∑ i, badDensity (s i)) ≤ 5 * Real.log L) :
    density s a N ≤ (∏ i, (1-badDensity (s i))) + L^(-100:ℝ) +
      3*(2*⌈500 * Real.log L⌉₊+1:ℕ)*
        (((Fintype.card ι : ℝ)+1)*Y)^(2*⌈500 * Real.log L⌉₊)/N := by
  have hk : 1000*Real.log L ≤ ((2*⌈500*Real.log L⌉₊+1:ℕ):ℝ) := by
    have hh := Nat.le_ceil (500*Real.log L)
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    linarith
  have ht := elementary_source_scale univ (fun i => badDensity (s i))
    (fun i _ => (badDensity_bounds (hs i)).1.le) L hL hS _ hk
  exact (finite_box_sieve s hc hs a N hN _).trans
    (_root_.add_le_add (_root_.add_le_add le_rfl ht) (boundary_budget s Y hY hsY N hN _))

end OrdinaryCorrelations.SourceBoxSieve

end

end OAI
