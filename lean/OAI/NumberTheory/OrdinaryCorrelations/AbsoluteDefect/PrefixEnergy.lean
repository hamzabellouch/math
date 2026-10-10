import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.NormPhase
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BoxAddWidth

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

namespace OrdinaryInitialWidth
open OrdinaryCorrelations OrdinaryLocalAdditive OrdinarySharpWindow Finset Filter MeasureTheory

noncomputable def prefixEnergy (a : ℕ→ℂ) (D : ℝ) (N : ℕ) : ℝ :=
  ∫ x : ℝ, ‖sharpWindow (Ioc 0 N) a (fun n => (n:ℝ)) D x‖

lemma prefixEnergy_mass {a : ℕ→ℂ} (ha : OneBounded a) {D : ℝ} (hD : 0 ≤ D) (N : ℕ) :
    prefixEnergy a D N ≤ D*N := by
  have hc : (∑ n ∈ Ioc 0 N, ‖a n‖) ≤ (N:ℝ) := by
    calc
      _ ≤ ∑ _n ∈ Ioc 0 N, (1:ℝ) := sum_le_sum (fun n _ => ha n)
      _ = _ := by simp
  exact (sharpWindow_l1_mass _ _ _ hD).trans (mul_le_mul_of_nonneg_left hc hD)

lemma prefixEnergy_double (a : ℕ→ℂ) (D : ℝ) (N : ℕ) :
    prefixEnergy a D (2*N) ≤ prefixEnergy a D N +
      ∫ x : ℝ, ‖sharpWindow (Ioc N (2*N)) a (fun n => (n:ℝ)) D x‖ := by
  have he (x : ℝ) : sharpWindow (Ioc 0 (2*N)) a (fun n => (n:ℝ)) D x =
      sharpWindow (Ioc 0 N) a (fun n => (n:ℝ)) D x +
      sharpWindow (Ioc N (2*N)) a (fun n => (n:ℝ)) D x := by
    unfold sharpWindow
    rw [←Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le N) (by omega : N ≤ 2*N),sum_union]
    simp
  have h1 := (sharpWindow_integrable (Ioc 0 N) a (fun n=>(n:ℝ)) D).norm
  have h2 := (sharpWindow_integrable (Ioc N (2*N)) a (fun n=>(n:ℝ)) D).norm
  unfold prefixEnergy
  calc
    _ ≤ ∫ x:ℝ, ‖sharpWindow (Ioc 0 N) a (fun n=>(n:ℝ)) D x‖ +
        ‖sharpWindow (Ioc N (2*N)) a (fun n=>(n:ℝ)) D x‖ := by
      apply integral_mono (sharpWindow_integrable _ _ _ _).norm (h1.add h2)
      intro x
      dsimp only
      rw [he]
      exact norm_add_le _ _
    _ = _ := integral_add h1 h2

lemma prefixEnergy_power_bound {a : ℕ→ℂ} (ha : OneBounded a)
    {D ε : ℝ} (hD : 0 ≤ D) (hε : 0 ≤ ε) (K : ℕ)
    (h : ∀ N : ℕ, K ≤ N →
      (∫x:ℝ, ‖sharpWindow (Ioc N (2*N)) a (fun n=>(n:ℝ)) D x‖) ≤ ε*D*N) :
    ∀ k : ℕ, prefixEnergy a D (2^k) ≤ (2*(K+1):ℝ)*D + ε*D*(2:ℝ)^k := by
  intro k
  induction k with
  | zero =>
      simp only [pow_zero]
      have ht := prefixEnergy_mass ha hD 1
      norm_num at ht
      nlinarith [mul_nonneg hD hε]
  | succ k ih =>
      by_cases hk : K ≤ 2^k
      · have hs := h (2^k) hk
        have ht := (prefixEnergy_double a D (2^k)).trans (add_le_add ih hs)
        have he : (2:ℕ)^(k+1)=2*2^k := by rw [pow_succ,Nat.mul_comm]
        rw [he]
        push_cast at ht
        rw [pow_succ]
        nlinarith only [ht]
      · have hk' : (2^(k+1):ℕ) ≤ 2*K := by
          rw [pow_succ];omega
        have ht := prefixEnergy_mass ha hD (2^(k+1))
        have hk'' : ((2^(k+1):ℕ):ℝ) ≤ 2*(K:ℝ) := by exact_mod_cast hk'
        have hmul := mul_le_mul_of_nonneg_left hk'' hD
        have hn := mul_nonneg (mul_nonneg hε hD) (pow_nonneg (by norm_num : (0:ℝ)≤2) (k+1))
        nlinarith

end OrdinaryInitialWidth

end

end OAI
