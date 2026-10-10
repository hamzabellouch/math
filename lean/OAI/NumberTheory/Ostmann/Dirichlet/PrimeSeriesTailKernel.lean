import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import OAI.NumberTheory.Ostmann.Dirichlet.PrimeSeriesDefinitions
import OAI.NumberTheory.Ostmann.Preliminaries.DivisorLog

namespace OAI

noncomputable section
namespace Ostmann.Dirichlet
open Ostmann.Preliminaries MeasureTheory
open scoped BigOperators

def primeSeriesTailKernel (σ : ℝ) (p : ℕ) (t : ℝ) : ℝ :=
  (Set.Ioi (p : ℝ)).indicator (fun u => σ * Real.log p * u ^ (-σ - 1)) t

lemma primeSeriesTailKernel_integrable {σ Q : ℝ} (hσ : 1 < σ) (hQ : 0 < Q) (p : ℕ) :
    IntegrableOn (primeSeriesTailKernel σ p) (Set.Ioi Q) := by
  have h := (integrableOn_Ioi_rpow_of_lt (by linarith : -σ - 1 < -1) hQ).const_mul
    (σ * Real.log p)
  exact h.indicator measurableSet_Ioi

lemma primeSeriesTailKernel_integral {σ Q : ℝ} (hσ : 1 < σ) {p : ℕ}
    (hp : p.Prime) (hQp : Q ≤ (p : ℝ)) :
    (∫ t in Set.Ioi Q, primeSeriesTailKernel σ p t) = ordinaryPrimeSeriesTerm σ p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hs0 : σ ≠ 0 := by linarith
  unfold primeSeriesTailKernel
  rw [setIntegral_indicator measurableSet_Ioi,
    Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi hQp), integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith : -σ - 1 < -1) hp0,
    show -σ - 1 + 1 = -σ by ring, Real.rpow_neg hp0.le]
  simp only [ordinaryPrimeSeriesTerm, hp, ite_true]
  field_simp

lemma primeSeriesTailKernel_sum_bound (P : Finset ℕ) {σ t : ℝ}
    (hσ : 0 ≤ σ) (ht : 0 < t) (hprime : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, primeSeriesTailKernel σ p t) ≤
      Real.log 4 * σ * t ^ (-σ) := by
  classical
  let S : Finset ℕ := P.filter (fun (p : ℕ) => (p : ℝ) < t)
  have hs : S ⊆ (⌊t⌋₊).primesLE := by
    intro p hp
    have hm := Finset.mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨Nat.le_floor hm.2.le, hprime p hm.1⟩
  have hlogs : (∑ p ∈ S, Real.log p) ≤ Real.log 4 * t := by
    have h1 : (∑ p ∈ S, Real.log p) ≤ ∑ p ∈ (⌊t⌋₊).primesLE, Real.log p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hs
      intro p hp _
      exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)
    have h2 := sum_log_primesLE_le ⌊t⌋₊
    have h3 := mul_le_mul_of_nonneg_left (Nat.floor_le ht.le)
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))
    exact h1.trans (h2.trans h3)
  have hid : (∑ p ∈ P, primeSeriesTailKernel σ p t) =
      σ * t ^ (-σ - 1) * (∑ p ∈ S, Real.log p) := by
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hpt : (p : ℝ) < t
    · simp only [primeSeriesTailKernel, Set.indicator, Set.mem_Ioi, hpt, ite_true]
      ring
    · simp only [primeSeriesTailKernel, Set.indicator, Set.mem_Ioi, hpt, ite_false]
  rw [hid]
  have hpow : t ^ (-σ - 1) * t = t ^ (-σ) := by
    conv_lhs => rhs; rw [← Real.rpow_one t]
    rw [← Real.rpow_add ht]
    congr 1
    ring
  calc
    _ ≤ σ * t ^ (-σ - 1) * (Real.log 4 * t) :=
      mul_le_mul_of_nonneg_left hlogs (mul_nonneg hσ (Real.rpow_nonneg ht.le _))
    _ = Real.log 4 * σ * (t ^ (-σ - 1) * t) := by ring
    _ = _ := by rw [hpow]

end Ostmann.Dirichlet

end

end OAI
