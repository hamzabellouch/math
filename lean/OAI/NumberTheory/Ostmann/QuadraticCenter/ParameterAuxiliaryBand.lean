import Mathlib.Analysis.SpecialFunctions.Log.Base
import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterAuxiliaryScale
import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterPrimeBand

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Ostmann.Preliminaries Filter
open scoped BigOperators

lemma dyadic_count_le_five (N : ℕ) {y : ℝ} (hy : 1 ≤ y)
    (hN : Real.log N ≤ 2 * y) : (Nat.log 2 N + 1 : ℕ) ≤ 5 * y := by
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlog := Real.natLog_le_logb N 2
  rw [Real.logb] at hlog
  have hm := (le_div_iff₀ (by linarith : 0 < Real.log 2)).mp hlog
  have hnonneg : (0 : ℝ) ≤ Nat.log 2 N := Nat.cast_nonneg _
  push_cast
  nlinarith

theorem eventually_actual_auxiliary_prime_block (d : Decomposition) :
    ∀ᶠ T : ℝ in atTop, ∃ (j : ℕ) (G : Finset ℕ),
      T ^ auxiliaryExponent / 2 ≤ Real.log (2 ^ j : ℕ) ∧
      Real.log (2 ^ j : ℕ) ≤ 2 * T ^ auxiliaryExponent ∧
      T ≤ (G.card : ℝ) ∧
      (∀ p ∈ G, BalancedResiduePrime d p ∧ 2 ^ j ≤ p ∧ p < 2 * 2 ^ j ∧
        T ^ auxiliaryExponent < Real.log p ∧ Real.log p ≤ 2 * T ^ auxiliaryExponent) := by
  classical
  filter_upwards [parameterX_tendsto.eventually (eventually_balanced_dyadic_prime_block d),
    eventually_auxiliary_size_conditions, eventually_auxiliary_band_cutoff] with T hselect hc hQ
  let y := T ^ auxiliaryExponent
  let X := parameterX T
  let Q := collisionScale 4 X
  let N := ⌊Real.exp (2 * y)⌋₊
  let P := boundedLogarithmicPrimeBand Q y
  have hy : 1 ≤ y := hc.2.1
  have hy0 : 0 < y := by linarith
  have hT : 0 < T := by linarith [hc.1]
  have hN : ∀ p ∈ P, p.val ≤ N := by
    intro p hp
    exact (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp).2).1).1
  obtain ⟨j, G, hj, hG, hgood, hcard⟩ := hselect P N hN
  have hmass : y / 2 ≤ boundedPrimeWeight P -
      3 * collisionConstant 4 * Real.log (Real.log (X : ℝ)) := by
    have hm := boundedLogarithmicPrimeBand_weight_lower Q
      (show Real.log 2 ≤ y by linarith [hc.2.2.1]) hQ
    linarith [hc.2.2.2.1]
  have hz : (0 : ℝ) < (2 ^ j : ℕ) := by positivity
  have hcard' : y / 2 * (2 ^ j : ℕ) ≤
      (Nat.log 2 N + 1 : ℕ) * Real.log (2 * (2 ^ j : ℕ)) * G.card :=
    (mul_le_mul_of_nonneg_right hmass hz.le).trans hcard
  have hne : G.Nonempty := by
    by_contra hn
    have he : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, Finset.card_empty, Nat.cast_zero, mul_zero] at hcard'
    exact (not_le_of_gt (mul_pos (by linarith) hz)) hcard'
  have hband : ∀ p ∈ G, y < Real.log p ∧ Real.log p ≤ 2 * y := by
    intro p hp
    have hs : p ∈ logarithmicPrimeBand y := by
      rw [← boundedLogarithmicPrimeBand_image Q y hQ]
      exact hG hp
    exact (mem_logarithmicPrimeBand hy0.le).mp hs |>.2
  obtain ⟨p, hp⟩ := hne
  have hpprime := balancedResiduePrime_prime (hgood p hp).1
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  have hzp : ((2 ^ j : ℕ) : ℝ) ≤ p := by exact_mod_cast (hgood p hp).2.1
  have hpz : (p : ℝ) ≤ 2 * (2 ^ j : ℕ) := by exact_mod_cast (hgood p hp).2.2.le
  have hlogzu : Real.log (2 ^ j : ℕ) ≤ 2 * y :=
    (Real.log_le_log hz hzp).trans (hband p hp).2
  have hlogzl : y / 2 ≤ Real.log (2 ^ j : ℕ) := by
    have he := Real.log_le_log hpR hpz
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hz.ne'] at he
    linarith [(hband p hp).1, hc.2.2.1]
  have hlog2z : Real.log (2 * (2 ^ j : ℕ)) ≤ 3 * T := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hz.ne']
    have hyT : y ≤ T := auxiliary_power_le_self hc.1
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith
  have hlog2z0 : 0 ≤ Real.log (2 * (2 ^ j : ℕ)) := by
    apply Real.log_nonneg
    have hz1 : (1 : ℝ) ≤ (2 ^ j : ℕ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero j (by decide : (2 : ℕ) ≠ 0)))
    linarith
  have hlogN : Real.log N ≤ 2 * y := by
    exact (log_floor_exp_bounds (show Real.log 2 ≤ 2 * y by linarith [hc.2.2.1])).2.2
  have hncount := dyadic_count_le_five N hy hlogN
  have hscale : (2 ^ j : ℕ) ≤ 10 * Real.log (2 * (2 ^ j : ℕ)) * G.card := by
    have hm := mul_le_mul_of_nonneg_right hncount
      (mul_nonneg hlog2z0 (Nat.cast_nonneg G.card))
    nlinarith
  have hexp : Real.exp (y / 2) ≤ (2 ^ j : ℕ) := (Real.le_log_iff_exp_le hz).mp hlogzl
  have hnum : T ≤ (G.card : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hlog2z (Nat.cast_nonneg G.card)
    have hgrow : 30 * T ^ 2 ≤ Real.exp (y / 2) := hc.2.2.2.2
    nlinarith
  refine ⟨j, G, hlogzl, hlogzu, hnum, ?_⟩
  intro q hq
  exact ⟨(hgood q hq).1, (hgood q hq).2.1, (hgood q hq).2.2, hband q hq⟩

end Ostmann.QuadraticCenter

end

end OAI
