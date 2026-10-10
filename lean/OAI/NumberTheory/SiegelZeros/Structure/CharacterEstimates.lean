/-
Portions of this file have been adapted from an external source.
An attribution header has been generated because the source file did not contain a copyright header.
The applicable license information is stated below.
-/

import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport

namespace OAI

namespace SiegelZeros

open scoped BigOperators Topology

open scoped BigOperators

namespace WeightedTorusJets

section

open ArithmeticFunction DirichletCharacter

theorem combined_vonMangoldt_LSeries {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => (vonMangoldt n : ℂ) * (1 + χ n)) s =
      -deriv riemannZeta s / riemannZeta s -
        deriv (LFunction χ) s / LFunction χ s := by
  have heq : (fun n : ℕ => (vonMangoldt n : ℂ) * (1 + χ n)) =
      (fun n : ℕ => (vonMangoldt n : ℂ)) +
        ((fun n : ℕ => χ n) * (fun n : ℕ => (vonMangoldt n : ℂ))) := by
    funext n
    simp [mul_add, mul_comm]
  rw [heq, LSeries_add (LSeriesSummable_vonMangoldt hs)
    (LSeriesSummable_twist_vonMangoldt χ hs),
    LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
    LSeries_twist_vonMangoldt_eq χ hs,
    deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs]
  simp [sub_eq_add_neg, neg_div]

theorem combined_vonMangoldt_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ => (vonMangoldt n : ℂ) * (1 + χ n)) s := by
  convert (LSeriesSummable_vonMangoldt hs).add
    (LSeriesSummable_twist_vonMangoldt χ hs) using 1
  funext n
  simp [mul_add, mul_comm]

theorem re_combined_vonMangoldt_term {q : ℕ} (χ : DirichletCharacter ℂ q)
    (s : ℝ) (n : ℕ) :
    (LSeries.term (fun m : ℕ => (vonMangoldt m : ℂ) * (1 + χ m)) s n).re =
      vonMangoldt n * (1 + (χ n).re) / (n : ℝ) ^ s := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn]
    change (((vonMangoldt n : ℂ) * (1 + χ n)) /
      (((n : ℝ) : ℂ) ^ (s : ℂ))).re = _
    rw [← Complex.ofReal_cpow (Nat.cast_nonneg n)]
    simp [Complex.div_ofReal_re]

open scoped ComplexOrder in

theorem combined_vonMangoldt_term_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : ∀ a : ZMod q, (χ a).im = 0) (s : ℝ) (n : ℕ) :
    0 ≤ LSeries.term (fun m : ℕ => (vonMangoldt m : ℂ) * (1 + χ m)) s n := by
  apply LSeries.term_nonneg
  apply mul_nonneg
  · exact_mod_cast (vonMangoldt_nonneg (n := n))
  · rw [Complex.nonneg_iff]
    constructor
    · simp only [Complex.add_re, Complex.one_re]
      have hnorm := χ.norm_le_one (n : ZMod q)
      have hre := (abs_le.mp (Complex.abs_re_le_norm (χ n))).1
      linarith
    · simp [hχ]

theorem prime_sum_rpow_le_logDeriv {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℝ} (hs : 1 < s)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ χ p = 1) :
    2 * ∑ p ∈ P, Real.log p / (p : ℝ) ^ s ≤
      (-deriv riemannZeta (s : ℂ) / riemannZeta s -
        deriv (LFunction χ) (s : ℂ) / LFunction χ s).re := by
  have hsc : 1 < (s : ℂ).re := hs
  have hsum := combined_vonMangoldt_summable χ hsc
  have hnonneg (n : ℕ) :
      0 ≤ (LSeries.term (fun m : ℕ => (vonMangoldt m : ℂ) * (1 + χ m)) s n).re := by
    rw [re_combined_vonMangoldt_term]
    apply div_nonneg (mul_nonneg vonMangoldt_nonneg ?_) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    have hnorm := χ.norm_le_one (n : ZMod q)
    have hre := (abs_le.mp (Complex.abs_re_le_norm (χ n))).1
    linarith
  have hbound := (Complex.hasSum_re hsum.hasSum).summable.sum_le_tsum P
    (fun n _ => hnonneg n)
  rw [← Complex.re_tsum hsum] at hbound
  change _ ≤ (LSeries _ (s : ℂ)).re at hbound
  rw [combined_vonMangoldt_LSeries χ hsc] at hbound
  refine le_trans ?_ hbound
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  rw [re_combined_vonMangoldt_term, (hP p hp).2, Complex.one_re,
    vonMangoldt_apply_prime (hP p hp).1]
  ring_nf
  exact le_rfl

theorem log_rpow_compare {x X : ℝ} (hx : 1 ≤ x) (hxX : x ≤ X) (hX : 1 < X) :
    (2 / Real.exp 1) * (Real.log x / x) ≤
      2 * (Real.log x / x ^ (1 + 1 / Real.log X)) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hpow : x ^ (1 + 1 / Real.log X) ≤ x * Real.exp 1 := by
    rw [Real.rpow_add hx0, Real.rpow_one, one_div]
    exact mul_le_mul_of_nonneg_left
      ((Real.rpow_le_rpow hx0.le hxX (inv_nonneg.mpr hlogX.le)).trans
        Real.rpow_inv_log_le_exp_one) hx0.le
  calc
    (2 / Real.exp 1) * (Real.log x / x) = (2 * Real.log x) / (x * Real.exp 1) := by
      ring
    _ ≤ (2 * Real.log x) / x ^ (1 + 1 / Real.log X) :=
      div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hlogx)
        (Real.rpow_pos_of_pos hx0 _) hpow
    _ = 2 * (Real.log x / x ^ (1 + 1 / Real.log X)) := by ring

theorem positive_prime_mass_le_logDeriv_floor {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {X : ℝ} (hX : 1 < X) :
    (2 / Real.exp 1) *
        ∑ p ∈ (Nat.primesLE ⌊X⌋₊).filter (fun p : ℕ => χ p = 1),
          Real.log p / (p : ℝ) ≤
      (-deriv riemannZeta ((1 + 1 / Real.log X : ℝ) : ℂ) /
          riemannZeta ((1 + 1 / Real.log X : ℝ) : ℂ) -
        deriv (LFunction χ) ((1 + 1 / Real.log X : ℝ) : ℂ) /
          LFunction χ ((1 + 1 / Real.log X : ℝ) : ℂ)).re := by
  classical
  have hs : 1 < 1 + 1 / Real.log X :=
    lt_add_of_pos_right 1 (one_div_pos.mpr (Real.log_pos hX))
  have hprime : ∀ p ∈ (Nat.primesLE ⌊X⌋₊).filter (fun p : ℕ => χ p = 1),
      p.Prime ∧ χ p = 1 := by
    intro p hp
    obtain ⟨hp, hχp⟩ := Finset.mem_filter.mp hp
    exact ⟨Nat.prime_of_mem_primesLE hp, hχp⟩
  apply le_trans _ (prime_sum_rpow_le_logDeriv χ hs _ hprime)
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hp := (Finset.mem_filter.mp hp).1
  exact log_rpow_compare
    (Nat.one_le_cast.mpr (Nat.prime_of_mem_primesLE hp).one_le)
    ((Nat.le_floor_iff (by linarith)).mp (Nat.le_of_mem_primesLE hp)) hX

end

theorem reciprocal_gap_identity {s β : ℝ} (hs : 1 < s) (hβ : β < 1) :
    1 / (s - 1) - 1 / (s - β) = (1 - β) / ((s - 1) * (s - β)) := by
  have hs1 : s - 1 ≠ 0 := by linarith
  have hsβ : s - β ≠ 0 := by linarith
  field_simp
  ring

theorem reciprocal_gap_le {L β : ℝ} (hL : 0 < L) (hβ : β < 1) :
    1 / ((1 + 1 / L) - 1) - 1 / ((1 + 1 / L) - β) ≤ (1 - β) * L ^ 2 := by
  have hLi : 0 < 1 / L := one_div_pos.mpr hL
  have hs : 1 < 1 + 1 / L := by linarith
  rw [reciprocal_gap_identity hs hβ, add_sub_cancel_left]
  calc
    (1 - β) / ((1 / L) * (1 + 1 / L - β)) ≤
        (1 - β) / ((1 / L) * (1 / L)) := by
      apply div_le_div_of_nonneg_left (by linarith) (mul_pos hLi hLi)
      exact mul_le_mul_of_nonneg_left (by linarith) hLi.le
    _ = (1 - β) * L ^ 2 := by field_simp

theorem primebias_sampling_point {X : ℝ} (hX : 3 ≤ X) :
    1 < 1 + 1 / Real.log X ∧ 1 + 1 / Real.log X ≤ 2 := by
  have hlog : 1 < Real.log X := by
    apply (Real.lt_log_iff_exp_lt (by linarith)).mpr
    exact Real.exp_one_lt_three.trans_le hX
  constructor
  · have := one_div_pos.mpr (show 0 < Real.log X by linarith)
    linarith
  · have := (div_le_one (show 0 < Real.log X by linarith)).mpr hlog.le
    linarith

theorem positive_prime_mass_of_logDeriv_upper {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {X β K : ℝ} (hX : 1 < X) (hβ : β < 1)
    (hupper :
      (-deriv riemannZeta ((1 + 1 / Real.log X : ℝ) : ℂ) /
          riemannZeta ((1 + 1 / Real.log X : ℝ) : ℂ) -
        deriv (DirichletCharacter.LFunction χ) ((1 + 1 / Real.log X : ℝ) : ℂ) /
          DirichletCharacter.LFunction χ ((1 + 1 / Real.log X : ℝ) : ℂ)).re ≤
        K * Real.log q + 1 / ((1 + 1 / Real.log X) - 1) -
          1 / ((1 + 1 / Real.log X) - β)) :
    (∑ p ∈ Nat.primesLE ⌊X⌋₊ with χ ((p : ℕ) : ZMod q) = 1,
      Real.log p / p) ≤
        (Real.exp 1 / 2) * K * Real.log q +
          (Real.exp 1 / 2) * ((1 - β) * (Real.log X) ^ 2) := by
  have hgap := reciprocal_gap_le (Real.log_pos hX) hβ
  have hbound := (positive_prime_mass_le_logDeriv_floor χ hX).trans hupper
  have hbound' : (2 / Real.exp 1) *
      (∑ p ∈ Nat.primesLE ⌊X⌋₊ with χ ((p : ℕ) : ZMod q) = 1, Real.log p / p) ≤
        K * Real.log q + (1 - β) * (Real.log X) ^ 2 := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hbound'
    (show 0 ≤ Real.exp 1 / 2 by positivity)
  have he : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  field_simp [he] at hscaled
  nlinarith

end WeightedTorusJets
namespace RealCharacterAnalysis

open _root_.Complex Filter
open scoped Topology ComplexConjugate

theorem real_values_iff_quadratic {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    (∀ a : ZMod q, (χ a).im = 0) ↔ χ.IsQuadratic := by
  constructor
  · intro h
    have hc : star χ = χ := by
      ext a
      exact Complex.conj_eq_iff_im.mpr (h a)
    have hi : χ⁻¹ = χ := (MulChar.star_eq_inv χ).symm.trans hc
    apply MulChar.isQuadratic_iff_sq_eq_one.mpr
    calc
      χ ^ 2 = χ * χ := sq χ
      _ = χ * χ⁻¹ := congrArg (χ * ·) hi.symm
      _ = 1 := mul_inv_cancel χ
  · intro h a
    rcases h a with h | h | h <;> simp [h]

theorem apply_prime_eq_zero_iff {q p : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : p.Prime) : χ (p : ZMod q) = 0 ↔ p ∣ q := by
  rw [MulChar.apply_eq_zero_iff, ZMod.isUnit_prime_iff_not_dvd hp, not_not]

theorem lSeries_conj (f : ℕ → ℂ) (s : ℂ) :
    LSeries (fun n => conj (f n)) (conj s) = conj (LSeries f s) := by
  rw [LSeries, LSeries, Complex.conj_tsum]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · simp only [LSeries.term_of_ne_zero hn, map_div₀]
    rw [Complex.cpow_conj _ _ (by simp [Real.pi_ne_zero.symm])]
    simp

theorem lFunction_conj {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) :
    DirichletCharacter.LFunction χ⁻¹ (conj s) =
      conj (DirichletCharacter.LFunction χ s) := by
  have hi : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ
  have hf := DirichletCharacter.differentiable_LFunction hi
  have hg : Differentiable ℂ
      (conj ∘ DirichletCharacter.LFunction χ ∘ conj) := by
    intro z
    simpa using
      (DirichletCharacter.differentiable_LFunction hχ (conj z)).conj_conj
  have heq : DirichletCharacter.LFunction χ⁻¹ =
      conj ∘ DirichletCharacter.LFunction χ ∘ conj := by
    apply (hf.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
      (hg.differentiableOn.analyticOnNhd isOpen_univ)
    have hn : {z : ℂ | 1 < z.re} ∈ nhds (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
    filter_upwards [hn] with z hz
    simp only [Function.comp_apply]
    rw [DirichletCharacter.LFunction_eq_LSeries χ⁻¹ hz,
      DirichletCharacter.LFunction_eq_LSeries χ (by simpa using hz)]
    have hc : (fun n : ℕ => χ⁻¹ (n : ZMod q)) =
        (fun n : ℕ => conj (χ (n : ZMod q))) := by
      funext n
      simpa using (MulChar.star_apply' χ (n : ZMod q)).symm
    rw [hc, ← lSeries_conj, Complex.conj_conj]
  simpa using congrFun heq (conj s)

theorem lFunction_real {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hr : ∀ a : ZMod q, (χ a).im = 0) (s : ℝ) :
    (DirichletCharacter.LFunction χ (s : ℂ)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  rw [← lFunction_conj χ hχ, Complex.conj_ofReal,
    ((real_values_iff_quadratic χ).mp hr).inv]

end RealCharacterAnalysis

/-
Generated attribution header: the source file did not contain a copyright header.
The Mertens estimates in the following namespace are adapted from PrimeNumberTheoremAnd.IEANTN.Mertens.
Source: https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/c39a751132c88b6e8080b74c74023fd95b3d8be0/PrimeNumberTheoremAnd/IEANTN/Mertens.lean
License: Apache License 2.0.

This code has been modified.
-/

namespace WeightedTorusJets.Mertens

open _root_.Real _root_.Finset Filter Asymptotics Topology
open ArithmeticFunction hiding log

theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)

lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]

theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]

noncomputable abbrev E₁Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x

theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring

theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring

noncomputable abbrev E₁p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x

theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

noncomputable abbrev E₁ : ℝ := ∑' p : ℕ, if p.Prime then (log p) / (p*(p-1)) else 0

lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl

theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

theorem E₁.nonneg : E₁ ≥ 0 :=
  tsum_nonneg E₁.summand_nonneg

theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem prime_log_div_bounded_error :
    ∃ C > 0, ∀ x : ℝ, 1 ≤ x →
      |∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p - log x| ≤ C := by
  refine ⟨log 4 + 6 + E₁, by positivity [E₁.nonneg], fun x hx => ?_⟩
  rw [Nat.primesLE_eq_filter_Ioc_zero]
  change |E₁p x| ≤ log 4 + 6 + E₁
  have hlog : 0 ≤ log 4 := by positivity
  exact abs_le.mpr
    ⟨by linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx],
     by linarith [E₁Λ.le hx, E₁p.le_E₁Λ x, E₁.nonneg]⟩

theorem prime_log_div_isBigO :
    (fun x : ℝ => ∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p - log x)
      =O[atTop] (fun _ => (1 : ℝ)) := by
  obtain ⟨C, _, hC⟩ := prime_log_div_bounded_error
  apply IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  simpa only [Real.norm_eq_abs, norm_one, mul_one] using hC x hx

end WeightedTorusJets.Mertens

end SiegelZeros

end OAI
