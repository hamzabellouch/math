import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Structure.SumLogPrimeFactors

namespace OAI

namespace SiegelZeros
open scoped _root_.SiegelZeros

section

namespace WeightedTorusJets
open ArithmeticFunction DirichletCharacter
open scoped LSeries.notation BigOperators ComplexOrder
theorem norm_logDeriv_LFunction_le_neg_logDeriv_zeta {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    ‖deriv (LFunction χ) s / LFunction χ s‖ ≤
      (-deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ)).re := by
  have htw := LSeriesSummable_twist_vonMangoldt χ hs
  have hΛ := LSeriesSummable_vonMangoldt (show 1 < (s.re : ℂ).re from hs)
  calc
    ‖deriv (LFunction χ) s / LFunction χ s‖ = ‖LSeries (↗χ * ↗Λ) s‖ := by
      rw [LSeries_twist_vonMangoldt_eq χ hs,
        deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs]
      simp [neg_div]
    _ ≤ ∑' n, ‖LSeries.term (↗χ * ↗Λ) s n‖ := norm_tsum_le_tsum_norm htw.norm
    _ ≤ ∑' n, ‖LSeries.term ↗Λ (s.re : ℂ) n‖ := by
      apply htw.norm.tsum_le_tsum _ hΛ.norm
      intro n
      have hcoeff : ‖(↗χ * ↗Λ) n‖ ≤ ‖(↗Λ n : ℂ)‖ := by
        simpa using mul_le_of_le_one_left (norm_nonneg (vonMangoldt n : ℂ))
          (χ.norm_le_one (n : ZMod q))
      simpa only [LSeries.norm_term_eq, Complex.ofReal_re] using
        (LSeries.norm_term_le (f := ↗χ * ↗Λ) (g := ↗Λ) (n := n) s hcoeff)
    _ = (LSeries ↗Λ (s.re : ℂ)).re := by
      rw [LSeries, Complex.re_tsum hΛ]
      apply tsum_congr
      intro n
      have hn : 0 ≤ LSeries.term ↗Λ (s.re : ℂ) n :=
        LSeries.term_nonneg (by exact_mod_cast (vonMangoldt_nonneg (n := n))) s.re
      simpa using congrArg Complex.re (RCLike.norm_of_nonneg' hn)
    _ = (-deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ)).re :=
      congrArg Complex.re (LSeries_vonMangoldt_eq_deriv_riemannZeta_div (show 1 < (s.re : ℂ).re from hs))

end WeightedTorusJets

namespace WeightedTorusJets

open _root_.SiegelZeros.Complex DirichletCharacter _root_.SiegelZeros.Complex.Hadamard

theorem exists_upper_bound_completedL_logDeriv :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ s : ℝ, 1 < s → s ≤ 2 →
      (logDeriv (conductorCompletedL χ) (s : ℂ)).re ≤
        1 / (s - 1) + K * Real.log q := by
  obtain ⟨Kg, hKg, hg⟩ := exists_upper_bound_conductor_gammaFactor_logDeriv
  obtain ⟨Cz, hCz, hz⟩ := exists_upper_bound_zeta_logDeriv_re
  refine ⟨Kg + Cz, by positivity, ?_⟩
  intro q _ hq χ hχ s hs hs2
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : 1 < Real.log q :=
    (Real.lt_log_iff_exp_lt (by linarith)).mpr (Real.exp_one_lt_three.trans_le hqR)
  have hnorm := norm_logDeriv_LFunction_le_neg_logDeriv_zeta χ
    (s := (s : ℂ)) (by simpa using hs)
  have hL : (logDeriv (LFunction χ) (s : ℂ)).re ≤
      (-logDeriv riemannZeta (s : ℂ)).re := by
    simpa only [logDeriv_apply, Complex.ofReal_re, neg_div] using
      (Complex.re_le_norm (deriv (LFunction χ) (s : ℂ) / LFunction χ (s : ℂ))).trans hnorm
  have hdecomp := congrArg Complex.re
    (conductorCompletedL_logDeriv_decomposition χ hχ (s := (s : ℂ))
      (by simpa using hs))
  rw [Complex.add_re] at hdecomp
  have hgamma := hg q hq χ s hs hs2
  have hzeta := hz s hs hs2
  nlinarith

theorem reciprocal_re_lower_of_near_one {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hzre : z.re ≤ 1) (hz : ‖z - 1‖ ≤ r) :
    1 / (6 * r) ≤ (1 / (((1 + 4 * r : ℝ) : ℂ) - z)).re := by
  have hre := (Complex.abs_re_le_norm (z - 1)).trans hz
  have him := (Complex.abs_im_le_norm (z - 1)).trans hz
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
    sub_zero] at hre him
  have hu : 4 * r ≤ 1 + 4 * r - z.re := by linarith
  have hu' : 1 + 4 * r - z.re ≤ 5 * r := by
    have := (abs_le.mp hre).1
    linarith
  have him2 : z.im ^ 2 ≤ r ^ 2 := by
    exact sq_le_sq.mpr (by simpa only [abs_of_pos hr] using him)
  have hden : 0 < (1 + 4 * r - z.re) ^ 2 + z.im ^ 2 := by
    nlinarith [sq_pos_of_pos (by linarith : 0 < 1 + 4 * r - z.re), sq_nonneg z.im]
  have hcomp : (1 + 4 * r - z.re) ^ 2 + z.im ^ 2 ≤
      6 * r * (1 + 4 * r - z.re) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu') (by linarith : 0 ≤ 1 + 4 * r - z.re)]
  have hdiv : 1 / (6 * r) ≤ (1 + 4 * r - z.re) /
      ((1 + 4 * r - z.re) ^ 2 + z.im ^ 2) :=
    (div_le_div_iff₀ (by positivity) hden).mpr (by nlinarith)
  simpa only [one_div, Complex.inv_re, Complex.normSq_apply, Complex.sub_re,
    Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub, neg_mul_neg,
    pow_two] using hdiv

theorem near_one_indices_eq_of_tsum_bound {ι : Type*} (z : ι → ℂ)
    {r B : ℝ} (hr : 0 < r) (hB : r * B < 1 / 12)
    (hre : ∀ i, (z i).re ≤ 1)
    (hsum : Summable (fun i => (1 / (((1 + 4 * r : ℝ) : ℂ) - z i)).re))
    (hbound : (∑' i, (1 / (((1 + 4 * r : ℝ) : ℂ) - z i)).re) ≤
      1 / (4 * r) + B)
    {i j : ι} (hi : ‖z i - 1‖ ≤ r) (hj : ‖z j - 1‖ ≤ r) : i = j := by
  classical
  by_contra hij
  have hnonneg : ∀ k, 0 ≤ (1 / (((1 + 4 * r : ℝ) : ℂ) - z k)).re := by
    intro k
    simp only [one_div, Complex.inv_re, Complex.sub_re, Complex.ofReal_re]
    exact div_nonneg (by have := hre k; linarith) (Complex.normSq_nonneg _)
  have htwo := hsum.sum_le_tsum {i, j} (fun k _ => hnonneg k)
  simp only [Finset.sum_pair hij] at htwo
  have hi' := reciprocal_re_lower_of_near_one hr (hre i) hi
  have hj' := reciprocal_re_lower_of_near_one hr (hre j) hj
  have hle : 2 / (6 * r) ≤ 1 / (4 * r) + B := by
    rw [show 2 / (6 * r) = 1 / (6 * r) + 1 / (6 * r) by ring]
    linarith
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hcalc : r * (2 / (6 * r)) = 1 / 3 := by field_simp; ring
  have hcalc' : r * (1 / (4 * r) + B) = 1 / 4 + r * B := by
    field_simp
  have hmul := mul_le_mul_of_nonneg_left hle hr.le
  rw [hcalc, hcalc'] at hmul
  linarith

theorem exists_near_one_divisor_indices_unique :
    ∃ c : ℝ, 0 < c ∧ c < 1 / 4 ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 → χ.IsQuadratic →
      ∀ i j : divisorZeroIndex₀ (conductorCompletedL χ) Set.univ,
      ‖divisorZeroIndex₀Val i - 1‖ ≤ c / Real.log q →
      ‖divisorZeroIndex₀Val j - 1‖ ≤ c / Real.log q → i = j := by
  obtain ⟨K, hK, hupper⟩ := exists_upper_bound_completedL_logDeriv
  let c : ℝ := 1 / (24 * (K + 1))
  have hc : 0 < c := by dsimp [c]; positivity
  have hc4 : c < 1 / 4 := by
    dsimp [c]
    apply (div_lt_iff₀ (by positivity)).mpr
    linarith
  refine ⟨c, hc, hc4, ?_⟩
  intro q _ hq χ hprim hχ hquad i j hi hj
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : 1 < Real.log q :=
    (Real.lt_log_iff_exp_lt (by linarith)).mpr (Real.exp_one_lt_three.trans_le hqR)
  let r : ℝ := c / Real.log q
  have hr : 0 < r := div_pos hc (by linarith)
  have hr4 : r < 1 / 4 := by
    apply lt_trans (b := c)
    · exact (div_lt_self hc hlogq)
    · exact hc4
  have hKc : c * K < 1 / 12 := by
    dsimp [c]
    rw [div_mul_eq_mul_div, (div_lt_iff₀ (by positivity))]
    nlinarith
  have hBr : r * (K * Real.log q) < 1 / 12 := by
    have heq : r * (K * Real.log q) = c * K := by
      dsimp [r]
      field_simp
    rwa [heq]
  have hs : 1 < 1 + 4 * r := by linarith
  have hs2 : 1 + 4 * r ≤ 2 := by linarith
  apply near_one_indices_eq_of_tsum_bound divisorZeroIndex₀Val hr hBr
    (fun k => (conductorCompletedL_divisorIndex_re_mem_Ioo χ hprim hχ k).2.le)
    (conductorCompletedL_zero_sum_absolutely_summable χ hprim hχ hs).of_abs _ hi hj
  rw [← real_logDeriv_conductorCompletedL_eq_divisor_tsum_source χ hprim hχ hquad hs]
  simpa only [add_sub_cancel_left] using hupper q hq χ hχ (1 + 4 * r) hs hs2

theorem analyticOrderAt_eq_one_of_divisor_indices_unique {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfne : f ≠ 0) {z : ℂ} (hz0 : z ≠ 0)
    (hz : f z = 0)
    (hunique : ∀ i j : divisorZeroIndex₀ f Set.univ,
      divisorZeroIndex₀Val i = z → divisorZeroIndex₀Val j = z → i = j) :
    analyticOrderAt f z = 1 := by
  have htop : analyticOrderAt f z ≠ ⊤ := by
    exact fun h => hfne ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z hf.analyticAt).mp h)
  have hpos : 0 < analyticOrderNatAt f z := by
    rw [Nat.pos_iff_ne_zero, analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero, not_or]
    exact ⟨(hf.analyticAt z).analyticOrderAt_ne_zero.mpr hz, htop⟩
  have hnat : analyticOrderNatAt f z = 1 := by
    by_contra hn
    have htwo : 1 < analyticOrderNatAt f z := by omega
    let i : divisorZeroIndex₀ f Set.univ := ⟨⟨z, ⟨0, by
      rw [RealCharacterAnalysis.toNat_divisor_eq_analyticOrderNatAt hf]
      exact hpos⟩⟩, hz0⟩
    let j : divisorZeroIndex₀ f Set.univ := ⟨⟨z, ⟨1, by
      rw [RealCharacterAnalysis.toNat_divisor_eq_analyticOrderNatAt hf]
      exact htwo⟩⟩, hz0⟩
    have heq := hunique i j rfl rfl
    have : (0 : ℕ) = 1 := congrArg (fun p => p.val.snd.val) heq
    omega
  rw [← Nat.cast_analyticOrderNatAt htop, hnat]
  rfl

end WeightedTorusJets

namespace WeightedTorusJets

open _root_.SiegelZeros.Complex DirichletCharacter _root_.SiegelZeros.Complex.Hadamard
open scoped ComplexConjugate

theorem exists_classical_near_one_zero_unique_real_simple :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) (hq : 3 ≤ q),
      let _ : NeZero q := ⟨by omega⟩
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
      (∀ a : ZMod q, (χ a).im = 0) → ∀ z : ℂ,
      ‖z - 1‖ ≤ c / Real.log q → LFunction χ z = 0 →
      z.im = 0 ∧ analyticOrderAt (LFunction χ) z = 1 ∧
        ∀ w : ℂ, ‖w - 1‖ ≤ c / Real.log q → LFunction χ w = 0 → w = z := by
  obtain ⟨c, hc, hc4, hindex_unique⟩ := exists_near_one_divisor_indices_unique
  refine ⟨c, hc, ?_⟩
  intro q hq _ χ hprim hχ hreal z hzdisk hz
  have hquad := (RealCharacterAnalysis.real_values_iff_quadratic χ).mp hreal
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : 1 < Real.log q :=
    (Real.lt_log_iff_exp_lt (by linarith)).mpr (Real.exp_one_lt_three.trans_le hqR)
  have hrad : c / Real.log q < 1 / 4 := (div_lt_self hc hlogq).trans hc4
  have hpos : ∀ w : ℂ, ‖w - 1‖ ≤ c / Real.log q → 0 < w.re := by
    intro w hw
    have hre := (Complex.abs_re_le_norm (w - 1)).trans hw
    simp only [Complex.sub_re, Complex.one_re] at hre
    have := (abs_le.mp hre).1
    linarith
  have hf := differentiable_conductorCompletedL χ hχ
  have hfne : conductorCompletedL χ ≠ 0 := by
    intro hzero
    have hzero₁ : conductorCompletedL χ 1 = 0 := congrFun hzero 1
    exact completedL_ne_zero_of_one_le_re χ hχ (s := 1) (by simp)
      ((conductorCompletedL_zero_iff χ 1).mp hzero₁)
  have hzero : ∀ w : ℂ, ‖w - 1‖ ≤ c / Real.log q → LFunction χ w = 0 →
      conductorCompletedL χ w = 0 := by
    intro w hw hwzero
    rw [conductorCompletedL_zero_iff,
      completedL_eq_mul_gammaFactor χ (hpos w hw), hwzero, zero_mul]
  have hindex : ∀ w : ℂ, ‖w - 1‖ ≤ c / Real.log q → LFunction χ w = 0 →
      ∃ p : divisorZeroIndex₀ (conductorCompletedL χ) Set.univ,
        divisorZeroIndex₀Val p = w := by
    intro w hw hwzero
    apply exists_divisorZeroIndex_val_eq_of_zero hf hfne _ (hzero w hw hwzero)
    intro hw0
    have := hpos w hw
    simp [hw0] at this
  obtain ⟨p, hp⟩ := hindex z hzdisk hz
  have hunique : ∀ w : ℂ, ‖w - 1‖ ≤ c / Real.log q → LFunction χ w = 0 → w = z := by
    intro w hw hwzero
    obtain ⟨p', hp'⟩ := hindex w hw hwzero
    have heq := hindex_unique q hq χ hprim hχ hquad p' p
      (by simpa only [hp'] using hw) (by simpa only [hp] using hzdisk)
    simpa only [hp', hp] using congrArg divisorZeroIndex₀Val heq
  have hconjzero : LFunction χ (conj z) = 0 := by
    have h := RealCharacterAnalysis.lFunction_conj χ hχ z
    simpa only [hquad.inv, hz, map_zero] using h
  have hconjdisk : ‖conj z - 1‖ ≤ c / Real.log q := by
    have heq : ‖conj z - 1‖ = ‖z - 1‖ := by
      simpa only [map_sub, map_one] using Complex.norm_conj (z - 1)
    rwa [heq]
  have hzim : z.im = 0 := Complex.conj_eq_iff_im.mp (hunique _ hconjdisk hconjzero)
  have horder : analyticOrderAt (conductorCompletedL χ) z = 1 := by
    refine analyticOrderAt_eq_one_of_divisor_indices_unique hf hfne ?_ (hzero z hzdisk hz) ?_
    · intro hz0
      have := hpos z hzdisk
      simp [hz0] at this
    · intro i j hi hj
      exact hindex_unique q hq χ hprim hχ hquad i j
        (by simpa only [hi] using hzdisk) (by simpa only [hj] using hzdisk)
  refine ⟨hzim, ?_, hunique⟩
  rwa [conductorCompletedL_analyticOrderAt_eq_LFunction χ hχ (hpos z hzdisk)] at horder

end WeightedTorusJets

end

end SiegelZeros

end OAI
