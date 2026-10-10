import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.RichRegime
open scoped Real

theorem scalar_conditions (σ g N M K : ℝ)
    (hNhi : N ≤ Real.exp (3*σ/2+g))
    (hMlo : Real.exp (σ/2+19*g/20)/4 ≤ M)
    (hKhi : K ≤ 2*Real.exp (σ+17*g/15))
    (hg : g ≤ 2*σ)
    (hlarge : 64*1024^2 ≤ Real.exp (37*g/20))
    (hcap : 256 ≤ Real.exp (23*g/30))
    (hchar : 102 < Real.exp (9*σ/20)) :
    1024^2*N ≤ M^3 ∧ 8*K ≤ M^2 ∧
      51*Real.sqrt (N/M) < Real.exp σ := by
  have hM : 0 < M := lt_of_lt_of_le (by positivity) hMlo
  have hcube : (Real.exp (σ/2+19*g/20)/4)^3 ≤ M^3 :=
    pow_le_pow_left₀ (by positivity) hMlo 3
  have hsq : (Real.exp (σ/2+19*g/20)/4)^2 ≤ M^2 :=
    pow_le_pow_left₀ (by positivity) hMlo 2
  have he3 : Real.exp (3*σ/2+g)*Real.exp (37*g/20) = (Real.exp (σ/2+19*g/20))^3 := by
    rw [← Real.exp_add,← Real.exp_nat_mul]
    congr 1
    ring
  have he2 : Real.exp (σ+17*g/15)*Real.exp (23*g/30) = (Real.exp (σ/2+19*g/20))^2 := by
    rw [← Real.exp_add,← Real.exp_nat_mul]
    congr 1
    ring
  have hn3 := mul_le_mul_of_nonneg_left hlarge (Real.exp_pos (3*σ/2+g)).le
  have hk2 := mul_le_mul_of_nonneg_left hcap (Real.exp_pos (σ+17*g/15)).le
  rw [he3] at hn3
  rw [he2] at hk2
  refine ⟨?_,?_,?_⟩
  · nlinarith
  · nlinarith
  · have hratio : N/M ≤ 4*Real.exp (11*σ/10) := by
      apply (div_le_iff₀ hM).mpr
      have hs : Real.exp (3*σ/2+g) ≤
          Real.exp (11*σ/10)*Real.exp (σ/2+19*g/20) := by
        rw [← Real.exp_add, Real.exp_le_exp]
        linarith
      have ht := mul_le_mul_of_nonneg_left hMlo (show 0 ≤ 4*Real.exp (11*σ/10) by positivity)
      nlinarith
    have hsqrt : Real.sqrt (N/M) ≤ 2*Real.exp (11*σ/20) := by
      apply (Real.sqrt_le_iff).mpr
      refine ⟨by positivity,hratio.trans_eq ?_⟩
      rw [mul_pow,← Real.exp_nat_mul]
      norm_num
      ring
    have he : Real.exp (11*σ/20)*Real.exp (9*σ/20) = Real.exp σ := by
      rw [← Real.exp_add]
      congr 1
      ring
    have ht := mul_lt_mul_of_pos_left hchar (Real.exp_pos (11*σ/20))
    rw [he] at ht
    linarith

theorem source_substitution (σ g n' a : ℝ)
    (hn' : Real.exp (3*σ/2+g)/4 ≤ n')
    (ha : Real.exp (-g/20) ≤ a) :
    Real.exp (σ/2+19*g/20)/4 ≤ n'*a/Real.exp σ ∧
    (Real.exp (3*σ/2+g)) ^ (4/3:ℝ) / Real.exp σ * Real.exp (-g/5) =
      Real.exp (σ+17*g/15) := by
  have hn0 : 0 ≤ n' := le_trans (by positivity) hn'
  constructor
  · apply (le_div_iff₀ (Real.exp_pos σ)).mpr
    have hh := mul_le_mul hn' ha (by positivity) hn0
    apply le_trans _ hh
    have he : Real.exp (σ/2+19*g/20)*Real.exp σ =
        Real.exp (3*σ/2+g)*Real.exp (-g/20) := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    have he' : Real.exp (σ/2+19*g/20)/4*Real.exp σ =
        Real.exp (3*σ/2+g)/4*Real.exp (-g/20) := by nlinarith [he]
    exact he'.le
  · rw [← Real.exp_mul,← Real.exp_sub,← Real.exp_add]
    congr 1
    ring

theorem sufficiently_large_conditions (σ g N M K : ℝ)
    (hσ : 1000 ≤ σ) (hglo : 100000000 ≤ g) (hghi : g ≤ 2*σ)
    (hNhi : N ≤ Real.exp (3*σ/2+g))
    (hMlo : Real.exp (σ/2+19*g/20)/4 ≤ M)
    (hKhi : K ≤ 2*Real.exp (σ+17*g/15)) :
    2 ≤ M ∧ 1024^2*N ≤ M^3 ∧ 8*K ≤ M^2 ∧
      51*Real.sqrt (N/M) < Real.exp σ := by
  have hm := Real.add_one_le_exp (σ/2+19*g/20)
  refine ⟨by linarith,scalar_conditions σ g N M K hNhi hMlo hKhi hghi ?_ ?_ ?_⟩
  · linarith [Real.add_one_le_exp (37*g/20)]
  · linarith [Real.add_one_le_exp (23*g/30)]
  · linarith only [hσ, Real.add_one_le_exp (9*σ/20)]

end SharpRamseyFive.RichRegime

end OAI
