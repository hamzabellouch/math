import OAI.NumberTheory.JointDickman.Analysis.CharacterMiddleSum
import OAI.NumberTheory.JointDickman.Analysis.CharacterFrequencyScales

namespace OAI

/-! # An arbitrarily small logarithmic bound for fixed-character L-functions -/
namespace JointDickman
open Complex Filter Finset
open scoped Topology

theorem character_LFunction_logarithmic_bound {B : ℝ} (hB : 2 ≤ B)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ t σ : ℝ,
      |t| = T → 1 ≤ σ → σ ≤ 2 →
      ‖χ.LFunction ((σ:ℂ)+(t:ℂ)*I)‖ ≤ (1/B)*Real.log T+C := by
  obtain ⟨A,δ,U₀,hA,hδ,hU₀,hmid⟩ := character_middle_sum_bound B (by linarith)
  have hden : 0 < 1-(2:ℝ)^(-δ) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  let C : ℝ := 1+Real.log 2+4*((q:ℝ)+1)+((q:ℝ)*A)/(1-(2:ℝ)^(-δ))
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [character_frequency_scales hB U₀] with T hscale
  intro t σ ht hσ hσ2
  obtain ⟨N,K,hN,hNU,hNT,hlog,hcover,hcap,hlo,hhi⟩ := hscale
  let M : ℕ := 2^K*N
  have hNM : N ≤ M := by
    dsimp [M]
    nlinarith [one_le_pow₀ (by norm_num : (1:ℕ) ≤ 2) (n := K)]
  have hM : 1 ≤ M := hN.trans hNM
  have hMR : (M:ℝ) = (2:ℝ)^K*(N:ℝ) := by simp [M]
  have hMI : (M:ℤ) = (2:ℤ)^K*(N:ℤ) := by simp [M]
  have hN0 : (0:ℝ) < N := by exact_mod_cast (zero_lt_one.trans_le hN)
  have hfreq : |t/(2*Real.pi)| = T/(2*Real.pi) := by
    rw [abs_div,abs_of_pos (by positivity : 0 < 2*Real.pi),ht]
  have hsre : ((σ:ℂ)+(t:ℂ)*I).re = σ := by simp
  have hsim : ((σ:ℂ)+(t:ℂ)*I).im = t := by simp
  have htail := character_LFunction_cutoff_bound χ hχ ((σ:ℂ)+(t:ℂ)*I)
    (by simpa only [hsre] using hσ) (by simpa only [hsre] using hσ2) M hM
    (by simpa only [hsim,ht,hMR] using hcover)
  have hmiddle := hmid q χ σ t (N:ℤ) K (by exact_mod_cast hNU) hσ
    (by simpa only [Int.cast_natCast,hfreq] using hlo)
    (by simpa only [Int.cast_natCast,hfreq] using hhi)
  have hpow : (N:ℝ)^(-δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast hN) (by linarith)
  have hmiddle' : ‖∑ n ∈ Ioc (N:ℤ) (M:ℤ),
      χ (n:ZMod q)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I))‖ ≤ ((q:ℝ)*A)/(1-(2:ℝ)^(-δ)) := by
    rw [hMI]
    exact hmiddle.trans (div_le_div_of_nonneg_right
      (mul_le_of_le_one_right (by positivity) hpow) hden.le)
  let f : ℤ → ℂ := fun n => χ (n:ZMod q)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I))
  have hsplit : (∑ n ∈ Icc 1 N, χ (n:ZMod q)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I)))+
      (∑ n ∈ Ioc (N:ℤ) (M:ℤ), f n) =
      ∑ n ∈ Icc 1 M, χ (n:ZMod q)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I)) := by
    have hh := sum_int_Ioc_consecutive f (a := 0) (b := N) (c := M)
      (by exact_mod_cast (Nat.zero_le N)) (by exact_mod_cast hNM)
    rw [int_Ioc_eq_Icc_succ 0, int_Ioc_eq_Icc_succ 0] at hh
    simp only [zero_add] at hh
    have heN := sum_nat_Icc_int_cast f 1 N
    have heM := sum_nat_Icc_int_cast f 1 M
    simp only [Nat.cast_one] at heN heM
    rw [←heN,←heM] at hh
    simpa [f] using hh
  have hhead := character_LFunction_head_bound χ ((σ:ℂ)+(t:ℂ)*I)
    (by simpa only [hsre] using hσ) N
  have hfull := norm_add_le
    (χ.LFunction ((σ:ℂ)+(t:ℂ)*I)-∑ n ∈ Icc 1 M, χ (n:ZMod q)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I)))
    (∑ n ∈ Icc 1 M, χ (n:ZMod q)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I)))
  rw [sub_add_cancel] at hfull
  have htail' : ‖χ.LFunction ((σ:ℂ)+(t:ℂ)*I) -
      ((∑ n ∈ Icc 1 N, χ (n:ZMod q)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I))) +
      ∑ n ∈ Ioc (N:ℤ) (M:ℤ), f n)‖ ≤ 4*((q:ℝ)+1) := by
    rw [hsplit]
    exact htail
  rw [←hsplit] at hfull
  have hsum := norm_add_le
    (∑ n ∈ Icc 1 N, χ (n:ZMod q)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I)))
    (∑ n ∈ Ioc (N:ℤ) (M:ℤ), f n)
  change ‖∑ n ∈ Ioc (N:ℤ) (M:ℤ), f n‖ ≤ _ at hmiddle'
  dsimp only [C]
  linarith

end JointDickman

end OAI
