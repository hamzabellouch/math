import OAI.NumberTheory.JointDickman.Analysis.CharacterMiddleSum
import OAI.NumberTheory.JointDickman.Analysis.ZetaCutoff
import OAI.NumberTheory.JointDickman.Analysis.CharacterFrequencyScales

namespace OAI

/-! # An arbitrarily small logarithmic bound for zeta away from its pole -/
namespace JointDickman
open Complex Filter Finset
open scoped Topology

theorem zeta_logarithmic_bound {B : ℝ} (hB : 2 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ t σ : ℝ,
      |t| = T → 1 < σ → σ ≤ 2 →
      ‖riemannZeta ((σ:ℂ)+(t:ℂ)*I)‖ ≤ (1/B)*Real.log T+C := by
  obtain ⟨A,δ,U₀,hA,hδ,hU₀,hmid⟩ := character_middle_sum_bound B (by linarith)
  have hden : 0 < 1-(2:ℝ)^(-δ) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  let C : ℝ := 1+Real.log 2+5+A/(1-(2:ℝ)^(-δ))
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  let χ : DirichletCharacter ℂ 1 := 1
  filter_upwards [character_frequency_scales hB U₀, eventually_ge_atTop (1 : ℝ)] with T hscale hT
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
  have htail₀ := zeta_cutoff_bound (s := (σ:ℂ)+(t:ℂ)*I)
    (by simpa only [hsre] using hσ) (by simpa only [hsre] using hσ2) hM
    (by simpa only [hsim, ht] using hT)
    (by simpa only [hsim,ht,hMR] using hcover)
  have hχn (n : ZMod 1) : χ n = 1 := by
    rw [show n = 1 from Subsingleton.elim _ _]; exact map_one χ
  have htail : ‖riemannZeta ((σ:ℂ)+(t:ℂ)*I) -
      ∑ n ∈ Icc 1 M, χ (n:ZMod 1)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I))‖ ≤ 5 := by
    simpa only [hχn, one_mul] using htail₀
  have hmiddle := hmid 1 χ σ t (N:ℤ) K (by exact_mod_cast hNU) hσ.le
    (by simpa only [Int.cast_natCast,hfreq] using hlo)
    (by simpa only [Int.cast_natCast,hfreq] using hhi)
  have hpow : (N:ℝ)^(-δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast hN) (by linarith)
  have hmiddle' : ‖∑ n ∈ Ioc (N:ℤ) (M:ℤ),
      χ (n:ZMod 1)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I))‖ ≤ A/(1-(2:ℝ)^(-δ)) := by
    rw [hMI]
    have hm : ‖∑ n ∈ Ioc (N:ℤ) ((2:ℤ)^K*(N:ℤ)),
        χ (n:ZMod 1)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I))‖ ≤ A*(N:ℝ)^(-δ)/(1-(2:ℝ)^(-δ)) := by
      simpa only [Nat.cast_one, Int.cast_natCast, one_mul] using hmiddle
    exact hm.trans (div_le_div_of_nonneg_right
      (mul_le_of_le_one_right (by positivity) hpow) hden.le)
  let f : ℤ → ℂ := fun n => χ (n:ZMod 1)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I))
  have hsplit : (∑ n ∈ Icc 1 N, χ (n:ZMod 1)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I)))+
      (∑ n ∈ Ioc (N:ℤ) (M:ℤ), f n) =
      ∑ n ∈ Icc 1 M, χ (n:ZMod 1)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I)) := by
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
    (by simpa only [hsre] using hσ.le) N
  have hfull := norm_add_le
    (riemannZeta ((σ:ℂ)+(t:ℂ)*I)-∑ n ∈ Icc 1 M, χ (n:ZMod 1)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I)))
    (∑ n ∈ Icc 1 M, χ (n:ZMod 1)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I)))
  rw [sub_add_cancel] at hfull
  have htail' : ‖riemannZeta ((σ:ℂ)+(t:ℂ)*I) -
      ((∑ n ∈ Icc 1 N, χ (n:ZMod 1)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I))) +
      ∑ n ∈ Ioc (N:ℤ) (M:ℤ), f n)‖ ≤ 5 := by
    rw [hsplit]
    exact htail
  rw [←hsplit] at hfull
  have hsum := norm_add_le
    (∑ n ∈ Icc 1 N, χ (n:ZMod 1)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I)))
    (∑ n ∈ Ioc (N:ℤ) (M:ℤ), f n)
  change ‖∑ n ∈ Ioc (N:ℤ) (M:ℤ), f n‖ ≤ _ at hmiddle'
  dsimp only [C]
  linarith

end JointDickman

end OAI
