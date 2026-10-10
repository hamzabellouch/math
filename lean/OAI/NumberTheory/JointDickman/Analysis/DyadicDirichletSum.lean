import OAI.NumberTheory.JointDickman.Analysis.CharacterDyadicSum

namespace OAI

/-! # Summing the decaying Dirichlet bounds over dyadic intervals -/
namespace JointDickman
open Finset

lemma sum_int_Ioc_consecutive (f : ℤ → ℂ) {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    (∑ n ∈ Ioc a b, f n)+(∑ n ∈ Ioc b c, f n) = ∑ n ∈ Ioc a c, f n := by
  rw [←Ioc_union_Ioc_eq_Ioc hab hbc, sum_union]
  apply disjoint_left.mpr
  intro n hn hn'
  have := mem_Ioc.mp hn
  have := mem_Ioc.mp hn'
  omega

lemma norm_dyadic_sum_bound (f : ℤ → ℂ) {N : ℤ} (hN : 0 < N)
    {D δ : ℝ} (hD : 0 ≤ D) (hδ : 0 < δ) (K : ℕ)
    (hblock : ∀ j < K,
      ‖∑ n ∈ Ioc ((2:ℤ)^j*N) ((2:ℤ)^(j+1)*N), f n‖ ≤
        D*(((2:ℝ)^j*(N:ℝ))^(-δ))) :
    ‖∑ n ∈ Ioc N ((2:ℤ)^K*N), f n‖ ≤ D*(N:ℝ)^(-δ)/(1-(2:ℝ)^(-δ)) := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  let r : ℝ := (2:ℝ)^(-δ)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have he (j : ℕ) : ((2:ℝ)^j*(N:ℝ))^(-δ) = (N:ℝ)^(-δ)*r^j := by
    rw [Real.mul_rpow (by positivity) hN'.le, Real.rpow_pow_comm (by norm_num)]
    exact mul_comm _ _
  have hb (J : ℕ) (hJK : J ≤ K) :
      ‖∑ n ∈ Ioc N ((2:ℤ)^J*N), f n‖ ≤ D*(N:ℝ)^(-δ)*(∑ j ∈ range J, r^j) := by
    induction J with
    | zero => simp
    | succ J ih =>
      have hpow : N ≤ (2:ℤ)^J*N := by nlinarith [one_le_pow₀ (by norm_num : (1:ℤ) ≤ 2) (n := J)]
      have hnext : (2:ℤ)^J*N ≤ (2:ℤ)^(J+1)*N := by rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0:ℤ) < 2) J]
      rw [←sum_int_Ioc_consecutive f hpow hnext]
      calc
        _ ≤ ‖∑ n ∈ Ioc N ((2:ℤ)^J*N), f n‖ + ‖∑ n ∈ Ioc ((2:ℤ)^J*N) ((2:ℤ)^(J+1)*N), f n‖ := norm_add_le _ _
        _ ≤ D*(N:ℝ)^(-δ)*(∑ j ∈ range J, r^j) + D*(((2:ℝ)^J*(N:ℝ))^(-δ)) :=
          add_le_add (ih (by omega)) (hblock J (by omega))
        _ = _ := by rw [he, sum_range_succ]; ring
  have hgeom : (∑ j ∈ range K, r^j) ≤ 1/(1-r) := by
    apply (le_div_iff₀ (sub_pos.mpr hr1)).mpr
    have hh := geom_sum_mul r K
    nlinarith [pow_nonneg hr0 K]
  calc
    _ ≤ D*(N:ℝ)^(-δ)*(∑ j ∈ range K, r^j) := hb K le_rfl
    _ ≤ D*(N:ℝ)^(-δ)*(1/(1-r)) := mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = _ := by dsimp [r]; ring

end JointDickman

end OAI
