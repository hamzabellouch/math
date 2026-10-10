import OAI.NumberTheory.JointDickman.Amplification.OutsideCandidateProduct
import OAI.NumberTheory.JointDickman.Amplification.ReciprocalTail

namespace OAI

/-! # Polynomial control of the conditional root-product error -/

namespace JointDickman
open Finset

theorem candidate_count_power_bound {B M N : ℕ} (hM : M ≤ B^2) (hN : N ≤ M^2*B^2) :
    N ≤ B^6 := by
  calc
    N ≤ M^2*B^2 := hN
    _ ≤ (B^2)^2*B^2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hM 2)
    _ = B^6 := by ring

theorem root_product_error_polynomial {B M N : ℕ} (hB : 1 ≤ B)
    (hM : M ≤ B^2) (hN : N ≤ M^2*B^2) {U D : ℝ}
    (hU : U ≤ 1/(auxiliaryCutoff B : ℝ))
    (hD : D ≤ (N : ℝ)*(2+5*(M : ℝ)+8*N)*(B : ℝ)/(Real.log 2*auxiliaryCutoff B)) :
    8*((N : ℝ)+(M : ℝ))^2*U+6*(N : ℝ)*D ≤
      212*(B : ℝ)^19/(auxiliaryCutoff B : ℝ) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hB)
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hP : (0 : ℝ) < auxiliaryCutoff B := by
    exact_mod_cast (pow_pos (lt_of_lt_of_le Nat.zero_lt_one hB) 1000)
  have hn : (N : ℝ) ≤ (B : ℝ)^6 := by exact_mod_cast candidate_count_power_bound hM hN
  have hm : (M : ℝ) ≤ (B : ℝ)^6 := by
    exact (show (M : ℝ) ≤ (B : ℝ)^2 by exact_mod_cast hM).trans
      (pow_le_pow_right₀ hB1 (by norm_num : 2 ≤ 6))
  have hb6 : (1 : ℝ) ≤ (B : ℝ)^6 := one_le_pow₀ hB1
  have hlog : (1/2 : ℝ) ≤ Real.log 2 := by have h := Real.log_two_gt_d9; linarith
  have hrec : 1/(Real.log 2*auxiliaryCutoff B) ≤ 2/(auxiliaryCutoff B : ℝ) := by
    have hh : (auxiliaryCutoff B : ℝ)/2 ≤ Real.log 2*auxiliaryCutoff B := by nlinarith
    calc
      _ ≤ 1/((auxiliaryCutoff B : ℝ)/2) := one_div_le_one_div_of_le (by positivity) hh
      _ = _ := by ring
  have hd : D ≤ 30*(B : ℝ)^13/(auxiliaryCutoff B : ℝ) := by
    calc
      D ≤ (N : ℝ)*(2+5*(M : ℝ)+8*N)*(B : ℝ)*(1/(Real.log 2*auxiliaryCutoff B)) := by
        convert hD using 1; ring
      _ ≤ (B : ℝ)^6*(15*(B : ℝ)^6)*(B : ℝ)*(2/(auxiliaryCutoff B : ℝ)) := by
        gcongr
        nlinarith
      _ = _ := by ring
  have hf : 8*((N : ℝ)+(M : ℝ))^2*U ≤ 32*(B : ℝ)^19/(auxiliaryCutoff B : ℝ) := by
    calc
      _ ≤ 8*((N : ℝ)+(M : ℝ))^2*(1/(auxiliaryCutoff B : ℝ)) := by gcongr
      _ ≤ 8*(2*(B : ℝ)^6)^2*(1/(auxiliaryCutoff B : ℝ)) := by gcongr; linarith
      _ = 32*(B : ℝ)^12/(auxiliaryCutoff B : ℝ) := by ring
      _ ≤ _ := by gcongr; norm_num
  have hg : 6*(N : ℝ)*D ≤ 180*(B : ℝ)^19/(auxiliaryCutoff B : ℝ) := by
    calc
      _ ≤ 6*(N : ℝ)*(30*(B : ℝ)^13/(auxiliaryCutoff B : ℝ)) := by gcongr
      _ ≤ 6*(B : ℝ)^6*(30*(B : ℝ)^13/(auxiliaryCutoff B : ℝ)) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ 32*(B : ℝ)^19/(auxiliaryCutoff B : ℝ)+180*(B : ℝ)^19/(auxiliaryCutoff B : ℝ) :=
      add_le_add hf hg
    _ = _ := by ring

end JointDickman

end OAI
