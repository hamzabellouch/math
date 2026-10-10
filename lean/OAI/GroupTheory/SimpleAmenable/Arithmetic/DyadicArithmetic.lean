import Mathlib

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SourceDyadicArithmetic
open Classical Filter
open scoped Topology

noncomputable def sourceDyadicN (n : ℕ) : ℝ := (2:ℝ)^(4*n)
noncomputable def sourceDyadicWeight (n : ℕ) : ℝ := (Real.log (sourceDyadicN n))^(-3/4:ℝ)
def sourceDyadicIndices (n : ℕ) : Finset ℕ := Finset.Icc n (2*n)

theorem sourceDyadicN_pos (n : ℕ) : 0 < sourceDyadicN n := by unfold sourceDyadicN; positivity

theorem sourceDyadicN_one_le (n : ℕ) : 1 ≤ sourceDyadicN n := by
  unfold sourceDyadicN
  exact one_le_pow₀ (by norm_num)

theorem sourceDyadicN_fourth_root (n : ℕ) : (sourceDyadicN n)^(1/4:ℝ)=(2:ℝ)^n := by
  unfold sourceDyadicN
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  have he : ((4*n:ℕ):ℝ)*(1/4:ℝ)=(n:ℝ) := by push_cast; ring
  rw [he,Real.rpow_natCast]

theorem sourceDyadicN_square_root (n : ℕ) : (sourceDyadicN n)^(1/2:ℝ)=(2:ℝ)^(2*n) := by
  unfold sourceDyadicN
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  have he : ((4*n:ℕ):ℝ)*(1/2:ℝ)=((2*n:ℕ):ℝ) := by push_cast; ring
  rw [he,Real.rpow_natCast]

theorem sourceDyadicIndices_exact (n i : ℕ) :
    i∈sourceDyadicIndices n ↔ (sourceDyadicN n)^(1/4:ℝ) ≤ (2:ℝ)^i ∧
      (2:ℝ)^i ≤ (sourceDyadicN n)^(1/2:ℝ) := by
  rw [sourceDyadicN_fourth_root,sourceDyadicN_square_root]
  simp only [sourceDyadicIndices,Finset.mem_Icc,pow_le_pow_iff_right₀ (by norm_num : (1:ℝ) < 2)]

theorem sourceDyadicIndices_card (n : ℕ) : (sourceDyadicIndices n).card=n+1 := by
  simp only [sourceDyadicIndices,Nat.card_Icc]
  omega

theorem sourceDyadic_log (n : ℕ) : Real.log (sourceDyadicN n)=(4*Real.log 2)*(n:ℝ) := by
  rw [sourceDyadicN,Real.log_pow]
  push_cast
  ring

theorem sourceDyadicWeight_square (n : ℕ) :
    (sourceDyadicWeight n)^2=(4*Real.log 2)^(-3/2:ℝ)*(n:ℝ)^(-3/2:ℝ) := by
  have hb : 0 ≤ 4*Real.log 2 := by positivity
  unfold sourceDyadicWeight
  rw [sourceDyadic_log,← Real.rpow_mul_natCast (mul_nonneg hb (Nat.cast_nonneg n))]
  norm_num
  rw [Real.mul_rpow hb (Nat.cast_nonneg n)]

theorem sourceDyadicWeight_energy_bound {n : ℕ} (hn : 1 ≤ n) :
    ((sourceDyadicIndices n).card:ℝ)*(sourceDyadicWeight n)^2 ≤ 2*(4*Real.log 2)^(-3/2:ℝ)*(n:ℝ)^(-1/2:ℝ) := by
  have hn₀ : 0 < (n:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn₁ : (1:ℝ) ≤ n := by exact_mod_cast hn
  rw [sourceDyadicIndices_card,Nat.cast_add,Nat.cast_one,sourceDyadicWeight_square]
  have hc : 0 ≤ (4*Real.log 2)^(-3/2:ℝ)*(n:ℝ)^(-3/2:ℝ) := by positivity
  have he : (n:ℝ)*(n:ℝ)^(-3/2:ℝ)=(n:ℝ)^(-1/2:ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one (n:ℝ)]
    rw [← Real.rpow_add hn₀]
    norm_num
  calc
    _ ≤ (2*(n:ℝ))*((4*Real.log 2)^(-3/2:ℝ)*(n:ℝ)^(-3/2:ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) hc
    _ = _ := by rw [show (2*(n:ℝ))*((4*Real.log 2)^(-3/2:ℝ)*(n:ℝ)^(-3/2:ℝ))=
        (2*(4*Real.log 2)^(-3/2:ℝ))*((n:ℝ)*(n:ℝ)^(-3/2:ℝ)) by ring,he]

theorem sourceDyadicWeight_energy_tendsto :
    Tendsto (fun n => ((sourceDyadicIndices n).card:ℝ)*(sourceDyadicWeight n)^2) atTop (nhds 0) := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)^(-1/2:ℝ)) atTop (nhds 0) := by
    convert (tendsto_rpow_neg_atTop (show (0:ℝ) < 1/2 by norm_num)).comp
      (tendsto_natCast_atTop_atTop (R:=ℝ)) using 1
    norm_num
    rfl
  have ht' := ht.const_mul (2*(4*Real.log 2)^(-3/2:ℝ))
  simp only [mul_zero] at ht'
  apply squeeze_zero' (Eventually.of_forall (fun n => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))) _ ht'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact sourceDyadicWeight_energy_bound hn

theorem sourceDyadic_fine_eventually (R : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠn : ℕ in atTop,∀i∈sourceDyadicIndices n,R ≤ κ/((2:ℝ)^i/sourceDyadicN n) := by
  have ht := (tendsto_pow_atTop_atTop_of_one_lt (show (1:ℝ) < 4 by norm_num)).const_mul_atTop hκ
  filter_upwards [ht.eventually_ge_atTop R] with n hn i hi
  have hi' : i ≤ 2*n := (Finset.mem_Icc.mp hi).2
  have hp : (2:ℝ)^i ≤ (2:ℝ)^(2*n) := pow_le_pow_right₀ (by norm_num) hi'
  have he : κ/((2:ℝ)^(2*n)/sourceDyadicN n)=κ*(4:ℝ)^n := by
    unfold sourceDyadicN
    have hN : (2:ℝ)^(4*n)=((2:ℝ)^(2*n))^2 := by rw [← pow_mul]; congr 1; omega
    have h4 : (4:ℝ)^n=(2:ℝ)^(2*n) := by rw [pow_mul]; norm_num
    rw [hN,h4]
    field_simp
  calc
    R ≤ κ*(4:ℝ)^n := hn
    _ = κ/((2:ℝ)^(2*n)/sourceDyadicN n) := he.symm
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left hκ.le (div_pos (by positivity) (sourceDyadicN_pos n))
      exact div_le_div_of_nonneg_right hp (sourceDyadicN_pos n).le

end SourceDyadicArithmetic

end SimpleAmenable
end
end

end OAI
