import Mathlib
import OAI.Combinatorics.KMedian.Expanders.SpectralWalk
import OAI.Combinatorics.KMedian.PCP.Boundary

namespace OAI

section Inline_PCPWalsh

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace Walsh
noncomputable def sign (b : Bit) : ℝ := if b=0 then 1 else -1
@[simp] lemma sign_zero : sign 0=1 := by simp [sign]
@[simp] lemma sign_one : sign 1= -1 := by norm_num [sign]
lemma sign_cases (b : Bit) : sign b=1 ∨ sign b= -1 := by
  rcases bit_cases b with rfl | rfl <;> simp
lemma sign_add (b c : Bit) : sign (b+c)=sign b*sign c := by
  rcases bit_cases b with rfl | rfl <;> rcases bit_cases c with rfl | rfl <;> simp [CharTwo.add_self_eq_zero, sign]
@[simp] lemma sign_sq (b : Bit) : sign b ^ 2=1 := by
  rcases sign_cases b with h | h <;> rw [h] <;> norm_num

variable {I : Type} [Fintype I]
noncomputable def character (b x : BitVector I) : ℝ := sign (dot b x)
lemma character_comm (b x : BitVector I) : character b x=character x b := by
  unfold character dot
  simp_rw [mul_comm]
lemma character_add (b x y : BitVector I) : character b (x+y)=character b x*character b y := by
  unfold character
  rw [dot_add_right, sign_add]
lemma character_add_left (a b x : BitVector I) :
    character (a+b) x=character a x*character b x := by
  unfold character
  rw [dot_add_left,sign_add]
@[simp] lemma character_zero (x : BitVector I) : character 0 x=1 := by simp [character]
@[simp] lemma character_sq (b x : BitVector I) : character b x^2=1 := by simp [character]
lemma character_cases (b x : BitVector I) : character b x=1 ∨ character b x= -1 := sign_cases _

variable [DecidableEq I]

lemma character_mean (b : BitVector I) : (𝔼 x, character b x) = if b=0 then 1 else 0 := by
  classical
  by_cases hb : b=0
  · subst b; simp
  rw [ite_eq_right hb]
  obtain ⟨i,hi⟩ : ∃ i, b i ≠ 0 := by
    by_contra h
    push Not at h
    exact hb (funext h)
  have hd : dot b (Pi.single i 1) ≠ 0 := by simpa only [dot_single] using hi
  have hbalance := linear_nonzero_rate (dotHom b) (Pi.single i 1) hd
  have he (x : BitVector I) : character b x=1-2*(if dot b x ≠ 0 then (1:ℝ) else 0) := by
    unfold character sign
    split_ifs <;> norm_num; simp_all
  simp_rw [he]
  rw [expect_sub_distrib, ← mul_expect, Fintype.expect_const]
  have hh : (𝔼 x : BitVector I, if dot b x ≠ 0 then (1:ℝ) else 0) =
      testRate (fun x => dotHom b x ≠ 0) := by
    unfold testRate
    apply expect_congr rfl
    intro x _
    by_cases hx : dot b x ≠ 0 <;> simp [dotHom,hx]
  rw [hh,hbalance]
  norm_num

lemma orthogonal (a b : BitVector I) :
    (𝔼 x, character a x * character b x) = if a=b then 1 else 0 := by
  simp_rw [← character_add_left]
  rw [character_mean]
  congr 1
  rw [add_eq_zero_iff_eq_neg]
  have hb : -b=b := funext (fun i => CharTwo.neg_eq (b i))
  rw [hb]

lemma dual_orthogonal (x y : BitVector I) :
    (𝔼 b, character b x * character b y) = if x=y then 1 else 0 := by
  simp_rw [character_comm (x := x),character_comm (x := y)]
  exact orthogonal x y

noncomputable def coefficient (f : BitVector I → ℝ) (b : BitVector I) : ℝ :=
  pairing f (character b)

lemma inversion (f : BitVector I → ℝ) (x : BitVector I) :
    (∑ b, coefficient f b * character b x) = f x := by
  classical
  unfold coefficient pairing
  simp_rw [expect_mul]
  rw [← expect_sum_comm]
  have he (y : BitVector I) :
      (∑ b, f y * character b y * character b x) =
        f y * ((Fintype.card (BitVector I):ℝ) * if y=x then 1 else 0) := by
    simp_rw [mul_assoc]
    rw [← mul_sum]
    congr 1
    have hh := dual_orthogonal y x
    rw [Fintype.expect_eq_sum_div_card] at hh
    have hn : (Fintype.card (BitVector I):ℝ) ≠ 0 := by positivity
    exact (div_eq_iff hn).mp hh |>.trans (mul_comm _ _)
  simp_rw [he]
  rw [Fintype.expect_eq_sum_div_card]
  simp only [mul_ite,mul_one,mul_zero]
  rw [sum_ite_eq' univ x (fun y => f y * (Fintype.card (BitVector I):ℝ))]
  simp only [mem_univ,ite_true]
  have hn : (Fintype.card (BitVector I):ℝ) ≠ 0 := by positivity
  exact mul_div_cancel_right₀ _ hn

theorem parseval (f : BitVector I → ℝ) : energy f=∑ b, coefficient f b ^ 2 := by
  unfold energy
  calc
    (𝔼 x, f x^2) = 𝔼 x, f x * ∑ b, coefficient f b * character b x := by
      apply expect_congr rfl
      intro x _
      rw [inversion]
      ring
    _ = ∑ b, 𝔼 x, coefficient f b * (f x * character b x) := by
      simp_rw [mul_sum, show ∀ x b, f x*(coefficient f b*character b x)=
        coefficient f b*(f x*character b x) by intros; ring]
      rw [expect_sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro b _
      rw [← mul_expect]
      change coefficient f b*coefficient f b=coefficient f b^2
      ring

@[simp] lemma coefficient_zero (f : BitVector I → ℝ) : coefficient f 0=𝔼 x, f x := by
  simp [coefficient,pairing]

end Walsh
end MetricKMedian.PCP

end Inline_PCPWalsh

end OAI
