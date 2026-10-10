import OAI.NumberTheory.JointDickman.Amplification.FiniteEventUnion
import OAI.NumberTheory.JointDickman.Probability.TwoSplitLaw

namespace OAI

/-! # Comparing a finite hit law with the empty outcome -/

namespace JointDickman
open Finset PublishedInputs

theorem finiteMass_l1_le_two {A : Type*} [Fintype A] (w v : A → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hv : ∀ a, 0 ≤ v a)
    (hwone : ∑ a, w a = 1) (hvone : ∑ a, v a = 1) :
    (∑ a, |w a-v a|) ≤ 2 := by
  calc
    _ ≤ ∑ a, (w a+v a) := sum_le_sum (fun a _ => abs_sub_le_iff.mpr ⟨by linarith [hv a],by linarith [hw a]⟩)
    _ = 2 := by rw [sum_add_distrib,hwone,hvone]; norm_num

theorem finitePushMass_nonneg {Ω A : Type*} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (f : Ω → A) (a : A) :
    0 ≤ finitePushMass w f a := by
  classical
  unfold finitePushMass
  exact sum_nonneg (fun x _ => by split_ifs <;> first | exact hw x | rfl)

theorem finitePushMass_sum {Ω A : Type*} [Fintype Ω] [Fintype A]
    (w : Ω → ℝ) (f : Ω → A) : (∑ a, finitePushMass w f a) = ∑ x, w x := by
  classical
  unfold finitePushMass
  rw [sum_comm]
  simp

theorem finitePushMass_test_real {Ω A : Type*} [Fintype Ω] [Fintype A]
    (w : Ω → ℝ) (f : Ω → A) (F : A → ℝ) :
    (∑ a, finitePushMass w f a*F a) = ∑ x, w x*F (f x) := by
  classical
  unfold finitePushMass
  simp_rw [sum_mul,ite_mul,zero_mul]
  rw [sum_comm]
  simp

open Classical in
theorem finiteMass_l1_point {A : Type*} [Fintype A] [DecidableEq A]
    (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (hwone : ∑ a, w a = 1) (a₀ : A) :
    (∑ a, |w a-(if a = a₀ then 1 else 0)|) =
      2*finiteProbability w (fun a => a ≠ a₀) := by
  have hw0 : w a₀ ≤ 1 := by
    rw [← hwone]
    exact single_le_sum (fun a _ => hw a) (mem_univ _)
  have hs : (∑ a ∈ univ.erase a₀, w a)+w a₀ = 1 := by
    rw [sum_erase_add _ _ (mem_univ _),hwone]
  rw [← sum_erase_add _ _ (mem_univ a₀)]
  have he : (∑ a ∈ univ.erase a₀, |w a-(if a = a₀ then 1 else 0)|) =
      ∑ a ∈ univ.erase a₀, w a := by
    apply sum_congr rfl
    intro a ha
    rw [ite_eq_right (ne_of_mem_erase ha),sub_zero,abs_of_nonneg (hw a)]
  have hp : finiteProbability w (fun a => a ≠ a₀) = ∑ a ∈ univ.erase a₀, w a := by
    unfold finiteProbability
    dsimp only
    have heq : univ.erase a₀ = univ.filter (fun a => a ≠ a₀) := by ext a; simp [and_comm]
    rw [heq,sum_filter]
    apply sum_congr rfl
    intro a _
    by_cases ha : a = a₀ <;> simp [ha]
  rw [he,ite_eq_left rfl,abs_of_nonpos (sub_nonpos.mpr hw0),hp]
  linarith only [hs]

end JointDickman

end OAI
