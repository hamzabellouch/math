import OAI.LinearAlgebra.MatrixMultiplication.Recovery.InheritedMasks
import Mathlib.Algebra.BigOperators.Field

namespace OAI

/-! Finite orbit symmetries, masks and exact recovery operations. -/

namespace MatrixMultiplication.InheritedMasks

open MatrixMultiplication.Foundation
open scoped BigOperators

section Pushforward

variable {A B : Type*} [Fintype A] [DecidableEq B]

def pushforwardLaw (statistic : A → B) (ν : A → ℝ) (b : B) : ℝ :=
  ∑ a with statistic a = b, ν a

theorem pushforwardLaw_nonneg (statistic : A → B) (ν : A → ℝ)
    (hν : ∀ a, 0 ≤ ν a) (b : B) : 0 ≤ pushforwardLaw statistic ν b := by
  exact Finset.sum_nonneg fun a _ => hν a

theorem pushforwardLaw_le_one (statistic : A → B) (ν : A → ℝ)
    (hν : ∀ a, 0 ≤ ν a) (hsum : ∑ a, ν a = 1) (b : B) :
    pushforwardLaw statistic ν b ≤ 1 := by
  calc
    pushforwardLaw statistic ν b ≤ ∑ a, ν a :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun a _ _ => hν a)
    _ = 1 := hsum

end Pushforward

section Windows

variable {P A B : Type*} [Fintype P]
  [Fintype A] [DecidableEq A] [DecidableEq B]

theorem wordPopulation_statistic (w : P → A) (statistic : A → B) (b : B) :
    wordPopulation (statistic ∘ w) b =
      ∑ a with statistic a = b, wordPopulation w a := by
  simpa only [wordPopulation, Fintype.card_subtype, Finset.mem_filter,
    Finset.mem_univ, true_and, Function.comp_apply] using
    (Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset P)
      (Finset.univ.filter fun a => statistic a = b) w).symm

theorem empiricalLaw_statistic (w : P → A) (statistic : A → B) (b : B) :
    empiricalLaw (statistic ∘ w) b =
      pushforwardLaw statistic (empiricalLaw w) b := by
  simp only [empiricalLaw, wordPopulation_statistic, pushforwardLaw,
    Nat.cast_sum, Finset.sum_div]

omit [Fintype A] in
theorem typeWindow_mono (ν : A → ℝ) (w : P → A) {τ η : ℝ}
    (hτη : τ ≤ η) (hw : typeWindow ν τ w) : typeWindow ν η w := by
  intro a
  exact (hw a).trans hτη

theorem typeWindow_statistic_coordinate (ν : A → ℝ) (τ : ℝ) (w : P → A)
    (statistic : A → B) (hw : typeWindow ν τ w) (b : B) :
    |empiricalLaw (statistic ∘ w) b - pushforwardLaw statistic ν b| ≤
      ((Finset.univ.filter fun a => statistic a = b).card : ℝ) * τ := by
  rw [empiricalLaw_statistic]
  unfold pushforwardLaw
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a with statistic a = b, |empiricalLaw w a - ν a| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ Finset.univ.filter (fun a => statistic a = b), τ :=
      Finset.sum_le_sum fun a _ => hw a
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

theorem typeWindow_statistic (ν : A → ℝ) (τ : ℝ) (w : P → A)
    (statistic : A → B) (hτ : 0 ≤ τ) (hw : typeWindow ν τ w) :
    typeWindow (pushforwardLaw statistic ν) (Fintype.card A * τ)
      (statistic ∘ w) := by
  intro b
  calc
    _ ≤ ((Finset.univ.filter fun a => statistic a = b).card : ℝ) * τ :=
      typeWindow_statistic_coordinate ν τ w statistic hw b
    _ ≤ Fintype.card A * τ :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_univ _)) hτ

end Windows

end MatrixMultiplication.InheritedMasks

end OAI
