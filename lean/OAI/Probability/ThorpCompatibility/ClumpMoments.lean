import Mathlib
import OAI.Probability.ThorpCompatibility.ClumpCost
import OAI.Probability.ThorpCompatibility.ListIncidence
import OAI.Probability.ThorpCompatibility.UniformAverages

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
open Finset
noncomputable def clumpWeight {α : Type*} (H z : ℝ) (s : Finset α) : ℝ :=
  if s = ∅ then 1 else if H < s.card then Real.exp (z * s.card) else 0

lemma clumpWeight_nonneg {α : Type*} (H z : ℝ) (s : Finset α) :
    0 ≤ clumpWeight H z s := by
  unfold clumpWeight
  split_ifs <;> positivity

lemma cell_clump_exp_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (H z : ℝ) (hH : 0 ≤ H) (r : α → Equiv.Perm β) (b : β × β) :
    Real.exp (z * (if H < (cellRows r b).card then ((cellRows r b).card : ℝ) else 0)) ≤
      ∑ s : Finset α, clumpWeight H z s *
        (if ∀ i ∈ s, r i b.1 = b.2 then 1 else 0) := by
  let W : Finset α → ℝ := fun s => clumpWeight H z s *
    (if ∀ i ∈ s, r i b.1 = b.2 then 1 else 0)
  change Real.exp _ ≤ ∑ s, W s
  have hW (s : Finset α) : 0 ≤ W s :=
    mul_nonneg (clumpWeight_nonneg _ _ _) (by split_ifs <;> norm_num)
  by_cases h : H < (cellRows r b).card
  · have hs : cellRows r b ≠ ∅ := by
      intro he
      simp [he] at h
      linarith
    have hp : ∀ i ∈ cellRows r b, r i b.1 = b.2 := by
      intro i hi
      simpa only [cellRows, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    calc
      _ = W (cellRows r b) := by
        dsimp [W]
        rw [ite_eq_left h, ite_eq_left hp]
        simp [clumpWeight, hs, h]
      _ ≤ _ := Finset.single_le_sum (fun s _ => hW s) (Finset.mem_univ _)
  · calc
      _ = W ∅ := by
        dsimp [W]
        simp [clumpWeight, h]
      _ ≤ _ := Finset.single_le_sum (fun s _ => hW s) (Finset.mem_univ _)

lemma clump_expansion {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (H z : ℝ) (r : α → Equiv.Perm β) :
    (∏ b : β × β, ∑ s : Finset α, clumpWeight H z s *
      (if ∀ i ∈ s, r i b.1 = b.2 then 1 else 0)) =
    ∑ S : β × β → Finset α, (∏ b, clumpWeight H z (S b)) *
      (if MeetsLists S r then 1 else 0) := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.prod_mul_distrib, Finset.prod_boole]
  have hiff : (∀ b : β × β, ∀ i ∈ S b, r i b.1 = b.2) ↔ MeetsLists S r := by
    simp [MeetsLists, Prod.forall]
  simp only [Finset.mem_univ, forall_const]
  by_cases h : MeetsLists S r
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hh => h (hiff.mp hh)), ite_eq_right h]

lemma clump_exp_moment_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (H z : ℝ) (hH : 0 ≤ H) (hn : 0 < Fintype.card β) :
    uniformMean (fun r : α → Equiv.Perm β => Real.exp (z * clumpCount H r)) ≤
      (∑ s : Finset α, clumpWeight H z s *
        (Real.exp 1 / Fintype.card β) ^ s.card) ^ (Fintype.card β ^ 2) := by
  let ρ : ℝ := Real.exp 1 / Fintype.card β
  calc
    _ ≤ uniformMean (fun r : α → Equiv.Perm β =>
        ∏ b : β × β, ∑ s : Finset α, clumpWeight H z s *
          (if ∀ i ∈ s, r i b.1 = b.2 then 1 else 0)) := by
      apply uniformMean_mono
      intro r
      unfold clumpCount
      rw [Nat.cast_sum, Finset.mul_sum, Real.exp_sum]
      apply Finset.prod_le_prod₀
      · intro b _
        exact (Real.exp_pos _).le
      · intro b _
        simpa only [Nat.cast_ite, Nat.cast_zero] using cell_clump_exp_le H z hH r b
    _ = ∑ S : β × β → Finset α, (∏ b, clumpWeight H z (S b)) *
        uniformProbability (MeetsLists S) := by
      simp_rw [clump_expansion]
      rw [uniformMean_sum]
      apply Finset.sum_congr rfl
      intro S _
      rw [uniformMean_const_mul, uniformMean_indicator]
    _ ≤ ∑ S : β × β → Finset α, (∏ b, clumpWeight H z (S b)) *
        ρ ^ (∑ b, (S b).card) := by
      apply Finset.sum_le_sum
      intro S _
      apply mul_le_mul_of_nonneg_left (meetsLists_probability_le hn S)
      exact Finset.prod_nonneg fun b _ => clumpWeight_nonneg _ _ _
    _ = ∏ b : β × β, ∑ s : Finset α, clumpWeight H z s * ρ ^ s.card := by
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    _ = _ := by simp [ρ, Fintype.card_prod, pow_two]

end ThorpCompatibility

end OAI
