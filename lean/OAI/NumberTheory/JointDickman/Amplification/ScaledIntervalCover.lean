import OAI.NumberTheory.JointDickman.Amplification.FiniteWeightedUnion
import OAI.NumberTheory.JointDickman.Counting.CountingModelMean

namespace OAI

/-! # A finite interval cover for the counting-scale energy average -/
namespace JointDickman
open Finset Classical

theorem scaled_interval_cover {X : ℝ} (hX : 1 ≤ X) (K U : ℕ)
    (hU : (U : ℝ) ≤ ((K : ℝ)+1)*X) :
    range U ⊆ range ⌈2*X⌉₊ ∪ (Icc 2 K).biUnion (fun k : ℕ => Ico ⌈(k : ℝ)*X⌉₊ ⌊2*((k : ℝ)*X)⌋₊) := by
  have hXp : 0 < X := by linarith
  intro u hu
  by_cases hsmall : u < ⌈2*X⌉₊
  · exact mem_union_left _ (mem_range.mpr hsmall)
  apply mem_union_right
  let k := ⌊(u : ℝ)/X⌋₊
  have h2u : 2*X ≤ (u : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast le_of_not_gt hsmall)
  have hk2 : 2 ≤ k := by
    apply Nat.le_floor
    change (2 : ℝ) ≤ (u : ℝ)/X
    exact (le_div_iff₀ hXp).mpr h2u
  have hu' : (u : ℝ) < ((K : ℝ)+1)*X := (by exact_mod_cast mem_range.mp hu : (u : ℝ) < U).trans_le hU
  have hkK : k ≤ K := by
    have hh : k < K+1 := (Nat.floor_lt (by positivity : 0 ≤ (u : ℝ)/X)).mpr (by
      rw [Nat.cast_add,Nat.cast_one]
      exact (div_lt_iff₀ hXp).mpr hu')
    omega
  have hku : (k : ℝ)*X ≤ u := (le_div_iff₀ hXp).mp (Nat.floor_le (by positivity))
  have huk : (u : ℝ) < ((k : ℝ)+1)*X := (div_lt_iff₀ hXp).mp (Nat.lt_floor_add_one ((u : ℝ)/X))
  have hk2r : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hupper : (u : ℝ)+1 ≤ 2*((k : ℝ)*X) := by nlinarith
  have huupper : u+1 ≤ ⌊2*((k : ℝ)*X)⌋₊ := Nat.le_floor (by simpa only [Nat.cast_add,Nat.cast_one] using hupper)
  exact mem_biUnion.mpr ⟨k,mem_Icc.mpr ⟨hk2,hkK⟩,
    mem_Ico.mpr ⟨Nat.ceil_le.mpr hku,by omega⟩⟩

theorem scaled_interval_sum_bound {X D : ℝ} (hX : 1 ≤ X) (hD : 0 ≤ D)
    (K U : ℕ) (hU : (U : ℝ) ≤ ((K : ℝ)+1)*X)
    (f : ℕ → ℝ) (hf : ∀ u, 0 ≤ f u) (hcap : ∀ u, f u ≤ D) :
    (∑ u ∈ range U, f u) ≤ (2*X+1)*D+
      ∑ k ∈ Icc 2 K, ∑ u ∈ Ico ⌈(k : ℝ)*X⌉₊ ⌊2*((k : ℝ)*X)⌋₊, f u := by
  calc
    _ ≤ ∑ u ∈ range ⌈2*X⌉₊ ∪ (Icc 2 K).biUnion
        (fun k : ℕ => Ico ⌈(k : ℝ)*X⌉₊ ⌊2*((k : ℝ)*X)⌋₊), f u :=
      sum_le_sum_of_subset_of_nonneg (scaled_interval_cover hX K U hU) (fun u _ _ => hf u)
    _ ≤ (∑ u ∈ range ⌈2*X⌉₊, f u)+
        ∑ u ∈ (Icc 2 K).biUnion (fun k : ℕ => Ico ⌈(k : ℝ)*X⌉₊ ⌊2*((k : ℝ)*X)⌋₊), f u :=
      sum_union_le_nonneg _ _ f hf
    _ ≤ (2*X+1)*D+∑ k ∈ Icc 2 K, ∑ u ∈ Ico ⌈(k : ℝ)*X⌉₊ ⌊2*((k : ℝ)*X)⌋₊, f u := by
      apply add_le_add
      · have hh : (∑ u ∈ range ⌈2*X⌉₊, f u) ≤ (⌈2*X⌉₊ : ℝ)*D :=
          (sum_le_sum (fun u _ => hcap u)).trans_eq (by simp)
        exact hh.trans (mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (by linarith : 0 ≤ 2*X)).le hD)
      · exact sum_biUnion_le_nonneg _ _ f hf

end JointDickman

end OAI
