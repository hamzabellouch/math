import OAI.Probability.MatroidProphet.Density.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI

namespace MatroidProphet

open Set

variable {α : Type*} [Fintype α]

lemma natRank_union_le_add_ncard (M : Matroid α) (X Z : Set α) :
    natRank M (X ∪ Z) ≤ natRank M X + Z.ncard := by
  have hz : Z.encard ≠ ⊤ := (Set.toFinite Z).encard_lt_top.ne
  have h := ENat.toNat_le_toNat (M.eRk_union_le_eRk_add_encard X Z)
    (WithTop.add_ne_top.2 ⟨rank_ne_top M X, hz⟩)
  simpa only [ENat.toNat_add (rank_ne_top M X) hz, natRank, Set.ncard_def] using h

lemma densityExpansion_residual_le_generators (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D P Z : Set α) :
    let Q := densityExpansion M hE κ D P
    (D ∩ (M.closure (Q ∪ Z) \ Q)).ncard ≤ κ * Z.ncard := by
  dsimp only
  have hd := densityExpansion_residual M hE κ D P Z
  have hr := Nat.mul_le_mul_left κ
    (natRank_union_le_add_ncard M (densityExpansion M hE κ D P) Z)
  rw [Nat.mul_add] at hr
  dsimp only at hd
  omega

lemma safe_layer_le_witness_residual (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D F K Z A S : Set α)
    (hS : S ⊆ (D ∩ A) \ densityExpansion M hE κ D (F ∪ K)) :
    S.ncard ≤ κ * Z.ncard +
      (A \ M.closure (densityExpansion M hE κ D F ∪ K ∪ Z)).ncard := by
  let Q := densityExpansion M hE κ D (F ∪ K)
  let R := A \ M.closure (densityExpansion M hE κ D F ∪ K ∪ Z)
  have hX : densityExpansion M hE κ D F ⊆ Q :=
    densityExpansion_mono M hE κ D subset_union_left
  have hK : K ⊆ Q := subset_union_right.trans
    (densityExpansion_extensive M hE κ D (F ∪ K))
  have hcl : M.closure (densityExpansion M hE κ D F ∪ K ∪ Z) ⊆
      M.closure (Q ∪ Z) :=
    M.closure_subset_closure (union_subset_union (union_subset hX hK) Subset.rfl)
  have hcharge : S \ R ⊆ D ∩ (M.closure (Q ∪ Z) \ Q) := by
    intro e he
    have hs := hS he.1
    refine ⟨hs.1.1, hcl ?_, hs.2⟩
    by_contra hn
    exact he.2 ⟨hs.1.2, hn⟩
  have hcount := (Set.ncard_mono hcharge).trans
    (densityExpansion_residual_le_generators M hE κ D (F ∪ K) Z)
  exact (Set.ncard_le_ncard_sdiff_add_ncard S R).trans (Nat.add_le_add_right hcount _)

lemma safe_sum_le_witness_residual {ι : Type*} (L : Finset ι)
    (M : Matroid α) (hE : M.E = univ) (κ : ℕ) (D : Set α)
    (F K Z A S : ι → Set α)
    (hS : ∀ b ∈ L, S b ⊆ (D ∩ A b) \ densityExpansion M hE κ D (F b ∪ K b)) :
    ∑ b ∈ L, (S b).ncard ≤ κ * (∑ b ∈ L, (Z b).ncard) +
      ∑ b ∈ L, (A b \ M.closure (densityExpansion M hE κ D (F b) ∪ K b ∪ Z b)).ncard := by
  calc
    _ ≤ ∑ b ∈ L, (κ * (Z b).ncard +
        (A b \ M.closure (densityExpansion M hE κ D (F b) ∪ K b ∪ Z b)).ncard) :=
      Finset.sum_le_sum fun b hb => safe_layer_le_witness_residual M hE κ D
        (F b) (K b) (Z b) (A b) (S b) (hS b hb)
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]

end MatroidProphet

end OAI
