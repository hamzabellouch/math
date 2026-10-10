import OAI.NumberTheory.ShortEgyptian.Holder

namespace OAI

universe uI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

lemma residue_double_count {I : Type uI} [Fintype I] [Nonempty I]
    (H K B : Finset ℕ) (N : I → ℕ) (hN : ∀ i, 0 < N i) (X Y ρ : ℝ) (hρ : 0 < ρ)
    (hH : ∀ u ∈ H, 0 < u ∧ (u:ℝ) ≤ X)
    (hsmall : ∀ u ∈ H, (u:ℝ) ≤ Y → u ∈ K)
    (hlift : ∀ u ∈ H, ∀ i, (residue (N i) u (quotient (N i) u):ℝ) ≤ Y →
      residue (N i) u (quotient (N i) u) ∈ K)
    (hgood : ∀ u ∈ H, u ∉ B → Y < (u:ℝ) →
      ρ*(Fintype.card I:ℝ)/2 ≤ ((univ.filter fun i =>
        (residue (N i) u (quotient (N i) u):ℝ) ≤ Y).card:ℝ)) :
    (H.card:ℝ) ≤ B.card+K.card+2/(ρ*Fintype.card I)*
      ∑ i, ∑ v ∈ K, (truncatedDivisorCount X (N i+v):ℝ) := by
  let W := H.filter (fun u => u ∉ B ∧ Y < (u:ℝ))
  have hsub : H ⊆ B ∪ K ∪ W := by
    intro u hu
    by_cases hb : u ∈ B
    · exact mem_union_left _ (mem_union_left _ hb)
    by_cases hy : (u:ℝ) ≤ Y
    · exact mem_union_left _ (mem_union_right _ (hsmall u hu hy))
    · exact mem_union_right _ (mem_filter.mpr ⟨hu,hb,lt_of_not_ge hy⟩)
  have hc : H.card ≤ B.card+K.card+W.card := (card_le_card hsub).trans
    ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
  let rem (i : I) (u : ℕ) := residue (N i) u (quotient (N i) u)
  have hswap : ∑ u ∈ W, (univ.filter fun i => rem i u ∈ K).card =
      ∑ i, (W.filter fun u => rem i u ∈ K).card := by
    simp only [card_eq_sum_ones,sum_filter]
    exact sum_comm
  have hfiber (i : I) : (W.filter fun u => rem i u ∈ K).card ≤
      ∑ v ∈ K, truncatedDivisorCount X (N i+v) := by
    rw [←sum_card_fiberwise_eq_card_filter W K (rem i)]
    apply sum_le_sum
    intro v _hv
    apply card_le_card
    intro u hu
    obtain ⟨hu,hrem⟩ := mem_filter.mp hu
    have huu := (mem_filter.mp hu).1
    have hupos := (hH u huu).1
    have heq := (residue_spec (hN i) hupos).2
    change N i+rem i u=u*quotient (N i) u at heq
    rw [hrem] at heq
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨predecessor_dvd heq,by have hh := hN i; omega⟩,(hH u huu).2⟩
  have hcount : ∑ u ∈ W, (univ.filter fun i => rem i u ∈ K).card ≤
      ∑ i, ∑ v ∈ K, truncatedDivisorCount X (N i+v) := by
    rw [hswap]
    exact sum_le_sum (fun i _ => hfiber i)
  have hlow (u : ℕ) (hu : u ∈ W) : ρ*(Fintype.card I:ℝ)/2 ≤
      ((univ.filter fun i => rem i u ∈ K).card:ℝ) := by
    obtain ⟨hu,hb,hy⟩ := mem_filter.mp hu
    apply (hgood u hu hb hy).trans
    apply Nat.cast_le.mpr
    apply card_le_card
    intro i hi
    exact mem_filter.mpr ⟨mem_univ i,hlift u hu i (mem_filter.mp hi).2⟩
  have hlo : (W.card:ℝ)*(ρ*Fintype.card I/2) ≤
      ∑ i, ∑ v ∈ K, (truncatedDivisorCount X (N i+v):ℝ) := by
    calc
      _ = ∑ u ∈ W, ρ*(Fintype.card I:ℝ)/2 := by simp only [sum_const,nsmul_eq_mul]
      _ ≤ ∑ u ∈ W, ((univ.filter fun i => rem i u ∈ K).card:ℝ) := sum_le_sum hlow
      _ ≤ _ := by exact_mod_cast hcount
  have hI : 0 < (Fintype.card I:ℝ) := by exact_mod_cast Fintype.card_pos
  have hW : (W.card:ℝ) ≤ 2/(ρ*Fintype.card I)*
      ∑ i, ∑ v ∈ K, (truncatedDivisorCount X (N i+v):ℝ) := by
    have hd := (le_div_iff₀ (div_pos (mul_pos hρ hI) (by norm_num : (0:ℝ)<2))).mpr hlo
    apply hd.trans_eq
    simp only [div_div_eq_mul_div]
    ring
  have hcR : (H.card:ℝ) ≤ B.card+K.card+W.card := by exact_mod_cast hc
  linarith

end ShortEgyptian

end OAI
