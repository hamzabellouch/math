import OAI.NumberTheory.JointDickman.Counting.BlockCounting
import OAI.NumberTheory.JointDickman.Amplification.FiniteWeightedUnion

namespace OAI

/-! # Splitting block origins into the left boundary and counting range -/
namespace JointDickman
open Finset Classical

theorem blockOrigins_sum_bound (M V K : ℕ) (f : ℤ → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hf : ∀ s, 0 ≤ f s) (hleft : ∀ s < 0, f s ≤ D)
    (hsupport : ∀ s : ℤ, (K : ℤ) ≤ s → f s = 0) :
    (∑ s ∈ blockOrigins M V, f s) ≤ (M : ℝ)*D+∑ u ∈ range K, f (u : ℤ) := by
  let U := Ico (1-(M : ℤ)) 0 ∪ (range K).image (fun u : ℕ => (u : ℤ))
  have heq : (∑ s ∈ blockOrigins M V ∩ U, f s) = ∑ s ∈ blockOrigins M V, f s := by
    apply sum_subset inter_subset_left
    intro s hs hn
    have hs' := mem_Icc.mp hs
    have hsu : s ∉ U := by intro hu; exact hn (mem_inter.mpr ⟨hs,hu⟩)
    apply hsupport
    by_contra hk
    have hk' : s < (K : ℤ) := lt_of_not_ge hk
    apply hsu
    by_cases hz : s < 0
    · exact mem_union_left _ (mem_Ico.mpr ⟨hs'.1,hz⟩)
    · apply mem_union_right
      apply mem_image.mpr
      refine ⟨s.toNat,mem_range.mpr ?_,?_⟩
      · omega
      · exact Int.toNat_of_nonneg (le_of_not_gt hz)
  rw [← heq]
  calc
    _ ≤ ∑ s ∈ U, f s := sum_le_sum_of_subset_of_nonneg inter_subset_right (fun s _ _ => hf s)
    _ ≤ (∑ s ∈ Ico (1-(M : ℤ)) 0, f s)+∑ s ∈ (range K).image (fun u : ℕ => (u : ℤ)), f s :=
      sum_union_le_nonneg _ _ f hf
    _ ≤ (M : ℝ)*D+∑ u ∈ range K, f (u : ℤ) := by
      apply add_le_add
      · calc
          _ ≤ ((Ico (1-(M : ℤ)) 0).card : ℝ)*D :=
            (sum_le_sum (fun s hs => hleft s (mem_Ico.mp hs).2)).trans_eq (by simp)
          _ ≤ (M : ℝ)*D := by
            apply mul_le_mul_of_nonneg_right _ hD
            exact_mod_cast (show (Ico (1-(M : ℤ)) 0).card ≤ M by rw [Int.card_Ico]; omega)
      · rw [sum_image]
        intro a _ b _ hab
        exact Int.ofNat_injective hab

end JointDickman

end OAI
