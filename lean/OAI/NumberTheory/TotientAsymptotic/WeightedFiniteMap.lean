import OAI.NumberTheory.TotientAsymptotic.FilteredComparison
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace TotientAsymptotic.FiniteMap

/-- A positive weight on all ordinary representatives converts a count of
values into a lower bound for the weighted representation count. -/
lemma weighted_lower {α β : Type*} [DecidableEq α] [DecidableEq β]
    (T D : Finset α) (W E U : Finset β) (F : α → β) (w : α → ℝ) (c : ℝ)
    (hc : 0≤c) (hU : U⊆W) (hbij : Set.BijOn F (↑(T\D)) (↑(W\E)))
    (hw : ∀ t∈T, 0≤w t)
    (hweight : ∀ t∈T\D, F t∈U → c≤w t) :
    c*((U.card : ℝ)-E.card) ≤ ∑ t∈T, w t := by
  let S := (T\D).filter (fun t => F t∈U)
  have hcard : S.card=(U\E).card := by
    apply Finset.card_bij (fun t _ => F t)
    · intro t ht
      obtain ⟨ht,hU⟩ := Finset.mem_filter.mp ht
      exact Finset.mem_sdiff.mpr ⟨hU,(Finset.mem_sdiff.mp (hbij.1 ht)).2⟩
    · intro t ht s hs he
      exact hbij.2.1 (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp hs).1 he
    · intro v hv
      obtain ⟨t,ht,he⟩ := hbij.2.2 (Finset.mem_sdiff.mpr ⟨hU (Finset.mem_sdiff.mp hv).1,(Finset.mem_sdiff.mp hv).2⟩)
      refine ⟨t,Finset.mem_filter.mpr ⟨ht,?_⟩,he⟩
      exact he ▸ (Finset.mem_sdiff.mp hv).1
  have hs : S⊆T := fun _ ht => (Finset.mem_sdiff.mp (Finset.mem_filter.mp ht).1).1
  have hce : (U.card : ℝ)-E.card≤(S.card : ℝ) := by
    have he := Finset.card_sdiff_add_card_inter U E
    have hle := Finset.card_le_card (show U∩E⊆E from Finset.inter_subset_right)
    have her : ((U\E).card : ℝ)+(U∩E).card=U.card := by exact_mod_cast he
    have hler : ((U∩E).card : ℝ)≤E.card := by exact_mod_cast hle
    rw [hcard]
    linarith
  calc
    c*((U.card : ℝ)-E.card) ≤ c*(S.card : ℝ) := mul_le_mul_of_nonneg_left hce hc
    _ = ∑ t∈S, c := by simp [mul_comm]
    _ ≤ ∑ t∈S, w t := Finset.sum_le_sum (fun t ht => hweight t (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp ht).2)
    _ ≤ ∑ t∈T, w t := Finset.sum_le_sum_of_subset_of_nonneg hs (fun t ht _ => hw t ht)

end TotientAsymptotic.FiniteMap

end

end OAI
