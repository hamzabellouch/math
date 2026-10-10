import Mathlib
import OAI.Combinatorics.KMedian.Model
import OAI.Combinatorics.KMedian.Instance

namespace OAI

section
section
namespace MetricKMedian
open Finset

def rationalNearest (I : Instance) (j : Fin I.n) (S : Finset (Fin I.n)) : ℚ :=
  if h : S.Nonempty then
    (S.image (I.distance j)).min' (h.image _)
  else 0

def rationalCost (I : Instance) (S : Finset (Fin I.n)) : ℚ :=
  ∑ j ∈ I.clients, rationalNearest I j S

namespace Instance

theorem cast_rationalNearest (I : Instance) (j : Fin I.n) (S : Finset (Fin I.n)) :
    (rationalNearest I j S:ℝ)=nearest I j S := by
  by_cases hS : S.Nonempty
  · rw [rationalNearest,dite_eq_left hS,nearest,dite_eq_left hS]
    apply le_antisymm
    · apply le_min'
      intro q hq
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hq
      exact_mod_cast min'_le _ _ (mem_image_of_mem (I.distance j) hi)
    · obtain ⟨i,hi,he⟩ := mem_image.mp (min'_mem (S.image (I.distance j)) (hS.image _))
      rw [← he]
      exact min'_le _ _ (mem_image_of_mem (fun i => (I.distance j i:ℝ)) hi)
  · simp only [rationalNearest,dite_eq_right hS,nearest,Rat.cast_zero]

theorem cast_rationalCost (I : Instance) (S : Finset (Fin I.n)) :
    (rationalCost I S:ℝ)=cost I S := by
  simp only [rationalCost,Rat.cast_sum,I.cast_rationalNearest,cost]

theorem nearest_antitone (I : Instance) (j : Fin I.n)
    {S T : Finset (Fin I.n)} (hS : S.Nonempty) (hST : S ⊆ T) :
    nearest I j T ≤ nearest I j S := by
  obtain ⟨i,hi,he⟩ := I.nearest_attained j S hS
  rw [he]
  exact I.nearest_le j (hST hi)

theorem cost_antitone (I : Instance) {S T : Finset (Fin I.n)}
    (hS : S.Nonempty) (hST : S ⊆ T) : cost I T ≤ cost I S :=
  sum_le_sum (fun j _ => I.nearest_antitone j hS hST)

theorem rationalCost_antitone (I : Instance) {S T : Finset (Fin I.n)}
    (hS : S.Nonempty) (hST : S ⊆ T) : rationalCost I T ≤ rationalCost I S := by
  have hh := I.cost_antitone hS hST
  rw [← I.cast_rationalCost T,← I.cast_rationalCost S] at hh
  exact_mod_cast hh

theorem deletion_cost_nonneg (I : Instance) (S : Finset (Fin I.n))
    (hk : I.k < S.card) (i : Fin I.n) :
    0 ≤ rationalCost I (S.erase i)-rationalCost I S := by
  have hne : (S.erase i).Nonempty := by
    apply card_pos.mp
    have hkpos := I.k_pos
    by_cases hi : i ∈ S
    · rw [card_erase_of_mem hi]
      omega
    · rw [erase_eq_of_notMem hi]
      omega
  exact sub_nonneg.mpr (I.rationalCost_antitone hne (erase_subset _ _))

end Instance
end MetricKMedian
end
end

end OAI
