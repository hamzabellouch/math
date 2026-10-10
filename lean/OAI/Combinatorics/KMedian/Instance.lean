import Mathlib
import OAI.Combinatorics.KMedian.Model

namespace OAI

section
section
namespace MetricKMedian
open Finset

namespace Instance

@[instance_reducible] def pseudoMetric (I : Instance) : PseudoMetricSpace (Fin I.n) where
  dist i j := (I.distance i j:ℝ)
  dist_self i := by rw [(I.distance_eq_zero i i).mpr rfl, Rat.cast_zero]
  dist_comm i j := by rw [I.distance_symm i j]
  dist_triangle i j h := by exact_mod_cast I.distance_triangle i j h

theorem facilities_nonempty (I : Instance) : I.facilities.Nonempty :=
  card_pos.mp (I.k_pos.trans I.k_le)

theorem feasible_nonempty (I : Instance) : (feasibleSets I).Nonempty := by
  obtain ⟨i,hi⟩ := I.facilities_nonempty
  refine ⟨{i},mem_filter.mpr ⟨mem_powerset.mpr ?_,singleton_nonempty _,?_⟩⟩
  · exact singleton_subset_iff.mpr hi
  · simpa only [card_singleton] using I.k_pos

theorem mem_feasible (I : Instance) (S : Finset (Fin I.n)) :
    S ∈ feasibleSets I ↔ S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ I.k := by
  simp only [feasibleSets,mem_filter,mem_powerset]

theorem nearest_nonneg (I : Instance) (j : Fin I.n) (S : Finset (Fin I.n)) :
    0 ≤ nearest I j S := by
  unfold nearest
  split_ifs with hS
  · apply le_min'
    intro q hq
    obtain ⟨i,_,rfl⟩ := mem_image.mp hq
    exact_mod_cast I.distance_nonneg j i
  · exact le_rfl

theorem nearest_le (I : Instance) (j : Fin I.n) {S : Finset (Fin I.n)}
    {i : Fin I.n} (hi : i ∈ S) : nearest I j S ≤ (I.distance j i:ℝ) := by
  rw [nearest,dite_eq_left (show S.Nonempty from ⟨i,hi⟩)]
  exact min'_le _ _ (mem_image_of_mem _ hi)

theorem nearest_attained (I : Instance) (j : Fin I.n) (S : Finset (Fin I.n))
    (hS : S.Nonempty) : ∃ i ∈ S, nearest I j S=(I.distance j i:ℝ) := by
  have hm := min'_mem (S.image (fun i => (I.distance j i:ℝ))) (hS.image _)
  obtain ⟨i,hi,he⟩ := mem_image.mp hm
  exact ⟨i,hi,by rw [nearest,dite_eq_left hS]; exact he.symm⟩

theorem cost_nonneg (I : Instance) (S : Finset (Fin I.n)) : 0 ≤ cost I S :=
  sum_nonneg (fun j _ => I.nearest_nonneg j S)

theorem cost_le_assignment (I : Instance) (S : Finset (Fin I.n))
    (a : ↥I.clients → Fin I.n) (ha : ∀ j, a j ∈ S) :
    cost I S ≤ ∑ j : ↥I.clients, (I.distance j (a j):ℝ) := by
  rw [cost,← sum_coe_sort]
  exact sum_le_sum (fun j _ => I.nearest_le j (ha j))

theorem optimum_attained (I : Instance) :
    ∃ S, S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ I.k ∧ cost I S=optimum I := by
  have hS := I.feasible_nonempty
  have hm := min'_mem ((feasibleSets I).image (cost I)) (hS.image _)
  obtain ⟨S,hSf,he⟩ := mem_image.mp hm
  obtain ⟨hsub,hne,hcard⟩ := (I.mem_feasible S).mp hSf
  exact ⟨S,hsub,hne,hcard,by rw [optimum,dite_eq_left hS]; exact he⟩

theorem optimum_nonneg (I : Instance) : 0 ≤ optimum I := by
  obtain ⟨S,_,_,_,he⟩ := I.optimum_attained
  rw [← he]
  exact I.cost_nonneg S

theorem optimum_le (I : Instance) {S : Finset (Fin I.n)}
    (hS : S ⊆ I.facilities) (hne : S.Nonempty) (hk : S.card ≤ I.k) : optimum I ≤ cost I S := by
  rw [optimum,dite_eq_left I.feasible_nonempty]
  exact min'_le _ _ (mem_image_of_mem _ ((I.mem_feasible S).mpr ⟨hS,hne,hk⟩))

theorem cost_eq_zero_iff (I : Instance) (S : Finset (Fin I.n)) (hne : S.Nonempty) :
    cost I S=0 ↔ I.clients ⊆ S := by
  constructor
  · intro hc j hj
    have hj0 : nearest I j S=0 := (sum_eq_zero_iff_of_nonneg
      (fun j _ => I.nearest_nonneg j S)).mp hc j hj
    obtain ⟨i,hi,he⟩ := I.nearest_attained j S hne
    have hd : I.distance j i=0 := by exact_mod_cast (he.symm.trans hj0)
    exact (I.distance_eq_zero j i).mp hd ▸ hi
  · intro hsub
    apply sum_eq_zero
    intro j hj
    apply le_antisymm _ (I.nearest_nonneg j S)
    have hh := I.nearest_le j (hsub hj)
    simpa only [(I.distance_eq_zero j j).mpr rfl,Rat.cast_zero] using hh

theorem optimum_eq_zero_iff (I : Instance) :
    optimum I=0 ↔ I.clients ⊆ I.facilities ∧ I.clients.card ≤ I.k := by
  constructor
  · intro hz
    obtain ⟨S,hSF,hne,hSk,hcost⟩ := I.optimum_attained
    have hJS := (I.cost_eq_zero_iff S hne).mp (hcost.trans hz)
    exact ⟨hJS.trans hSF,(card_le_card hJS).trans hSk⟩
  · rintro ⟨hJF,hJk⟩
    by_cases hJ : I.clients.Nonempty
    · apply le_antisymm _ I.optimum_nonneg
      exact (I.optimum_le hJF hJ hJk).trans_eq ((I.cost_eq_zero_iff I.clients hJ).mpr Subset.rfl)
    · have he := not_nonempty_iff_eq_empty.mp hJ
      obtain ⟨S,hSF,hne,hSk,_⟩ := I.optimum_attained
      apply le_antisymm _ I.optimum_nonneg
      exact (I.optimum_le hSF hne hSk).trans_eq (by simp [cost,he])

end Instance
end MetricKMedian
end
end

end OAI
