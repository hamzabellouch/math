import Mathlib
import OAI.Probability.CriticalPercolation.Growth.HomogeneousGeometry

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
variable {X : Type*} (W : Geometry X)

lemma packing_card_bound (J : Finset X) (r : ℕ)
    (hJ : (J:Set X).PairwiseDisjoint (fun a => W.around a r))
    (F : Finset X) (hF : ∀ a∈J, W.around a r⊆F) :
    J.card*(W.ball r).card≤F.card := by
  calc
    _ = ∑ a∈J, (W.around a r).card := by simp only [W.card_around,Finset.sum_const_nat]
    _ = (J.biUnion (fun a => W.around a r)).card := (Finset.card_biUnion hJ).symm
    _ ≤ _ := Finset.card_le_card (by
      intro x hx
      obtain ⟨a,ha,hx⟩ := Finset.mem_biUnion.mp hx
      exact hF a ha hx)

theorem exists_word_ball_packing (R r : ℕ) :
    ∃ J : Finset X, J⊆W.ball R ∧
      (J:Set X).PairwiseDisjoint (fun a => W.around a r) ∧
      J.card*(W.ball r).card≤(W.ball (R+r)).card ∧
      ∀ x∈W.ball R, ∃ a∈J, x∈W.around a (2*r) := by
  let C : Finset (Finset X) := (W.ball R).powerset.filter
    (fun (J : Finset X) => (J:Set X).PairwiseDisjoint (fun a => W.around a r))
  obtain ⟨J,hJmax⟩ := C.exists_maximal <| Finset.filter_nonempty_iff.mpr
    ⟨∅,Finset.empty_mem_powerset _,by simp⟩
  simp only [C,Finset.mem_filter,Finset.mem_powerset] at hJmax
  obtain ⟨hJR,hJ⟩ := hJmax.1
  refine ⟨J,hJR,hJ,W.packing_card_bound J r hJ _ (fun a ha => W.around_subset_ball (hJR ha)),?_⟩
  intro x hx
  by_cases hxJ : x∈J
  · exact ⟨x,hxJ,W.self_mem_around _ _⟩
  by_cases! hd : ∀ a∈J, Disjoint (W.around x r) (W.around a r)
  · exact False.elim (hJmax.not_gt
      ⟨Finset.insert_subset_iff.mpr ⟨hx,hJR⟩,by
        rw [Finset.coe_insert]
        exact hJ.insert (fun a ha _ => hd a ha)⟩
      (Finset.ssubset_insert hxJ))
  · obtain ⟨a,ha,hd⟩ := hd
    obtain ⟨y,hyx,hya⟩ := Finset.not_disjoint_iff.mp hd
    refine ⟨a,ha,?_⟩
    simpa only [show r+r=2*r by omega] using W.mem_around_add hya (W.mem_around_symm hyx)

lemma packing_overlap (J : Finset X) (r t K : ℕ)
    (hJ : (J:Set X).PairwiseDisjoint (fun a => W.around a r))
    (hvol : (W.ball (t+r)).card≤K*(W.ball r).card) (x : X) :
    (J.filter (fun a => x∈W.around a t)).card≤K := by
  let I := J.filter (fun a => x∈W.around a t)
  have hIJ : I⊆J := Finset.filter_subset _ _
  have hId : (I:Set X).PairwiseDisjoint (fun a => W.around a r) := fun a ha b hb hab => hJ (hIJ ha) (hIJ hb) hab
  have hsub (a : X) (ha : a∈I) : W.around a r⊆W.around x (t+r) := by
    intro y hy
    exact W.mem_around_add (W.mem_around_symm (Finset.mem_filter.mp ha).2) hy
  have hh := W.packing_card_bound I r hId (W.around x (t+r)) hsub
  rw [W.card_around x (t+r)] at hh
  exact le_of_mul_le_mul_right (hh.trans hvol) (W.ball_card_pos r)

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
