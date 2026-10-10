import Mathlib
import OAI.Combinatorics.KMedian.Process.PhysicalPotential

namespace OAI

section
section
namespace MetricKMedian.Completion
open Finset PhysicalPotential
variable {J I : Type*} [DecidableEq J] [DecidableEq I]

theorem radius_packing (U : Finset J) (R : J → ℝ) (B : J → Finset I)
    (hB : ∀ j ∈ U, (B j).Nonempty) :
    ∃ A : Finset J, A ⊆ U ∧ (↑A : Set J).PairwiseDisjoint B ∧
      ∀ j ∈ U, ∃ a ∈ A, R a ≤ R j ∧ ¬Disjoint (B j) (B a) := by
  revert hB
  refine Finset.strongInductionOn U ?_
  intro U ih hB
  by_cases hu : U.Nonempty
  · obtain ⟨j0,hj0,hr0⟩ := U.exists_min_image R hu
    let V := U.filter (fun j => Disjoint (B j0) (B j))
    have hVU : V ⊆ U := filter_subset _ _
    have hjV : j0 ∉ V := by
      intro hj
      have hdis := (mem_filter.mp hj).2
      obtain ⟨i,hi⟩ := hB j0 hj0
      exact disjoint_left.mp hdis hi hi
    have hVU' : V ⊂ U := Finset.ssubset_iff_subset_ne.mpr ⟨hVU, fun he => hjV (he ▸ hj0)⟩
    obtain ⟨A,hAV,hAd,hcover⟩ := ih V hVU' (fun j hj => hB j (hVU hj))
    refine ⟨insert j0 A, insert_subset hj0 (hAV.trans hVU), ?_, ?_⟩
    · rw [coe_insert]
      apply hAd.insert
      intro a ha _
      exact (mem_filter.mp (hAV ha)).2
    · intro j hj
      by_cases hjv : j ∈ V
      · obtain ⟨a,ha,hr,hd⟩ := hcover j hjv
        exact ⟨a,mem_insert_of_mem ha,hr,hd⟩
      · have hnot : ¬Disjoint (B j0) (B j) := fun hd => hjv (mem_filter.mpr ⟨hj,hd⟩)
        exact ⟨j0,mem_insert_self _ _,hr0 j hj,fun hd => hnot hd.symm⟩
  · have he : U=∅ := not_nonempty_iff_eq_empty.mp hu
    subst U
    refine ⟨∅,Subset.rfl,?_,?_⟩
    · simp
    · simp

omit [DecidableEq J] in
                                                                           
theorem packing_mass {g : ℝ} (hg : 0 ≤ g) (A : Finset J) (B : J → Finset I)
    (active : Finset I) (hB : ∀ j ∈ A, B j ⊆ active)
    (hdis : (↑A : Set J).PairwiseDisjoint B)
    (hunit : ∀ j ∈ A, 1 ≤ mass g (B j)) :
    (A.card:ℝ) ≤ mass g active := by
  have hu : A.biUnion B ⊆ active := by
    intro i hi
    obtain ⟨j,hj,hij⟩ := mem_biUnion.mp hi
    exact hB j hj hij
  have he : (∑ j ∈ A, mass g (B j))=mass g (A.biUnion B) := by
    simp only [mass, card_biUnion hdis, Nat.cast_sum, mul_sum]
  have hh := sum_le_sum hunit
  simp only [sum_const, nsmul_eq_mul, mul_one] at hh
  exact (hh.trans_eq he).trans (mass_mono hg hu)

omit [DecidableEq J] [DecidableEq I] in

theorem packed_connection {X : Type*} [PseudoMetricSpace X]
    (client : J → X) (location : I → X) (R : J → ℝ) (B : J → Finset I)
    (hR : ∀ j i, i ∈ B j → dist (client j) (location i) ≤ R j)
    {j a : J} (hr : R a ≤ R j) (hinter : ¬Disjoint (B j) (B a))
    {opened : I} (ho : opened ∈ B a) :
    dist (client j) (location opened) ≤ 3*R j := by
  obtain ⟨i,hij,hia⟩ := not_disjoint_iff.mp hinter
  have h1 := dist_triangle (client j) (location i) (client a)
  have h2 := dist_triangle (client j) (client a) (location opened)
  have hi := hR j i hij
  have ha := hR a i hia
  have ho' := hR a opened ho
  rw [dist_comm (location i) (client a)] at h1
  linarith only [h1,h2,hi,ha,ho',hr]

end MetricKMedian.Completion
end
end

end OAI
