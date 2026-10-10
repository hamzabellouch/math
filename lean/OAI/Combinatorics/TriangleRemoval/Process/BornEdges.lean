import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.BirthGraph

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.BirthGraph
open scoped BigOperators

variable {N : ℕ} (B : BirthGraph N)

def bornEdges (v : Fin N) : Finset (Finset (Fin N)) :=
  (B.older v).image (fun u => {u, v})

def backEdges (Z : Finset (Fin N)) : Finset (Finset (Fin N)) :=
  Z.biUnion B.bornEdges

theorem pair_injective_on_older (v : Fin N) :
    Set.InjOn (fun u : Fin N => ({u, v} : Finset (Fin N))) (B.older v) := by
  intro a ha b hb hab
  have hm : a ∈ ({b, v} : Finset (Fin N)) := by
    change ({a, v} : Finset (Fin N)) = {b, v} at hab
    rw [← hab]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm
  · exact hm
  · exact False.elim ((ne_of_lt (B.older_lt v a ha)) hm)

@[simp] theorem bornEdges_card (v : Fin N) : (B.bornEdges v).card = (B.older v).card :=
  Finset.card_image_of_injOn (B.pair_injective_on_older v)

theorem bornEdges_disjoint {v w : Fin N} (hvw : v ≠ w) :
    Disjoint (B.bornEdges v) (B.bornEdges w) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp hf
  have hv : v ∈ ({b, w} : Finset (Fin N)) := hbe.symm ▸ (by simp)
  have hw : w ∈ ({a, v} : Finset (Fin N)) := hbe ▸ (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv hw
  have hvb : v = b := hv.resolve_right hvw
  have hwa : w = a := hw.resolve_right hvw.symm
  have hlt := B.older_lt v a ha
  have hlt' := B.older_lt w b hb
  subst a b
  exact (not_lt_of_gt hlt) hlt'

theorem backEdges_card (Z : Finset (Fin N)) :
    (B.backEdges Z).card = ∑ v ∈ Z, (B.older v).card := by
  rw [backEdges, Finset.card_biUnion]
  · simp only [bornEdges_card]
  · intro a _ b _ hab
    exact B.bornEdges_disjoint hab

theorem backEdges_mem_pair {Z : Finset (Fin N)} {e : Finset (Fin N)}
    (he : e ∈ B.backEdges Z) :
    ∃ v ∈ Z, ∃ u ∈ B.older v, e = {u, v} := by
  obtain ⟨v, hv, he⟩ := Finset.mem_biUnion.mp he
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp he
  exact ⟨v, hv, u, hu, rfl⟩

theorem backEdges_card_le (Z : Finset (Fin N)) : (B.backEdges Z).card ≤ 2 * Z.card := by
  rw [backEdges_card]
  calc
    _ ≤ ∑ _v ∈ Z, 2 := Finset.sum_le_sum (fun v _ => B.older_card v)
    _ = _ := by simp [mul_comm]

theorem backEdges_card_eq (Z : Finset (Fin N)) (h : ∀ v ∈ Z, (B.older v).card = 2) :
    (B.backEdges Z).card = 2 * Z.card := by
  rw [backEdges_card]
  simp only [Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul, mul_comm]

def inducedEdges (U : Finset (Fin N)) : Finset (Finset (Fin N)) :=
  (B.backEdges U).filter (fun e => e ⊆ U)

theorem inducedEdges_eq (U : Finset (Fin N)) : B.inducedEdges U =
    U.biUnion (fun v => ((B.older v) ∩ U).image (fun u => {u, v})) := by
  ext e
  simp only [inducedEdges, backEdges, bornEdges, Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_image, Finset.mem_inter]
  constructor
  · rintro ⟨⟨v, hv, u, hu, rfl⟩, hs⟩
    exact ⟨v, hv, u, ⟨hu, hs (by simp)⟩, rfl⟩
  · rintro ⟨v, hv, u, ⟨hu, huU⟩, rfl⟩
    refine ⟨⟨v, hv, u, hu, rfl⟩, ?_⟩
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨huU, hv⟩

theorem inducedEdges_card_le (U : Finset (Fin N)) :
    (B.inducedEdges U).card ≤ ∑ v ∈ U, ((B.older v) ∩ U).card := by
  rw [inducedEdges_eq]
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum ?_)
  intro v _
  exact Finset.card_image_le

theorem inducedEdges_sparse (U : Finset (Fin N)) (hU : U.Nonempty) :
    (B.inducedEdges U).card + 2 ≤ 2 * U.card := by
  let v := U.min' hU
  have hv : v ∈ U := Finset.min'_mem U hU
  have hzero : (B.older v) ∩ U = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    have hu' := Finset.mem_inter.mp hu
    exact (not_le_of_gt (B.older_lt v u hu'.1)) (Finset.min'_le U u hu'.2)
  have hsum : (∑ x ∈ U, ((B.older x) ∩ U).card) ≤ 2 * (U.card - 1) := by
    rw [← Finset.sum_erase_add _ _ hv, hzero, Finset.card_empty, add_zero]
    calc
      _ ≤ ∑ _x ∈ U.erase v, 2 := by
        apply Finset.sum_le_sum
        intro x _
        exact (Finset.card_le_card Finset.inter_subset_left).trans (B.older_card x)
      _ = _ := by simp [Finset.card_erase_of_mem hv, mul_comm]
  have hpos : 1 ≤ U.card := hU.card_pos
  have hh := (B.inducedEdges_card_le U).trans hsum
  omega

theorem induced_plus_one_sparse (U : Finset (Fin N)) (a b : Fin N) :
    ((insert ({a, b} : Finset (Fin N)) (B.backEdges Finset.univ)).filter
      (fun e => e ⊆ U)).card ≤ 2 * U.card := by
  by_cases hU : U.Nonempty
  · have hs : ((insert ({a, b} : Finset (Fin N)) (B.backEdges Finset.univ)).filter
        (fun e => e ⊆ U)) ⊆ insert {a, b} (B.inducedEdges U) := by
      intro e he
      obtain ⟨he, heU⟩ := Finset.mem_filter.mp he
      rcases Finset.mem_insert.mp he with he | he
      · exact Finset.mem_insert.mpr (Or.inl he)
      · obtain ⟨v, _, u, hu, heu⟩ := B.backEdges_mem_pair he
        apply Finset.mem_insert.mpr ∘ Or.inr
        apply Finset.mem_filter.mpr
        refine ⟨?_, heU⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨v, heU (by rw [heu]; simp), ?_⟩
        exact Finset.mem_image.mpr ⟨u, hu, heu.symm⟩
    have hcard := (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)
    have hsp := B.inducedEdges_sparse U hU
    omega
  · have hzero : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
    subst U
    have hempty : ((insert ({a, b} : Finset (Fin N)) (B.backEdges Finset.univ)).filter
        (fun e => e ⊆ ∅)).card = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨he, hs⟩ := Finset.mem_filter.mp he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact Finset.notMem_empty a (hs (by simp))
      · obtain ⟨v, _, u, _, heu⟩ := B.backEdges_mem_pair he
        exact Finset.notMem_empty v (hs (by rw [heu]; simp))
    rw [hempty]
    exact Nat.zero_le _

end SharpTerminalLeave.BirthGraph

end

end OAI
