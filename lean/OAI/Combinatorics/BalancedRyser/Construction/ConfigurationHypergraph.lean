import OAI.Combinatorics.BalancedRyser.Construction.ConstructionRepresentationLemmas
import OAI.Combinatorics.BalancedRyser.Construction.PartitionHypergraph
import OAI.Combinatorics.BalancedRyser.Probability.BlockIntersection
import OAI.Combinatorics.BalancedRyser.Probability.ConfigurationBlockCardinality
import OAI.Combinatorics.BalancedRyser.Probability.PointLabelInjective

namespace OAI

namespace Balanced.Configuration

open BlockPartitions

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

noncomputable def directionEquiv : Direction F ≃ Fin (Fintype.card F + 1) :=
  Fintype.equivFinOfCardEq (by simp [Direction])

noncomputable def blockLabelEquiv (hV : C.Valid) (hC : C.Compatible)
    (hq : 4 ≤ Fintype.card F) (d : Direction F) :
    {b // b ∈ C.labelsInDirection d} ≃ Fin (Fintype.card F + 1) :=
  Fintype.equivFinOfCardEq (by
    rw [Fintype.card_coe]
    exact C.labelsInDirection_card hV hC hq d)

noncomputable def constructedHypergraph (hV : C.Valid) (hC : C.Compatible)
    (hq : 4 ≤ Fintype.card F) :
    PartiteHypergraph (Fintype.card F + 1) (Fintype.card F + 1) :=
  partitionHypergraph (directionEquiv (F := F)) (C.blockLabelEquiv hV hC hq)
    (pointLabel hV hC)

theorem pointLabel_surjective (hV : C.Valid) (hC : C.Compatible)
    {ρ : ℝ} {B : ℕ} (hρ : 0 < ρ) (hO : C.Occupancy ρ B) (d : Direction F) :
    Function.Surjective (pointLabel hV hC d) := by
  classical
  intro b
  have hb : C.IsBlockLabel b.val :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp b.property).1).2
  obtain ⟨p, hp⟩ := C.blockPoints_nonempty hV hρ hO b.val hb
  let x : {p // p ∈ C.points} := ⟨p, C.blockPoints_subset_points b.val hp⟩
  exact ⟨x, (pointLabel_eq_iff hV hC d x b).mpr hp⟩

theorem pointLabel_agrees (hV : C.Valid) (hC : C.Compatible)
    (p q : {p // p ∈ C.points}) :
    ∃ d, pointLabel hV hC d p = pointLabel hV hC d q := by
  obtain ⟨b, hb, hp, hq⟩ := C.pair_common_block hV hC p.property q.property
  let d := blockDirection b
  have hbDir : b ∈ C.labelsInDirection d :=
    Finset.mem_filter.mpr ⟨hb, rfl⟩
  let b' : {b // b ∈ C.labelsInDirection d} := ⟨b, hbDir⟩
  refine ⟨d, ?_⟩
  exact ((pointLabel_eq_iff hV hC d p b').mpr hp).trans
    ((pointLabel_eq_iff hV hC d q b').mpr hq).symm

theorem constructedHypergraph_nonisolated (hV : C.Valid) (hC : C.Compatible)
    (hq : 4 ≤ Fintype.card F) {ρ : ℝ} {B : ℕ}
    (hρ : 0 < ρ) (hO : C.Occupancy ρ B) :
    (C.constructedHypergraph hV hC hq).Nonisolated :=
  partitionHypergraph_nonisolated _ _ _ (C.pointLabel_surjective hV hC hρ hO)

theorem constructedHypergraph_intersecting (hV : C.Valid) (hC : C.Compatible)
    (hq : 4 ≤ Fintype.card F) :
    (C.constructedHypergraph hV hC hq).Intersecting := by
  have : Nonempty {p // p ∈ C.points} := C.points_nonempty.to_subtype
  exact partitionHypergraph_intersecting _ _ _ (C.pointLabel_agrees hV hC)

theorem constructedHypergraph_represents (hV : C.Valid) (hC : C.Compatible)
    (hq : 4 ≤ Fintype.card F) {ρ : ℝ} {B : ℕ}
    (hρ : ρ < 1) (hO : C.Occupancy ρ B)
    (hsize : 2 * (1 + (B : ℝ)) < ρ * Fintype.card F) :
    C.Represents (C.constructedHypergraph hV hC hq) := by
  let eD := directionEquiv (F := F)
  let eL := C.blockLabelEquiv hV hC hq
  have hinj := pointLabel_injective_of_occupancy hV hC hρ hO hsize
  refine ⟨eD, eL, partitionHypergraph_edgeEquiv eD eL (pointLabel hV hC) hinj, ?_⟩
  intro p d b
  change p.val ∈ C.blockPoints b.val ↔
    encodeAssignment eD eL (pointLabel hV hC) p (eD d) = eL d b
  rw [encodeAssignment_apply_index]
  exact (pointLabel_eq_iff hV hC d p b).symm.trans (eL d).apply_eq_iff_eq.symm

theorem constructedHypergraph_hasCoverNumber (hV : C.Valid) (hC : C.Compatible)
    (hq : 4 ≤ Fintype.card F)
    (hcover : ∀ A : Finset (BlockLabel F), A ⊆ C.blockLabels →
      C.points ⊆ A.biUnion C.blockPoints → Fintype.card F + 1 ≤ A.card) :
    (C.constructedHypergraph hV hC hq).HasCoverNumber (Fintype.card F + 1) := by
  classical
  apply partitionHypergraph_hasCoverNumber
  intro D hD
  let A : Finset (BlockLabel F) := D.image (fun v => v.2.val)
  have hA : A ⊆ C.blockLabels := by
    intro b hb
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
    exact (Finset.mem_filter.mp v.2.property).1
  have hAcovers : C.points ⊆ A.biUnion C.blockPoints := by
    intro p hp
    obtain ⟨d, hd⟩ := hD ⟨p, hp⟩
    refine Finset.mem_biUnion.mpr ⟨(pointLabel hV hC d ⟨p, hp⟩).val, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨⟨d, pointLabel hV hC d ⟨p, hp⟩⟩, hd, rfl⟩
    · exact pointLabel_mem hV hC d ⟨p, hp⟩
  exact (hcover A hA hAcovers).trans Finset.card_image_le

theorem exists_constructed_hypergraph (hV : C.Valid) (hC : C.Compatible)
    (hq : 4 ≤ Fintype.card F) {ρ : ℝ} {B : ℕ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hO : C.Occupancy ρ B)
    (hsize : 2 * (1 + (B : ℝ)) < ρ * Fintype.card F) :
    ∃ H : PartiteHypergraph (Fintype.card F + 1) (Fintype.card F + 1),
      C.Represents H ∧ H.Intersecting ∧ H.Nonisolated := by
  exact ⟨C.constructedHypergraph hV hC hq,
    C.constructedHypergraph_represents hV hC hq hρ1 hO hsize,
    C.constructedHypergraph_intersecting hV hC hq,
    C.constructedHypergraph_nonisolated hV hC hq hρ0 hO⟩

end Balanced.Configuration

end OAI
