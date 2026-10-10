import OAI.Combinatorics.Ryser.Construction.FiniteOutsideAction
import OAI.Combinatorics.Ryser.Construction.CoverCounting
import OAI.Combinatorics.Ryser.Construction.CoverBudget
import OAI.Combinatorics.Ryser.Construction.DeletionUnionOutside

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [DecidableEq G]
variable [Fintype F] [Fintype G]

theorem not_isCover_of_finite_outside_lines
    (data : ConfigurationData k F G) (B : Finset (AffineLine F))
    (p : Point F) (I : Finset G) (lines : G → AffineLine F)
    (hbase : ∀ i, Function.Injective (data.base i))
    (houtside : ∀ i w, p ≠ data.base i w)
    (hthrough : ∀ i ∈ I, Incidence p (lines i))
    (haltered : ∀ i ∈ I, (lines i).1 ∈ data.altered i)
    (hdensity : ∀ i ∈ I,
      5 ≤ (data.retained.filter (fun w => Incidence (data.base i w) (lines i))).card)
    (hIcard : I.card = (B ∩ affinePencil (Sum.inl p)).card)
    (hthin : OffPencilThin data p)
    (C : Finset (Vertex (k := k) data.altered))
    (hforced : forcedPencilVertices data B (Sum.inl p) ⊆ C)
    (hCcard : C.card ≤ Fintype.card F) :
    ¬ IsCover (hypergraph data) C := by
  classical
  intro hC
  obtain ⟨S, hS, hSout⟩ := exists_five_selection I
    (fun i => data.retained.filter (fun w => Incidence (data.base i w) (lines i)))
    hdensity
  have hretained : ∀ i ∈ I, S i ⊆ data.retained := by
    intro i hi w hw
    exact (Finset.mem_filter.mp ((hS i hi).1 hw)).1
  have honlines : ∀ i ∈ I, ∀ w ∈ S i, Incidence (data.base i w) (lines i) := by
    intro i hi w hw
    exact (Finset.mem_filter.mp ((hS i hi).1 hw)).2
  have hselectedOutside : ∀ i ∈ I, ∀ w ∈ S i, p ≠ data.base i w := by
    intro i _ w _
    exact houtside i w
  have hsize : ∀ i, (S i).card ≤ 5 := by
    intro i
    by_cases hi : i ∈ I
    · exact (hS i hi).2.le
    · rw [hSout i hi, Finset.card_empty]
      exact Nat.zero_le _
  let E := selectedPositions I S
  let R := C \ forcedPencilVertices data B (Sum.inl p)
  have hnotForced : ∀ x ∈ E, ∀ v ∈ exceptionalEdge data x.1 x.2,
      v ∉ forcedPencilVertices data B (Sum.inl p) := by
    intro x hx v hv hvforced
    obtain ⟨hi, hw⟩ := mem_selectedPositions.mp hx
    obtain ⟨ell, hell, rfl⟩ := Finset.mem_image.mp hvforced
    have hpell : Incidence p ell :=
      (mem_affinePencil (Sum.inl p) ell).mp (Finset.mem_sdiff.mp hell).1
    have hjoin := joinDirection_mem_altered_of_incident_line data x.1 p x.2
      (lines x.1) (houtside x.1 x.2) (hthrough x.1 hi)
      (honlines x.1 hi x.2 hw) (haltered x.1 hi)
    exact ordinaryVertex_notMem_exceptionalEdge_of_altered_join data p x.1 x.2
      (houtside x.1 x.2) hjoin ell hpell hv
  have hcover : ∀ x ∈ E, ∃ v ∈ R, v ∈ exceptionalEdge data x.1 x.2 := by
    intro x hx
    obtain ⟨hi, hw⟩ := mem_selectedPositions.mp hx
    have hedge : exceptionalEdge data x.1 x.2 ∈ hypergraph data :=
      (mem_hypergraph data _).mpr (Or.inr ⟨x.1, x.2, hretained x.1 hi hw, rfl⟩)
    obtain ⟨v, hvC, hv⟩ := hC _ hedge
    exact ⟨v, Finset.mem_sdiff.mpr ⟨hvC, hnotForced x hx v hv⟩, hv⟩
  have hcapacity : ∀ v ∈ R,
      (E.filter (fun x => v ∈ exceptionalEdge data x.1 x.2)).card ≤ 5 := by
    intro v _
    exact selectedPositions_hit_card_le_five data p I lines S hbase hretained
      hselectedOutside hthrough haltered honlines hsize hthin v
  have hcount : E.card ≤ 5 * R.card :=
    card_le_mul_resource_card E R
      (fun v x => v ∈ exceptionalEdge data x.1 x.2) 5 hcover hcapacity
  have hEcard : E.card = 5 * I.card :=
    card_selectedPositions I S 5 (fun i hi => (hS i hi).2)
  have hpositive : 0 < I.card := by
    rw [hIcard]
    exact finite_deletedPencil_card_pos data B p C hforced hCcard
  have hbudget : R.card ≤ I.card - 1 := by
    rw [hIcard]
    exact finite_additional_card_le data B p C hforced hCcard
  omega

variable [Fintype k]

theorem not_isCover_of_finite_outside_placedSubplanes
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a)
    (hsep : DeletionSeparated σ M b a)
    (data : ConfigurationData k F G)
    (hdataBase : ∀ i, data.base i = placedPoint σ (M i) (b i))
    (hdataAltered : ∀ i, data.altered i = alteredDirections σ (M i))
    (hdataRetained : data.retained = retainedPoints a)
    (p : Point F) (hout : ∀ i, p ∉ placedSubplane σ (M i) (b i))
    (hthin : OffPencilThin data p)
    (C : Finset (Vertex (k := k) data.altered))
    (hforced : forcedPencilVertices data (allDeletedLines σ M b a) (Sum.inl p) ⊆ C)
    (hCcard : C.card ≤ Fintype.card F) :
    ¬ IsCover (hypergraph data) C := by
  classical
  let I := activeDeletionGroups σ M b a p
  let lines : G → AffineLine F := fun i =>
    if hi : i ∈ I then activeDeletionLine σ M b a p ⟨i, hi⟩ else (none, 0)
  have hline (i : G) (hi : i ∈ I) :
      lines i = activeDeletionLine σ M b a p ⟨i, hi⟩ := by
    simp only [lines, dite_eq_left hi]
  apply not_isCover_of_finite_outside_lines data (allDeletedLines σ M b a)
    p I lines
  · intro i
    rw [hdataBase i]
    exact placedPoint_injective σ (M i) (b i)
  · intro i w
    rw [hdataBase i]
    intro hpw
    exact hout i ((mem_placedSubplane_iff σ (M i) (b i) p).mpr ⟨w, hpw.symm⟩)
  · intro i hi
    rw [hline i hi]
    exact incidence_activeDeletionLine σ M b a p ⟨i, hi⟩
  · intro i hi
    rw [hline i hi, hdataAltered i]
    exact ((mem_deletedLines σ (M i) (b i) a _).mp
      (activeDeletionLine_mem σ M b a p ⟨i, hi⟩)).1
  · intro i hi
    rw [hdataRetained, hdataBase i, hline i hi]
    have hd := activeDeletionLine_many_placedRetainedPoints σ M b a p ha ⟨i, hi⟩
    rw [Finset.filter_image,
      Finset.card_image_of_injective _ (placedPoint_injective σ (M i) (b i))] at hd
    exact hd
  · exact (card_allDeletedLines_inter_affinePencil_eq_card_activeDeletionGroups
      σ M b a p hsep hout).symm
  · exact hthin
  · exact hforced
  · exact hCcard

end RyserCoveringCounterexample.Construction

end

end OAI
