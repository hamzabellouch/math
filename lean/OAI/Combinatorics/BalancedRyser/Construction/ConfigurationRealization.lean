import OAI.Combinatorics.BalancedRyser.Construction.ConstructionBlockCardinality
import OAI.Combinatorics.BalancedRyser.Construction.ConstructionRepresentationLemmas
import OAI.Combinatorics.BalancedRyser.Construction.PartitionHypergraph

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace ConfigurationRealizationProof

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

abbrev PointDomain := {p : Point F // p ∈ C.points}
abbrev DirectionalLabel (g : Direction F) :=
  {b : Configuration.BlockLabel F // b ∈ C.labelsInDirection g}

noncomputable def blockLabelSigmaEquiv :
    {b : Configuration.BlockLabel F // b ∈ C.blockLabels} ≃
      (g : Direction F) × DirectionalLabel C g := by
  classical
  refine {
    toFun := fun b => ⟨Configuration.blockDirection b.val,
      ⟨b.val, Finset.mem_filter.mpr ⟨b.property, rfl⟩⟩⟩
    invFun := fun gb => ⟨gb.2.val, (Finset.mem_filter.mp gb.2.property).1⟩
    left_inv := ?_
    right_inv := ?_
  }
  · intro b
    rfl
  · rintro ⟨g, b, hb⟩
    have hg : Configuration.blockDirection b = g := (Finset.mem_filter.mp hb).2
    subst g
    rfl

noncomputable def directionEquiv : Direction F ≃ Fin (Fintype.card F + 1) :=
  Fintype.equivFinOfCardEq (by simp [Direction])

noncomputable def directionalLabelEquiv (hV : C.Valid) (hC : C.Compatible)
    (g : Direction F) : DirectionalLabel C g ≃ Fin (Fintype.card F + 1) := by
  classical
  apply Fintype.equivFinOfCardEq
  simpa only [DirectionalLabel, Fintype.card_coe] using
    BlockCardinality.labels_in_direction_card C hV hC g

noncomputable def labelEquiv
    (eG : Direction F ≃ Fin (Fintype.card F + 1))
    (eL : ∀ g, DirectionalLabel C g ≃ Fin (Fintype.card F + 1)) :
    {b : Configuration.BlockLabel F // b ∈ C.blockLabels} ≃
      PartiteHypergraph.Vertex (Fintype.card F + 1) (Fintype.card F + 1) :=
  (blockLabelSigmaEquiv C).trans (encodeLabel eG eL)

noncomputable def realization_of_assignment
    (eG : Direction F ≃ Fin (Fintype.card F + 1))
    (eL : ∀ g, DirectionalLabel C g ≃ Fin (Fintype.card F + 1))
    (label : (g : Direction F) → PointDomain C → DirectionalLabel C g)
    (hinj : Function.Injective (fun p g => label g p))
    (hinc : ∀ g p (b : DirectionalLabel C g),
      p.val ∈ C.blockPoints b.val ↔ label g p = b) :
    ConfigurationRealization C (partitionHypergraph eG eL label) where
  directionEquiv := eG
  labelEquiv := labelEquiv C eG eL
  edgeEquiv := partitionHypergraph_edgeEquiv eG eL label hinj
  label_direction := by
    intro b
    rfl
  incidence := by
    intro p b
    change p.val ∈ C.blockPoints b.val ↔
      encodeAssignment eG eL label p (eG (Configuration.blockDirection b.val)) =
        eL (Configuration.blockDirection b.val)
          ⟨b.val, Finset.mem_filter.mpr ⟨b.property, rfl⟩⟩
    rw [encodeAssignment_apply_index]
    exact (hinc (Configuration.blockDirection b.val) p
      ⟨b.val, Finset.mem_filter.mpr ⟨b.property, rfl⟩⟩).trans
        (eL (Configuration.blockDirection b.val)).injective.eq_iff.symm

end ConfigurationRealizationProof
end Balanced

end OAI
