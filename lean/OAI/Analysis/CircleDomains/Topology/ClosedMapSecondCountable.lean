import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact

namespace OAI

/-! A closed surjection with compact fibers preserves second countability.
Finite unions of source basis sets give an explicit countable target
basis; no metrizability assertion is assumed. -/
open Set Topology TopologicalSpace
noncomputable section
namespace CircleDomainRigidity

lemma secondCountable_of_closed_surjection_compact_fibers
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] (f : X → Y) (hc : Continuous f)
    (hclosed : IsClosedMap f) (hsurj : Function.Surjective f)
    (hfib : ∀ y, IsCompact (f ⁻¹' {y})) : SecondCountableTopology Y := by
  classical
  let B := countableBasis X
  let J := {b : Set X // b ∈ B}
  have : Countable J := (countable_countableBasis X).to_subtype
  let V (t : Finset J) : Set X := ⋃ b ∈ t, (b : Set X)
  have hV (t : Finset J) : IsOpen (V t) :=
    isOpen_biUnion fun b _ => (isBasis_countableBasis X).isOpen b.property
  let W (t : Finset J) : Set Y := (f '' (V t)ᶜ)ᶜ
  have hW (t : Finset J) : IsOpen (W t) := (hclosed _ (hV t).isClosed_compl).isOpen_compl
  have hbase : IsTopologicalBasis (range W) := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro U ⟨t,rfl⟩
      exact hW t
    · intro y U hy hU
      let C (b : J) : Set X := if (b : Set X) ⊆ f ⁻¹' U then b else ∅
      have hC (b : J) : IsOpen (C b) := by
        dsimp only [C]
        split_ifs
        · exact (isBasis_countableBasis X).isOpen b.property
        · exact isOpen_empty
      have hcover : f ⁻¹' {y} ⊆ ⋃ b, C b := by
        intro x hx
        have hxU : x ∈ f ⁻¹' U := by
          change f x = y at hx
          change f x ∈ U
          rw [hx]
          exact hy
        obtain ⟨b,hb,hxb,hbU⟩ := (isBasis_countableBasis X).exists_subset_of_mem_open
          hxU (hU.preimage hc)
        exact mem_iUnion.mpr ⟨⟨b,hb⟩, by simpa only [C, ite_eq_left hbU] using hxb⟩
      obtain ⟨t,ht⟩ := (hfib y).elim_finite_subcover C hC hcover
      let t' := t.filter (fun b : J => (b : Set X) ⊆ f ⁻¹' U)
      have hCV : f ⁻¹' {y} ⊆ V t' := by
        intro x hx
        obtain ⟨b,hbt,hxb⟩ := mem_iUnion₂.mp (ht hx)
        have hbU : (b : Set X) ⊆ f ⁻¹' U := by
          by_contra hn
          simp only [C, ite_eq_right hn, mem_empty_iff_false] at hxb
        apply mem_iUnion₂.mpr
        exact ⟨b, Finset.mem_filter.mpr ⟨hbt,hbU⟩, by simpa only [C, ite_eq_left hbU] using hxb⟩
      have hVU : V t' ⊆ f ⁻¹' U := by
        intro x hx
        obtain ⟨b,hbt,hxb⟩ := mem_iUnion₂.mp hx
        exact (Finset.mem_filter.mp hbt).2 hxb
      refine ⟨W t', mem_range_self _, ?_, ?_⟩
      · rintro ⟨x,hx,hxy⟩
        exact hx (hCV hxy)
      · intro z hz
        obtain ⟨x,rfl⟩ := hsurj z
        apply hVU
        by_contra hx
        exact hz ⟨x,hx,rfl⟩
  exact hbase.secondCountableTopology (countable_range W)

end CircleDomainRigidity

end

end OAI
