import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Bases

namespace OAI

/-! A countable subfamily of the actual collar neighborhoods suffices at every
point and every scale. The selected sets retain their original witnesses. -/

open Set Function TopologicalSpace

noncomputable section
namespace CircleDomainRigidity

theorem exists_countable_local_family {X C : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] (S : Set X) (U : C → Set X)
    (hU : ∀ c, IsOpen (U c))
    (hlocal : ∀ x ∈ S, ∀ V : Set X, IsOpen V → x ∈ V →
      ∃ c, x ∈ U c ∧ U c ⊆ V) :
    ∃ D : Set C, D.Countable ∧ ∀ x ∈ S, ∀ V : Set X,
      IsOpen V → x ∈ V → ∃ c ∈ D, x ∈ U c ∧ U c ⊆ V := by
  classical
  obtain ⟨B, hB⟩ := exists_seq_basis X
  have hcover (n : ℕ) : ∃ D : Set C, D.Countable ∧
      (∀ c ∈ D, U c ⊆ B n) ∧ S ∩ B n ⊆ ⋃ c ∈ D, U c := by
    let T := {c : C | U c ⊆ B n}
    have hc : S ∩ B n ⊆ ⋃ c : T, U c.val := by
      rintro x ⟨hxS, hxB⟩
      obtain ⟨c, hxc, hc⟩ := hlocal x hxS (B n)
        (hB.isOpen (mem_range_self n)) hxB
      exact mem_iUnion.mpr ⟨⟨c, hc⟩, hxc⟩
    obtain ⟨D, hD, hcov⟩ := (HereditarilyLindelofSpace.isLindelof (S ∩ B n)).elim_countable_subcover
      (fun c : T => U c.val) (fun c => hU c.val) hc
    refine ⟨Subtype.val '' D, hD.image _, ?_, ?_⟩
    · rintro c ⟨d, hd, rfl⟩
      exact d.property
    · intro x hx
      obtain ⟨c, hcD, hxc⟩ := mem_iUnion₂.mp (hcov hx)
      exact mem_iUnion₂.mpr ⟨c.val, mem_image_of_mem _ hcD, hxc⟩
  choose D hD hDB hcov using hcover
  refine ⟨⋃ n, D n, countable_iUnion hD, ?_⟩
  intro x hxS V hV hxV
  obtain ⟨W, hWB, hxW, hWV⟩ := hB.exists_subset_of_mem_open hxV hV
  obtain ⟨n, rfl⟩ := hWB
  obtain ⟨c, hcD, hxc⟩ := mem_iUnion₂.mp (hcov n ⟨hxS, hxW⟩)
  exact ⟨c, mem_iUnion.mpr ⟨n, hcD⟩, hxc, (hDB n c hcD).trans hWV⟩

end CircleDomainRigidity

end

end OAI
