import OAI.GroupTheory.PolycyclicRecognition.Algebra.SeparateGroupClosure

namespace OAI

/-! # Finite-index subgroups are dense in a connected polynomial group

A closed subgroup of finite index is open: its finite quotient is T1 and
therefore discrete. The argument uses only continuous translations. In a
connected group this forces the closure of every finite-index subgroup to
be the whole group.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type*} [Group G] [TopologicalSpace G]
  [SeparatelyContinuousMul G] [ContinuousInv G]

omit [ContinuousInv G] in
theorem separate_isOpen_of_closed_finiteIndex (H : Subgroup G) [H.FiniteIndex]
    (hH : IsClosed (H : Set G)) : IsOpen (H : Set G) := by
  let q : G → G ⧸ H := Quotient.mk''
  let : TopologicalSpace (G ⧸ H) := TopologicalSpace.coinduced q inferInstance
  have hq : Topology.IsQuotientMap q := isQuotientMap_quot_mk
  let : T1Space (G ⧸ H) := by
    constructor
    intro z
    obtain ⟨r, rfl⟩ := Quotient.exists_rep z
    apply hq.isCoinducing.isClosed_preimage.mp
    have he : q ⁻¹' {q r} = (fun g : G => r⁻¹ * g) ⁻¹' (H : Set G) := by
      ext g
      change q g = q r ↔ r⁻¹ * g ∈ H
      rw [eq_comm, QuotientGroup.eq]
    rw [he]
    exact hH.preimage (continuous_const_mul r⁻¹)
  have he : q ⁻¹' {q 1} = (H : Set G) := by
    ext g
    change q g = q 1 ↔ g ∈ H
    rw [eq_comm, QuotientGroup.eq, inv_one, one_mul]
  rw [← he]
  exact (isOpen_discrete _).preimage hq.continuous

theorem separateClosure_eq_top_of_finiteIndex [PreconnectedSpace G]
    (H : Subgroup G) [H.FiniteIndex] : separateClosure H = ⊤ := by
  let C := separateClosure H
  let : C.FiniteIndex := Subgroup.finiteIndex_of_le (show H ≤ C from subset_closure)
  have hCclosed : IsClosed (C : Set G) := separateClosure_closed H
  have hopen := separate_isOpen_of_closed_finiteIndex C hCclosed
  have he : (C : Set G) = Set.univ :=
    (show IsClopen (C : Set G) from ⟨hCclosed, hopen⟩).eq_univ ⟨1, C.one_mem⟩
  exact SetLike.ext' he

end PolycyclicRecognition

end

end OAI
