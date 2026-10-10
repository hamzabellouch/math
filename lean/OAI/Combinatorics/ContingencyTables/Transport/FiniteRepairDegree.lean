import OAI.Combinatorics.ContingencyTables.Transport.FiniteSymmetricEnergy

namespace OAI

/-! # The finite list of designated and inverse repair neighbors -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped Classical

variable {X D T : Type*} [Fintype D] [Fintype T]

omit [Fintype T] in
/-- If the source encoding is injective there is at most one outgoing
repair at a fixed state. -/
theorem outgoing_repair_card_le (x y : D → X) (hx : Function.Injective x) (v : X) :
    ((Finset.univ.filter (fun d => x d=v)).image y).card ≤ 1 := by
  have hsmall : (Finset.univ.filter (fun d => x d=v)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact hx ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  exact Finset.card_image_le.trans hsmall

/-- The ordered defect type and repaired profile identify the source.
Consequently a fixed target has at most one inverse repair of each type. -/
theorem incoming_repair_card_le (x y : D → X) (label : D → T)
    (h : Function.Injective (fun d => (label d,y d))) (v : X) :
    ((Finset.univ.filter (fun d => y d=v)).image x).card ≤ Fintype.card T := by
  let S := {d : D // y d=v}
  have hlabel : Function.Injective (fun d : S => label d.val) := by
    intro a b he
    apply Subtype.ext
    exact h (Prod.ext he (a.property.trans b.property.symm))
  have hcard : Fintype.card S ≤ Fintype.card T := Fintype.card_le_of_injective _ hlabel
  have he : (Finset.univ.filter (fun d => y d=v)).card=Fintype.card S := by
    symm
    exact Fintype.card_subtype _
  exact Finset.card_image_le.trans (he.le.trans hcard)

noncomputable def repairNeighbors (x y : D → X) (v : X) : Finset X :=
  ((Finset.univ.filter (fun d => x d=v)).image y) ∪
    ((Finset.univ.filter (fun d => y d=v)).image x)

omit [Fintype T] in
lemma mem_repairNeighbors_forward (x y : D → X) (v : X) (d : D) (h : x d=v) :
    y d ∈ repairNeighbors x y v := by
  unfold repairNeighbors
  exact Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨d,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩)

omit [Fintype T] in
lemma mem_repairNeighbors_reverse (x y : D → X) (v : X) (d : D) (h : y d=v) :
    x d ∈ repairNeighbors x y v := by
  unfold repairNeighbors
  exact Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨d,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩)

theorem repairNeighbors_card_le (x y : D → X) (hx : Function.Injective x) (label : D → T)
    (h : Function.Injective (fun d => (label d,y d))) (v : X) :
    (repairNeighbors x y v).card ≤ 1+Fintype.card T := by
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add (outgoing_repair_card_le x y hx v) (incoming_repair_card_le x y label h v))

end ContingencyTables.IntegerWeightedTransport

end OAI
