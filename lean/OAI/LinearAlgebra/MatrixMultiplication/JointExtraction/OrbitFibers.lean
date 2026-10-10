import OAI.LinearAlgebra.MatrixMultiplication.Recovery.EquivOrbitTransport

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

namespace MatrixMultiplication.JointOrbitFibers

attribute [local instance] Classical.propDecidable

variable {G X Y : Type*} [Group G] [MulAction G X] [Fintype X]

noncomputable def fullFiber (q : MulAction.orbitRel.Quotient G X) : Finset X :=
  Finset.univ.filter fun x => (Quotient.mk'' x : MulAction.orbitRel.Quotient G X) = q

@[simp] theorem mem_fullFiber {q : MulAction.orbitRel.Quotient G X} {x : X} :
    x ∈ fullFiber q ↔ (Quotient.mk'' x : MulAction.orbitRel.Quotient G X) = q := by
  simp only [fullFiber, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem mem_fullFiber_mk {x y : X} :
    y ∈ fullFiber (Quotient.mk'' x : MulAction.orbitRel.Quotient G X) ↔
      ∃ g : G, g • x = y := by
  rw [mem_fullFiber]
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

theorem fullFiber_nonempty (q : MulAction.orbitRel.Quotient G X) :
    (fullFiber q).Nonempty := by
  induction q using Quotient.inductionOn with
  | h x => exact ⟨x, mem_fullFiber.mpr rfl⟩

theorem fullFiber_card_pos (q : MulAction.orbitRel.Quotient G X) :
    0 < (fullFiber q).card :=
  Finset.card_pos.mpr (fullFiber_nonempty q)

section FiniteGroup

variable [Fintype G] [DecidableEq X]

theorem fullFiber_mk (x : X) :
    fullFiber (Quotient.mk'' x : MulAction.orbitRel.Quotient G X) =
      OrbitCounting.orbitSet (G := G) x := by
  ext y
  rw [mem_fullFiber_mk]
  simp only [OrbitCounting.orbitSet, Finset.mem_image, Finset.mem_univ, true_and]

theorem fullFiber_eq_orbitSet (q : MulAction.orbitRel.Quotient G X) (x : X)
    (hx : x ∈ fullFiber q) :
    fullFiber q = OrbitCounting.orbitSet (G := G) x := by
  rw [← mem_fullFiber.mp hx, fullFiber_mk]

end FiniteGroup

noncomputable def transportedFiber (e : Y ≃ X)
    (q : MulAction.orbitRel.Quotient G X) : Finset Y :=
  (fullFiber q).map e.symm.toEmbedding

@[simp] theorem mem_transportedFiber (e : Y ≃ X)
    {q : MulAction.orbitRel.Quotient G X} {y : Y} :
    y ∈ transportedFiber e q ↔
      (Quotient.mk'' (e y) : MulAction.orbitRel.Quotient G X) = q := by
  constructor
  · intro h
    obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp h
    have he : e y = x := by
      rw [← hxy]
      exact e.apply_symm_apply x
    rw [he]
    exact mem_fullFiber.mp hx
  · intro h
    exact Finset.mem_map.mpr ⟨e y, mem_fullFiber.mpr h, e.symm_apply_apply y⟩

@[simp] theorem transportedFiber_card (e : Y ≃ X)
    (q : MulAction.orbitRel.Quotient G X) :
    (transportedFiber e q).card = (fullFiber q).card :=
  Finset.card_map _

theorem transportedFiber_card_pos (e : Y ≃ X)
    (q : MulAction.orbitRel.Quotient G X) :
    0 < (transportedFiber e q).card := by
  rw [transportedFiber_card]
  exact fullFiber_card_pos q

theorem transportedFiber_mk [Fintype G] [DecidableEq X] [DecidableEq Y]
    (e : Y ≃ X) (y : Y) :
    letI : MulAction G Y := EquivOrbitTransport.action e
    transportedFiber e
        (Quotient.mk'' (e y) : MulAction.orbitRel.Quotient G X) =
      OrbitCounting.orbitSet (G := G) y := by
  let : MulAction G Y := EquivOrbitTransport.action e
  ext z
  rw [mem_transportedFiber]
  constructor
  · intro h
    have hz : e z ∈ fullFiber
        (Quotient.mk'' (e y) : MulAction.orbitRel.Quotient G X) :=
      mem_fullFiber.mpr h
    obtain ⟨g, hg⟩ := mem_fullFiber_mk.mp hz
    apply Finset.mem_image.mpr
    refine ⟨g, Finset.mem_univ _, ?_⟩
    change e.symm (g • e y) = z
    rw [hg, e.symm_apply_apply]
  · intro h
    obtain ⟨g, _, hg⟩ := Finset.mem_image.mp h
    apply Quotient.sound
    change ∃ g : G, g • e y = e z
    refine ⟨g, ?_⟩
    have he := congrArg e hg
    change e (e.symm (g • e y)) = e z at he
    simpa only [e.apply_symm_apply] using he

theorem transportedFiber_filter_card (e : Y ≃ X)
    (q : MulAction.orbitRel.Quotient G X) (bad : Y → Prop) [DecidablePred bad] :
    ((transportedFiber e q).filter bad).card =
      ((fullFiber q).filter (bad ∘ e.symm)).card := by
  rw [transportedFiber, Finset.filter_map]
  exact Finset.card_map _

end MatrixMultiplication.JointOrbitFibers

end OAI
