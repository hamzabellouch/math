import OAI.GroupTheory.PolycyclicRecognition.Algebra.TorsionFreeCyclicExtension

namespace OAI

/-! # Torsion-free finite-index subgroups of polycyclic groups

This proves the torsion-free consequence of Robinson, *A Course in the
Theory of Groups*, second edition, Theorem 5.4.15(i), needed by the duality
comparison. The proof is induction along the actual cyclic subnormal series.
-/

noncomputable section
namespace PolycyclicRecognition

open ChromaticCyclic

variable {G J : Type} [Group G] [Group J]

theorem torsionFree_finiteIndex_of_equiv (e : G ≃* J)
    (h : ∃ H : Subgroup G, H.FiniteIndex ∧ HasNoNontrivialTorsion H) :
    ∃ K : Subgroup J, K.FiniteIndex ∧ HasNoNontrivialTorsion K := by
  obtain ⟨H, hHi, hHt⟩ := h
  let := hHi
  let d := H.equivMapOfInjective e.toMonoidHom e.injective
  exact ⟨H.map e.toMonoidHom, Subgroup.FiniteIndex.map_of_surjective H e.surjective,
    hHt.of_injective d.symm.toMonoidHom d.symm.injective⟩

theorem torsionFree_finiteIndex_of_cyclicStep {H K : Subgroup G}
    (s : CyclicStep H K) (hfg : Group.FG H)
    (hH : ∃ L : Subgroup H, L.FiniteIndex ∧ HasNoNontrivialTorsion L) :
    ∃ L : Subgroup K, L.FiniteIndex ∧ HasNoNontrivialTorsion L := by
  let e := (Subgroup.subgroupOfEquivOfLe s.le).symm
  let : Group.FG (H.subgroupOf K) :=
    @Group.fg_of_surjective _ _ _ _ hfg e.toMonoidHom e.surjective
  let := s.normal
  let := s.cyclic
  exact torsionFree_finiteIndex_of_cyclic_extension (H.subgroupOf K)
    (torsionFree_finiteIndex_of_equiv e hH)

theorem IsPolycyclic.exists_torsionFree_finiteIndex (hG : IsPolycyclic G) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ HasNoNontrivialTorsion H := by
  obtain ⟨n, ⟨c⟩⟩ := hG
  have hm : ∀ i, i ≤ n → Group.FG (c.group i) ∧
      ∃ H : Subgroup (c.group i), H.FiniteIndex ∧ HasNoNontrivialTorsion H := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [c.first]
      refine ⟨inferInstance, ⊤, inferInstance, ?_⟩
      intro g m hm hg
      exact Subsingleton.elim _ _
    | succ i ih =>
      intro hi
      obtain ⟨hfg, htf⟩ := ih (by omega)
      exact ⟨finitelyGenerated_of_cyclicStep (c.step i (by omega)) hfg,
        torsionFree_finiteIndex_of_cyclicStep (c.step i (by omega)) hfg htf⟩
  have htop := (hm n le_rfl).2
  rw [c.last] at htop
  exact torsionFree_finiteIndex_of_equiv (Subgroup.topEquiv) htop

/-- Every polycyclic group has a torsion-free subgroup of finite index. -/
theorem polycyclicTorsionFreeIndexInput : PolycyclicTorsionFreeIndexInput :=
  fun _ _ h => h.exists_torsionFree_finiteIndex

end PolycyclicRecognition

end

end OAI
