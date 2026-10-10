import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentLatticeCyclicExtension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicKernelSplitting
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentPolyZ

namespace OAI

/-! # Realizing an arbitrary finitely generated torsion-free nilpotent group

The induction follows an actual torsion-free cyclic series. Its successive
integer normal forms are retained as polynomial parameters at every stage.
-/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G] [Group.IsNilpotent G]

theorem nilpotent_lattice_coordinates_of_cyclic_quotient
    (N : Subgroup G) [N.Normal] [IsCyclic (G ⧸ N)]
    (C : NilpotentLatticeCoordinates N)
    (hQ : HasNoNontrivialTorsion (G ⧸ N)) :
    Nonempty (NilpotentLatticeCoordinates G) := by
  cases finite_or_infinite (G ⧸ N) with
  | inl h =>
    let := h
    let := subsingleton_of_finite_torsionFree (G ⧸ N) hQ
    have htop : N = ⊤ := by
      apply top_unique
      intro g _
      exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
    subst N
    exact ⟨C.of_equiv Subgroup.topEquiv⟩
  | inr h =>
    let := h
    let E : Multiplicative ℤ ≃* G ⧸ N := intCyclicMulEquiv
    let q : G →* Multiplicative ℤ := E.symm.toMonoidHom.comp (QuotientGroup.mk' N)
    have hker : q.ker = N := by
      ext g
      change E.symm (QuotientGroup.mk' N g) = 1 ↔ g ∈ N
      rw [← E.symm.map_one, E.symm.injective.eq_iff]
      exact QuotientGroup.eq_one_iff g
    obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective N (E (Multiplicative.ofAdd 1))
    have hqt : q t = Multiplicative.ofAdd 1 := by
      change E.symm (QuotientGroup.mk' N t) = _
      rw [ht, E.symm_apply_apply]
    let e := cyclicKernelEquiv q t hqt
    let : Group.IsNilpotent
        (q.ker ⋊[integerPowerAction (MulAut.conjNormal t)] Multiplicative ℤ) :=
      (Group.isNilpotent_congr e).mpr inferInstance
    let C' := C.of_equiv (MulEquiv.subgroupCongr hker.symm)
    obtain ⟨D⟩ := C'.cyclic_extension (MulAut.conjNormal t)
    exact ⟨D.of_equiv e⟩

theorem nilpotent_lattice_coordinates_of_polyZ (hG : IsPolyZ G) :
    Nonempty (NilpotentLatticeCoordinates G) := by
  obtain ⟨n, c, hc⟩ := hG
  have hm : ∀ i, i ≤ n → Nonempty (NilpotentLatticeCoordinates (c.group i)) := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [c.first]
      exact ⟨NilpotentLatticeCoordinates.of_subsingleton⟩
    | succ i ih =>
      intro hi
      let s := c.step i (by omega)
      let := s.normal
      let := s.cyclic
      let e := (Subgroup.subgroupOfEquivOfLe s.le).symm
      obtain ⟨C⟩ := ih (by omega)
      exact nilpotent_lattice_coordinates_of_cyclic_quotient
        ((c.group i).subgroupOf (c.group (i + 1))) (C.of_equiv e) (hc i (by omega))
  obtain ⟨C⟩ := hm n le_rfl
  rw [c.last] at C
  exact ⟨C.of_equiv Subgroup.topEquiv⟩

theorem nilpotent_lattice_coordinates [Group.FG G]
    (hG : HasNoNontrivialTorsion G) : Nonempty (NilpotentLatticeCoordinates G) :=
  nilpotent_lattice_coordinates_of_polyZ
    (nilpotent_polyZ_of_finitelyGenerated_torsionFree hG)

omit [Group.IsNilpotent G] in
def NilpotentLatticeCoordinates.solvableLieModel (C : NilpotentLatticeCoordinates G) :
    SimplyConnectedSolvableLieModel :=
  { modelSpace := C.carrier, carrier := C.carrier }

theorem torsionFree_nilpotent_uniform_lattice [Group.FG G]
    (hG : HasNoNontrivialTorsion G) :
    ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
      IsUniformLattice Λ ∧ Nonempty (G ≃* Λ) := by
  obtain ⟨C⟩ := nilpotent_lattice_coordinates hG
  exact ⟨C.solvableLieModel, C.lattice, C.uniform, ⟨C.equiv⟩⟩

end PolycyclicRecognition

end

end OAI
