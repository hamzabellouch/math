import OAI.GroupTheory.PolycyclicRecognition.Lattices.SolvableLatticeRecognition

namespace OAI

/-!
# Virtual polycyclicity and finite-index solvable lattices

Dekimpe's realization and polycyclicity of solvable Lie lattices identify
virtual polycyclicity with a finite-index solvable-lattice realization.
-/

namespace PolycyclicRecognition

/-- A group with a finite-index subgroup isomorphic to a uniform solvable Lie
lattice is virtually polycyclic. -/
theorem virtuallyPolycyclic_of_finiteIndex_solvableLattice
    (fw : FarbWeinbergerLatticeInput) {H : Type} [Group H]
    (Γ : Subgroup H) (hΓ : Γ.FiniteIndex)
    (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier)
    (hΛ : IsUniformLattice Λ) (e : Γ ≃* Λ) :
    IsVirtuallyPolycyclic H :=
  ⟨Γ, hΓ, (fw S Λ hΛ).of_injective e.toMonoidHom e.injective⟩

/-- Virtual polycyclicity is equivalent to finite-index realization as a
discrete uniform lattice in a simply connected solvable Lie group. -/
theorem virtuallyPolycyclic_iff_finiteIndex_solvableLattice
    (dekimpe : DekimpeLatticeRealizationInput) (fw : FarbWeinbergerLatticeInput)
    (H : Type) [Group H] :
    IsVirtuallyPolycyclic H ↔
      ∃ Γ : Subgroup H, Γ.FiniteIndex ∧
        ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
          IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  constructor
  · exact exists_uniform_solvable_lattice_of_virtuallyPolycyclic dekimpe H
  · rintro ⟨Γ, hΓ, S, Λ, hΛ, ⟨e⟩⟩
    exact virtuallyPolycyclic_of_finiteIndex_solvableLattice fw Γ hΓ S Λ hΛ e

end PolycyclicRecognition

end OAI
