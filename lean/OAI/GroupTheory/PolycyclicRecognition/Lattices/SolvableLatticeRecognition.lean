import OAI.GroupTheory.PolycyclicRecognition.Lattices.SolvableLatticeModel
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolycyclicFiniteGeneration
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.VirtualPolycyclicDuality

namespace OAI

/-!
# The algebraic endgame for recognition of solvable Lie lattices

B. Farb and S. Weinberger, *Isometries, rigidity and universal covers*,
Annals of Mathematics 168 (2008), 915–940, Proposition 3.4, p.932,
states that every lattice in a connected solvable Lie group is polycyclic.
The lattice-polycyclicity predicate specializes this statement to uniform
lattices in connected simply connected solvable Lie groups.

Elementary amenability and the finiteness and duality theorems give virtual
polycyclicity. Dekimpe's realization then produces a finite-index lattice in
a possibly different solvable Lie group. Elementary amenability remains an
explicit premise of these conditional recognition theorems.
-/

namespace PolycyclicRecognition

/-- The simply connected uniform-lattice specialization of
Farb–Weinberger (2008), Proposition 3.4. -/
def FarbWeinbergerLatticeInput : Prop :=
  ∀ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
    IsUniformLattice Λ → IsPolycyclic Λ

/-- Coarse comparison with an actual solvable Lie lattice supplies the
polycyclic comparison group for the elementary-amenable endgame. -/
theorem virtuallyPolycyclic_of_elementaryAmenable_coarse_solvableLattice
    (fw : FarbWeinbergerLatticeInput)
    (liFP : LiFinitenessInput) (eaFP : ElementaryAmenableFinitenessInput)
    (liPD : LiDualityInput) (bieri : BieriDualityInput)
    (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier)
    (hΛ : IsUniformLattice Λ)
    (H : Type) [Group H] [Group.FG H] (hEA : IsElementaryAmenable H)
    (e : GroupCoarseEquivalence Λ H) : IsVirtuallyPolycyclic H := by
  have hpoly := fw S Λ hΛ
  let := hpoly.finitelyGenerated
  exact virtuallyPolycyclic_of_elementaryAmenable_coarse_virtualPolycyclic_proved
    liFP eaFP liPD bieri Λ H hpoly.isVirtuallyPolycyclic e hEA

/-- The lattice realization follows from the algebraic endgame and the
precisely stated published realization theorem. The ambient Lie group is
allowed to change, as in the manuscript's lattice-recognition statement. -/
theorem exists_solvableLattice_of_elementaryAmenable_coarse_solvableLattice
    (dekimpe : DekimpeLatticeRealizationInput) (fw : FarbWeinbergerLatticeInput)
    (liFP : LiFinitenessInput) (eaFP : ElementaryAmenableFinitenessInput)
    (liPD : LiDualityInput) (bieri : BieriDualityInput)
    (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier)
    (hΛ : IsUniformLattice Λ)
    (H : Type) [Group H] [Group.FG H] (hEA : IsElementaryAmenable H)
    (e : GroupCoarseEquivalence Λ H) :
    ∃ Γ : Subgroup H, Γ.FiniteIndex ∧
      ∃ (S' : SimplyConnectedSolvableLieModel) (Λ' : Subgroup S'.carrier),
        IsUniformLattice Λ' ∧ Nonempty (Γ ≃* Λ') := by
  apply exists_uniform_solvable_lattice_of_virtuallyPolycyclic dekimpe H
  exact virtuallyPolycyclic_of_elementaryAmenable_coarse_solvableLattice
    fw liFP eaFP liPD bieri S Λ hΛ H hEA e

end PolycyclicRecognition

end OAI
