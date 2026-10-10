import OAI.GroupTheory.PolycyclicRecognition.Lattices.UniformLatticeMetric
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolycyclicFiniteGeneration
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.VirtualPolycyclicDuality

namespace OAI

/-!
# The duality comparison from an actual uniform lattice

The metric lattice comparison gives a Robinson/Bieri duality comparison.
Polycyclicity of the comparison lattice is retained explicitly; for solvable
Lie lattices it is the conclusion of Farb--Weinberger (2008), Proposition 3.4.
-/

namespace PolycyclicRecognition

open Metric

variable {G H : Type} [Group G] [MetricSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G] [ProperSpace G]
  [Group H] [MetricSpace H] [IsIsometricSMul H H]

/-- A metric quasi-isometry to a uniform-lattice ambient group produces a
finitely generated integral-duality comparison group. -/
theorem IsUniformLattice.exists_duality_comparison
    {Λ : Subgroup G} (hΛ : IsUniformLattice Λ) (hpoly : IsPolycyclic Λ)
    (f : H → G) (hfinite : ∀ R : ℝ, (closedBall (1 : H) R).Finite)
    {K C K' C' E : ℝ} (hK : 0 ≤ K) (hK' : 0 ≤ K')
    (hupper : ∀ x y, dist (f x) (f y) ≤ K * dist x y + C)
    (hlower : ∀ x y, dist x y ≤ K' * dist (f x) (f y) + C')
    (hsurj : ∀ g, ∃ x, dist g (f x) ≤ E) :
    ∃ (L : Subgroup Λ) (Γ : Subgroup L),
      L.FiniteIndex ∧ Γ.FiniteIndex ∧ Group.FG Γ ∧
      Nonempty (GroupCoarseEquivalence Γ H) ∧
      ∃ n : ℕ, IsIntegralPoincareDualityGroup Γ n := by
  let := hpoly.finitelyGenerated
  obtain ⟨e⟩ := hΛ.nonempty_coarseEquivalence f hfinite hK hK' hupper hlower hsurj
  exact exists_coarse_poincareDuality_comparison_proved Λ H
    hpoly.isVirtuallyPolycyclic e.symm

/-- Elementary amenability and a metric quasi-isometry to an ambient group
with a polycyclic uniform lattice imply virtual polycyclicity, given the
finiteness and duality inputs. -/
theorem IsUniformLattice.virtuallyPolycyclic_of_elementaryAmenable
    (liFP : LiFinitenessInput) (eaFP : ElementaryAmenableFinitenessInput)
    (liPD : LiDualityInput) (bieri : BieriDualityInput)
    {Λ : Subgroup G} (hΛ : IsUniformLattice Λ) (hpoly : IsPolycyclic Λ)
    [Group.FG H] (hEA : IsElementaryAmenable H)
    (f : H → G) (hfinite : ∀ R : ℝ, (closedBall (1 : H) R).Finite)
    {K C K' C' E : ℝ} (hK : 0 ≤ K) (hK' : 0 ≤ K')
    (hupper : ∀ x y, dist (f x) (f y) ≤ K * dist x y + C)
    (hlower : ∀ x y, dist x y ≤ K' * dist (f x) (f y) + C')
    (hsurj : ∀ g, ∃ x, dist g (f x) ≤ E) : IsVirtuallyPolycyclic H := by
  let := hpoly.finitelyGenerated
  obtain ⟨e⟩ := hΛ.nonempty_coarseEquivalence f hfinite hK hK' hupper hlower hsurj
  exact virtuallyPolycyclic_of_elementaryAmenable_coarse_virtualPolycyclic_proved
    liFP eaFP liPD bieri Λ H hpoly.isVirtuallyPolycyclic e.symm hEA

end PolycyclicRecognition

end OAI
