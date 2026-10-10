import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NilpotentLatticeDuality
import OAI.GroupTheory.PolycyclicRecognition.Lattices.LatticeTopLine

namespace OAI

/-! # Finiteness of a nilpotent kernel below a lattice quotient

The rational top class supplies the lower dimension bound. Integral
orientation homology and exhaustion stabilization then force finite generation.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] ModuleCat.isModule Rep.hV2
variable {G : Type} [Group G] [Countable G]

theorem nilpotent_kernel_finitelyGenerated_of_latticeQuotient (r : ℕ)
    (q : G →* IntegralLatticeGroup r) (hq : Function.Surjective q)
    [Group.IsNilpotent q.ker] {n : ℕ} (hG : IsIntegralPoincareDualityGroup G n) :
    Group.FG q.ker := by
  obtain ⟨d, R, ⟨eR⟩, hb, ⟨z, hz⟩, htor, hcom, hfinite, horientation⟩ :=
    nilpotent_topHomology_finiteness_criterion ((hG.finiteCohomologicalDimension G).subgroup q.ker)
  obtain ⟨B, ⟨eB⟩⟩ := exists_latticeTopLine q hq d hb R eR z hz htor hcom horientation
  have hlow : d + r ≤ n := by
    by_contra h
    let : HasProjectiveDimensionLE (trivialIntegral G) n := hG.cohomologicalDimension
    have hzero := groupHomology_isZero_above_dimension n B (d + r) (by omega)
    let : Subsingleton (groupHomology B (d + r)) := ModuleCat.subsingleton_of_isZero hzero
    have he : eB.symm (1 : ℚ) = eB.symm 0 := Subsingleton.elim _ _
    exact one_ne_zero (eB.symm.injective he)
  have hupp := hG.dimension_le_of_lattice_quotient r q hq d hb
  have hn : n = d + r := le_antisymm hupp hlow
  subst n
  obtain ⟨D, ⟨eD⟩, hfiniteD, x, hx⟩ := hG.exists_finite_nonzero_top
  let := hfiniteD
  obtain ⟨j, hj⟩ := exists_latticeTopHomologyInjection r q hq d hb D
  have hy : j x ≠ 0 := fun h => hx (hj (h.trans (map_zero j.hom).symm))
  obtain ⟨i⟩ := horientation (Rep.res q.ker.subtype D) ⟨eD⟩ ⟨j x, hy⟩
  let E : groupHomology R d ≅ groupHomology (Rep.res q.ker.subtype D) d :=
    (groupHomology.functor ℤ q.ker d).mapIso i
  have hEi : Function.Injective E.inv := (ModuleCat.mono_iff_injective _).mp inferInstance
  obtain ⟨htD, hcD⟩ := integralRankOne_properties_of_injective E.inv hEi htor hcom
  have hFD := (lattice_topHomology_finiteness r q hq d hb D htD hcD).2.2 x hx hfiniteD
  let := hFD
  exact hfinite (Module.Finite.equiv E.symm.toLinearEquiv)

theorem polycyclic_of_nilpotent_latticeQuotient (r : ℕ)
    (q : G →* IntegralLatticeGroup r) (hq : Function.Surjective q)
    [Group.IsNilpotent q.ker] {n : ℕ} (hG : IsIntegralPoincareDualityGroup G n) :
    IsPolycyclic G := by
  let := nilpotent_kernel_finitelyGenerated_of_latticeQuotient r q hq hG
  let e := QuotientGroup.quotientKerEquivOfSurjective q hq
  let : Group.FG (IntegralLatticeGroup r) := (integralLattice_poincareDuality r).1.fg
  have hQ : IsPolycyclic (G ⧸ q.ker) :=
    (isPolycyclic_of_finitelyGenerated_nilpotent (IntegralLatticeGroup r)).of_surjective
      e.symm.toMonoidHom e.symm.surjective
  exact isPolycyclic_of_normal_subgroup q.ker
    (isPolycyclic_of_finitelyGenerated_nilpotent q.ker) hQ

end PolycyclicRecognition

end

end OAI
