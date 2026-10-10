import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NilpotentCyclicDuality
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.LatticeTopHomologyInjection
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.LatticeKernelHomologyFiniteness

namespace OAI

/-! # The dimension reduction in nilpotent-by-abelian duality

The ambient duality dimension is bounded by the sum of the kernel dimension
and the lattice rank. Equality yields finite generation through integral
orientation homology.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] ModuleCat.isModule Rep.hV2
variable {G : Type} [Group G] [Countable G]

theorem nilpotent_lattice_duality_degree (r : ℕ)
    (q : G →* IntegralLatticeGroup r) (hq : Function.Surjective q)
    [Group.IsNilpotent q.ker] {n : ℕ} (hG : IsIntegralPoincareDualityGroup G n) :
    ∃ d : ℕ, n ≤ d + r ∧
      (Infinite (G ⧸ q.ker) → d < n) ∧
      (n = d + r → Group.FG q.ker) := by
  obtain ⟨d, R, ⟨eR⟩, hb, ⟨z, hz⟩, htor, hcom, hfinite, horientation⟩ :=
    nilpotent_topHomology_finiteness_criterion ((hG.finiteCohomologicalDimension G).subgroup q.ker)
  refine ⟨d, hG.dimension_le_of_lattice_quotient r q hq d hb, ?_, ?_⟩
  · intro hInfinite
    let := hInfinite
    exact hG.lt_dimension_of_normal_topHomology q.ker R z hz
  · intro hn
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

end PolycyclicRecognition

end

end OAI
