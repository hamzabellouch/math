import OAI.GroupTheory.PolycyclicRecognition.Finiteness.InfiniteQuotientHomology
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteTopOrientation
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NilpotentTopHomologyFiniteness
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CyclicKernelHomologyFiniteness
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.IntegerExtensionHomologyBound
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.PoincareHomologyDimension

namespace OAI

/-! # The duality finiteness endgame for a nilpotent-by-cyclic group

No finiteness of the nilpotent kernel is assumed. The strict subgroup dimension
bound identifies the ambient top degree, and its finite nonzero orientation
homology forces stabilization of the nilpotent exhaustion.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] ModuleCat.isModule Rep.hV2
variable {G : Type} [Group G] [Countable G]

theorem nilpotent_kernel_finitelyGenerated_of_integerQuotient
    (q : G →* Multiplicative ℤ) (t : G) (ht : q t = Multiplicative.ofAdd 1)
    [Group.IsNilpotent q.ker] {n : ℕ} (hG : IsIntegralPoincareDualityGroup G n) :
    Group.FG q.ker := by
  let := integerQuotient_isCyclic q t ht
  let := integerQuotient_infinite q t ht
  obtain ⟨d, R, ⟨eR⟩, hb, ⟨z, hz⟩, htor, hcom, hfinite, horientation⟩ :=
    nilpotent_topHomology_finiteness_criterion ((hG.finiteCohomologicalDimension G).subgroup q.ker)
  have hdn : d < n := hG.lt_dimension_of_normal_topHomology q.ker R z hz
  have hnd : n ≤ d + 1 := hG.homologicalDimension_le (d + 1)
    (homology_bound_of_integer_quotient q t ht d hb)
  have hn : n = d + 1 := by omega
  subst n
  obtain ⟨D, ⟨eD⟩, hfiniteD, x, hx⟩ := hG.exists_finite_nonzero_top
  let := hfiniteD
  have hv : IsZero (groupHomology (Rep.res q.ker.subtype D) (d + 1)) :=
    hb _ _ (by omega)
  let P := Rep.standardResolution ℤ q.ker
  let j := cyclicTopHomologyInjection q t ht P D d hv
  have hj : Function.Injective j := (ModuleCat.mono_iff_injective _).mp inferInstance
  have hy : j x ≠ 0 := fun h => hx (hj (h.trans (map_zero j.hom).symm))
  obtain ⟨i⟩ := horientation (Rep.res q.ker.subtype D) ⟨eD⟩ ⟨j x, hy⟩
  let E : groupHomology R d ≅ groupHomology (Rep.res q.ker.subtype D) d :=
    (groupHomology.functor ℤ q.ker d).mapIso i
  have hEi : Function.Injective E.inv := (ModuleCat.mono_iff_injective _).mp inferInstance
  obtain ⟨htD, hcD⟩ := integralRankOne_properties_of_injective E.inv hEi htor hcom
  have hFD : Module.Finite ℤ (groupHomology (Rep.res q.ker.subtype D) d) :=
    cyclic_topHomology_finiteness q t ht P D d hv htD hcD x hx
  let := hFD
  exact hfinite (Module.Finite.equiv E.symm.toLinearEquiv)

theorem polycyclic_of_nilpotent_integerQuotient
    (q : G →* Multiplicative ℤ) (t : G) (ht : q t = Multiplicative.ofAdd 1)
    [Group.IsNilpotent q.ker] {n : ℕ} (hG : IsIntegralPoincareDualityGroup G n) :
    IsPolycyclic G := by
  let := integerQuotient_isCyclic q t ht
  let := nilpotent_kernel_finitelyGenerated_of_integerQuotient q t ht hG
  exact isPolycyclic_of_normal_subgroup q.ker
    (isPolycyclic_of_finitelyGenerated_nilpotent q.ker) isPolycyclic_of_isCyclic

end PolycyclicRecognition

end

end OAI
