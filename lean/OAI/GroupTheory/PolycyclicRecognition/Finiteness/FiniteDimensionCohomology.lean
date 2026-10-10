import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SubgroupResolution
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

namespace OAI

/-! # Cohomology above the integral dimension bound

The bound applies to every coefficient representation. In particular the
periodic cohomology of a nontrivial finite cyclic group rules out finite
integral cohomological dimension.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable {G : Type}

theorem groupCohomology_isZero_above_dimension [Group G] (d : ℕ)
    [HasProjectiveDimensionLE (trivialIntegral G) d]
    (A : Rep ℤ G) (i : ℕ) (hi : d < i) :
    IsZero (groupCohomology A i) := by
  let P := finiteProjectiveResolution (Rep.standardResolution ℤ G) d
  have hP : IsZero (P.complex.X i) :=
    finiteTruncation_isZero (Rep.standardResolution ℤ G) d i hi
  have hX : IsZero ((P.complex.linearYonedaObj ℤ A).X i) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact ⟨fun f g => hP.eq_of_src f g⟩
  refine IsZero.of_iso ?_ (groupCohomologyIso A i P)
  apply HomologicalComplex.ExactAt.isZero_homology
  apply ShortComplex.exact_of_isZero_X₂
  simpa only [HomologicalComplex.shortComplexFunctor_obj_X₂] using hX

/-- A nonzero dualizing module cannot occur above the cohomological dimension. -/
theorem IsIntegralPoincareDualityGroup.dimension_le [Group G] {n d : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n)
    [HasProjectiveDimensionLE (trivialIntegral G) d] : n ≤ d := by
  by_contra hnd
  have hz := groupCohomology_isZero_above_dimension d (Rep.leftRegular ℤ G) n
    (Nat.lt_of_not_ge hnd)
  obtain ⟨e⟩ := hG.2.2
  have hzero : IsZero (ModuleCat.of ℤ ℤ) := IsZero.of_iso hz e.symm
  have h01 : (0 : ℤ) = 1 := ModuleCat.isZero_iff_subsingleton.mp hzero |>.elim _ _
  exact zero_ne_one h01

/-- One finite dimension bound controls every duality subgroup. -/
theorem HasFiniteIntegralCohomologicalDimension.bounds_duality_subgroups [Group G]
    (hG : HasFiniteIntegralCohomologicalDimension G) :
    ∃ d : ℕ, ∀ (H : Subgroup G) (n : ℕ), IsIntegralPoincareDualityGroup H n → n ≤ d := by
  obtain ⟨d, hd⟩ := hG
  let := hd
  refine ⟨d, fun H n hH => ?_⟩
  let := subgroup_cohomologicalDimension_le H d
  exact hH.dimension_le

section FiniteCyclic
variable [CommGroup G] [Fintype G] (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)

include g hg in
/-- The class of one in positive even integral cohomology is nonzero whenever
there is more than one group element. -/
theorem finiteCyclic_even_cohomology_not_isZero (hG : 1 < Fintype.card G)
    (i : ℕ) [NeZero i] (hi : Even i) :
    ¬ IsZero (groupCohomology (trivialIntegral G) i) := by
  intro hz
  let x : LinearMap.ker (Rep.applyAsHom (trivialIntegral G) g -
      𝟙 (trivialIntegral G)).hom.toLinearMap := ⟨1, by change (1 : ℤ) - 1 = 0; omega⟩
  have hx : Rep.FiniteCyclicGroup.groupCohomologyπEven
      (trivialIntegral G) g hg i hi x = 0 := by
    exact ModuleCat.isZero_iff_subsingleton.mp hz |>.elim _ _
  obtain ⟨z, hz⟩ := (Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff
    (trivialIntegral G) g hg i hi x).mp hx
  have heq : (Fintype.card G : ℤ) * z = 1 := by
    simpa [Rep.norm, Representation.norm, trivialIntegral, x] using hz
  have hdvd : (Fintype.card G : ℤ) ∣ 1 := ⟨z, heq.symm⟩
  have hc : (Fintype.card G : ℤ) = 1 := (Int.eq_one_of_dvd_one (by omega) hdvd)
  omega

end FiniteCyclic
end PolycyclicRecognition

end

end OAI
