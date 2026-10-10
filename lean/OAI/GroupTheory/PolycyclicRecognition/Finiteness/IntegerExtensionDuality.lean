import OAI.GroupTheory.PolycyclicRecognition.Algebra.InducedCyclicDifference
import OAI.GroupTheory.PolycyclicRecognition.Algebra.IntegerQuotientStructure
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CofiberCohomology

namespace OAI

/-! # The cohomological dimension shift for an infinite cyclic extension -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G] (q : G →* Multiplicative ℤ)
  (t : G) (ht : q t = Multiplicative.ofAdd 1)

section Cyclic
variable [IsCyclic (G ⧸ q.ker)] [Infinite (G ⧸ q.ker)]
local instance : CommGroup (G ⧸ q.ker) := IsCyclic.commGroup

variable (P : ProjectiveResolution (Rep.trivial ℤ q.ker ℤ))

def integerExtensionResolution : ProjectiveResolution (trivialIntegral G) :=
  cokernelProjectiveResolution
    (cyclicQuotientSequence (G ⧸ q.ker) (QuotientGroup.mk' q.ker) (QuotientGroup.mk' q.ker t))
    (quotientInducedResolution q.ker P) (quotientInducedResolution q.ker P)
    (cyclicQuotientSequence_shortExact (G ⧸ q.ker) (QuotientGroup.mk' q.ker)
      (QuotientGroup.mk' q.ker t) (integerQuotient_generator q t ht))

def integerExtensionMap :=
  ProjectiveResolution.lift
    (Rep.resMap (QuotientGroup.mk' q.ker)
      (cyclicDifference (G ⧸ q.ker) (QuotientGroup.mk' q.ker t)))
    (quotientInducedResolution q.ker P) (quotientInducedResolution q.ker P)

omit [Infinite (G ⧸ q.ker)] in
theorem integerExtensionMap_homology (i : ℕ) :
    HomologicalComplex.homologyMap
      (repCochainPrecomp ℤ (integerExtensionMap q t P) (Rep.leftRegular ℤ G)) i =
        inducedCohomologyDifference q t P i :=
  (repCochainHomotopy ℤ (inducedCyclicDifferenceHomotopy q.ker t P)
    (Rep.leftRegular ℤ G)).homologyMap_eq i

variable (hP : ∀ i, Module.Finite ℤ[q.ker] (P.complex.X i).ρ.asModule)

include ht hP in
omit [Infinite (G ⧸ q.ker)] in
theorem integerExtensionMap_homology_mono (i : ℕ) :
    Mono (HomologicalComplex.homologyMap
      (repCochainPrecomp ℤ (integerExtensionMap q t P) (Rep.leftRegular ℤ G)) i) := by
  rw [integerExtensionMap_homology]
  exact (ModuleCat.mono_iff_injective _).mpr
    (inducedCohomologyDifference_injective q t ht P hP i)

def integerExtensionCohomologyIso (i : ℕ) :
    groupCohomology (Rep.leftRegular ℤ G) (i + 1) ≅
      groupCohomology (Rep.leftRegular ℤ q.ker) i := by
  let := integerExtensionMap_homology_mono q t ht P hP (i + 1)
  refine groupCohomologyIso (Rep.leftRegular ℤ G) (i + 1) (integerExtensionResolution q t ht P) ≪≫
    (cofiberCochainCokernelIso (integerExtensionMap q t P) (Rep.leftRegular ℤ G) i).symm ≪≫
      ?_ ≪≫ inducedCohomologyDifferenceCokernelIso q t ht P hP i ≪≫
        (groupCohomologyIso (Rep.leftRegular ℤ q.ker) i P).symm
  exact cokernel.mapIso _ _ (Iso.refl _) (Iso.refl _)
    (by
      exact (Category.comp_id (HomologicalComplex.homologyMap
        (repCochainPrecomp ℤ (integerExtensionMap q t P) (Rep.leftRegular ℤ G)) i)).trans
          ((integerExtensionMap_homology q t P i).trans
            (Category.id_comp (inducedCohomologyDifference q t P i)).symm))

include q t ht P hP in
theorem integerExtensionCohomology_zero :
    IsZero (groupCohomology (Rep.leftRegular ℤ G) 0) := by
  let := integerExtensionMap_homology_mono q t ht P hP 0
  exact IsZero.of_iso (cofiberCochain_homology_zero (integerExtensionMap q t P)
    (Rep.leftRegular ℤ G))
      (groupCohomologyIso (Rep.leftRegular ℤ G) 0 (integerExtensionResolution q t ht P))

end Cyclic

include ht in
theorem poincareDuality_of_integerQuotient {n : ℕ}
    (hN : IsIntegralPoincareDualityGroup q.ker n) :
    IsIntegralPoincareDualityGroup G (n + 1) := by
  let := integerQuotient_isCyclic q t ht
  let := integerQuotient_infinite q t ht
  obtain ⟨P, d, hP, hd⟩ := hN.1
  refine ⟨finiteProjectiveResolution_of_infiniteCyclicQuotient q.ker hN.1, ?_, ?_⟩
  · intro i hi
    cases i with
    | zero => exact integerExtensionCohomology_zero q t ht P hP
    | succ j =>
      exact IsZero.of_iso (hN.2.1 j (by omega))
        (integerExtensionCohomologyIso q t ht P hP j)
  · obtain ⟨e⟩ := hN.2.2
    exact ⟨integerExtensionCohomologyIso q t ht P hP n ≪≫ e⟩

end PolycyclicRecognition

end

end OAI
