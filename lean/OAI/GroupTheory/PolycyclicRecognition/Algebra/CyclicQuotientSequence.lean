import OAI.GroupTheory.PolycyclicRecognition.Finiteness.InfiniteCyclicResolution
import Mathlib.RepresentationTheory.Rep.Res

namespace OAI

/-! # The coefficient sequence for an infinite cyclic quotient

Inflating the cyclic augmentation sequence gives the two copies of the
quotient permutation module used in the cyclic-extension argument.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable (Q : Type) [CommGroup Q]

def cyclicAugmentationSequence (z : Q) : ShortComplex (Rep ℤ Q) :=
  ShortComplex.mk (cyclicDifference Q z) (cyclicAugmentation Q)
    (cyclicDifference_augmentation Q z)

theorem cyclicAugmentationSequence_exact (z : Q)
    (hz : ∀ x, x ∈ Subgroup.zpowers z) : (cyclicAugmentationSequence Q z).Exact := by
  apply (forget₂ (Rep ℤ Q) (ModuleCat ℤ)).reflects_exact_of_faithful
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range (Representation.leftRegular ℤ Q z - LinearMap.id) =
    LinearMap.ker (integralAugmentation Q)
  exact (integralAugmentation_ker_of_cyclic Q z hz).symm

theorem cyclicAugmentationSequence_shortExact [Infinite Q] (z : Q)
    (hz : ∀ x, x ∈ Subgroup.zpowers z) : (cyclicAugmentationSequence Q z).ShortExact where
  exact := cyclicAugmentationSequence_exact Q z hz
  mono_f := by
    rw [Rep.mono_iff_injective]
    exact leftRegular_difference_injective z hz
  epi_g := by
    rw [Rep.epi_iff_surjective]
    intro r
    refine ⟨MonoidAlgebra.single 1 r, ?_⟩
    exact integralAugmentation_single Q 1 r

variable {G : Type} [Group G]

def cyclicQuotientSequence (q : G →* Q) (z : Q) : ShortComplex (Rep ℤ G) :=
  (cyclicAugmentationSequence Q z).map (Rep.resFunctor q)

theorem cyclicQuotientSequence_shortExact [Infinite Q] (q : G →* Q) (z : Q)
    (hz : ∀ x, x ∈ Subgroup.zpowers z) : (cyclicQuotientSequence Q q z).ShortExact :=
  (Rep.shortExact_res q).mpr (cyclicAugmentationSequence_shortExact Q z hz)

theorem cohomologicalDimension_bound_of_cyclicQuotientModule [Infinite Q]
    (q : G →* Q) (z : Q) (hz : ∀ x, x ∈ Subgroup.zpowers z) (d : ℕ)
    [HasProjectiveDimensionLE (Rep.res q (Rep.leftRegular ℤ Q)) d] :
    HasProjectiveDimensionLE (trivialIntegral G) (d + 1) := by
  apply (cyclicQuotientSequence_shortExact Q q z hz).hasProjectiveDimensionLT_X₃ (d + 1)
  · change HasProjectiveDimensionLE (Rep.res q (Rep.leftRegular ℤ Q)) d
    infer_instance
  · change HasProjectiveDimensionLT (Rep.res q (Rep.leftRegular ℤ Q)) (d + 1 + 1)
    exact hasProjectiveDimensionLT_of_ge _ (d + 1) (d + 1 + 1) (by omega)

end PolycyclicRecognition

end

end OAI
