import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalizedFreeRepresentation
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

namespace OAI

/-! # Functorial syzygies from the normalized free cover -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

abbrev normalizedSyzygy (A : Rep.{0} ℤ G) : Rep.{0} ℤ G :=
  kernel (normalizedFreeAugmentation A)

def normalizedSyzygyMap {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    normalizedSyzygy A ⟶ normalizedSyzygy B :=
  kernel.map (normalizedFreeAugmentation A) (normalizedFreeAugmentation B)
    (normalizedFreeMap f) f (normalizedFreeAugmentation_natural f).symm

@[reassoc (attr := simp)]
theorem normalizedSyzygyMap_ι {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    normalizedSyzygyMap f ≫ kernel.ι (normalizedFreeAugmentation B) =
      kernel.ι (normalizedFreeAugmentation A) ≫ normalizedFreeMap f := by
  apply kernel.lift_ι

def normalizedSyzygyFunctor : Rep.{0} ℤ G ⥤ Rep.{0} ℤ G where
  obj := normalizedSyzygy
  map := normalizedSyzygyMap
  map_id A := by
    apply (cancel_mono (kernel.ι (normalizedFreeAugmentation A))).mp
    simp only [normalizedSyzygyMap_ι, normalizedFreeMap_id, Category.comp_id, Category.id_comp]
  map_comp f g := by
    apply (cancel_mono (kernel.ι (normalizedFreeAugmentation _))).mp
    simp only [Category.assoc, normalizedSyzygyMap_ι, normalizedSyzygyMap_ι_assoc,
      normalizedFreeMap_comp]

@[simp]
theorem normalizedSyzygyMap_zero (A B : Rep.{0} ℤ G) :
    normalizedSyzygyMap (0 : A ⟶ B) = 0 := by
  apply (cancel_mono (kernel.ι (normalizedFreeAugmentation B))).mp
  simp

def normalizedSyzygySequence (A : Rep.{0} ℤ G) : ShortComplex (Rep.{0} ℤ G) :=
  ShortComplex.mk (kernel.ι (normalizedFreeAugmentation A))
    (normalizedFreeAugmentation A) (kernel.condition _)

theorem normalizedSyzygySequence_shortExact (A : Rep.{0} ℤ G) :
    (normalizedSyzygySequence A).ShortExact := by
  refine {
    exact := ShortComplex.exact_kernel (normalizedFreeAugmentation A)
    mono_f := ?_
    epi_g := ?_ }
  · change Mono (kernel.ι (normalizedFreeAugmentation A))
    infer_instance
  · change Epi (normalizedFreeAugmentation A)
    infer_instance

def normalizedSyzygySequenceMap {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    normalizedSyzygySequence A ⟶ normalizedSyzygySequence B where
  τ₁ := normalizedSyzygyMap f
  τ₂ := normalizedFreeMap f
  τ₃ := f
  comm₁₂ := normalizedSyzygyMap_ι f
  comm₂₃ := normalizedFreeAugmentation_natural f

def iteratedNormalizedSyzygy : ℕ → (Rep.{0} ℤ G ⥤ Rep.{0} ℤ G)
  | 0 => 𝟭 _
  | n + 1 => iteratedNormalizedSyzygy n ⋙ normalizedSyzygyFunctor

def normalizedSyzygyConnecting (A : Rep.{0} ℤ G) (n : ℕ) :
    groupCohomology ((iteratedNormalizedSyzygy n).obj A) n ⟶
      groupCohomology ((iteratedNormalizedSyzygy (n + 1)).obj A) (n + 1) :=
  groupCohomology.δ (normalizedSyzygySequence_shortExact
    ((iteratedNormalizedSyzygy n).obj A)) n (n + 1) rfl

end PolycyclicRecognition

end

end OAI
