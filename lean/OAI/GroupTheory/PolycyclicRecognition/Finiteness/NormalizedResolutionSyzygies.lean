import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalizedProjectiveResolution

namespace OAI

/-! # Quotient terms of the normalized projective resolution -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

def normalizedResolutionProjection (A : Rep.{0} ℤ G) (n : ℕ) :
    (normalizedResolutionComplex A).X n ⟶ (iteratedNormalizedSyzygy n).obj A :=
  normalizedFreeAugmentation ((iteratedNormalizedSyzygy n).obj A)

theorem normalizedResolution_d_projection (A : Rep.{0} ℤ G) (n : ℕ) :
    (normalizedResolutionComplex A).d (n + 1) n ≫ normalizedResolutionProjection A n = 0 := by
  rw [normalizedResolutionComplex_d]
  exact normalizedFreeStep_comp ((iteratedNormalizedSyzygy n).obj A)

def normalizedResolutionCokernelSequence (A : Rep.{0} ℤ G) (n : ℕ) :
    ShortComplex (Rep.{0} ℤ G) :=
  ShortComplex.mk ((normalizedResolutionComplex A).d (n + 1) n)
    (normalizedResolutionProjection A n) (normalizedResolution_d_projection A n)

theorem normalizedResolutionCokernelSequence_exact (A : Rep.{0} ℤ G) (n : ℕ) :
    (normalizedResolutionCokernelSequence A n).Exact := by
  simp only [normalizedResolutionCokernelSequence, normalizedResolutionComplex_d,
    normalizedResolutionProjection]
  exact normalizedFreeStep_exact ((iteratedNormalizedSyzygy n).obj A)

def normalizedResolutionOpcyclesIso (A : Rep.{0} ℤ G) (n : ℕ) :
    (normalizedResolutionComplex A).opcycles n ≅ (iteratedNormalizedSyzygy n).obj A := by
  let S := normalizedResolutionCokernelSequence A n
  let : Epi S.g := by
    change Epi (normalizedFreeAugmentation ((iteratedNormalizedSyzygy n).obj A))
    infer_instance
  exact ((normalizedResolutionComplex A).opcyclesIsCokernel (n + 1) n (by simp)).coconePointUniqueUpToIso
    (normalizedResolutionCokernelSequence_exact A n).gIsCokernel

@[reassoc (attr := simp)]
theorem normalizedResolutionOpcyclesIso_projection (A : Rep.{0} ℤ G) (n : ℕ) :
    (normalizedResolutionComplex A).pOpcycles n ≫ (normalizedResolutionOpcyclesIso A n).hom =
      normalizedResolutionProjection A n := by
  let S := normalizedResolutionCokernelSequence A n
  let : Epi S.g := by
    change Epi (normalizedFreeAugmentation ((iteratedNormalizedSyzygy n).obj A))
    infer_instance
  let h₁ := (normalizedResolutionComplex A).opcyclesIsCokernel (n + 1) n (by simp)
  let h₂ := (normalizedResolutionCokernelSequence_exact A n).gIsCokernel
  exact h₁.comp_coconePointUniqueUpToIso_hom h₂ WalkingParallelPair.one

end PolycyclicRecognition

end

end OAI
