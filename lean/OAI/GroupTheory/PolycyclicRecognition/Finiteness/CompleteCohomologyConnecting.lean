import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CompleteCohomologyStableMaps
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PresentationKernelMap

namespace OAI

/-! # Connecting maps for the completed coefficient theory

The kernel map of a projective cover and the syzygy dimension equivalence
give connecting maps for every short exact coefficient sequence. Naturality
holds because different choices of projective lift have the same stable map.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

def shiftedCompleteBoundary (p : ℕ) (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    ShiftedCompletedCohomology p S.X₃ →ₗ[ℤ] ShiftedCompletedCohomology (p + 1) S.X₁ :=
  (shiftedCompletedCohomologyMap (p + 1) (presentationKernelMap S hS)).comp
    (shiftedSyzygyAddEquiv p S.X₃).symm.toAddMonoidHom.toIntLinearMap

theorem shiftedCompleteBoundary_apply (p : ℕ) (S : ShortComplex (Rep.{0} ℤ G))
    (hS : S.ShortExact) (x : ShiftedCompletedCohomology p S.X₃) :
    shiftedCompleteBoundary p S hS x =
      shiftedCompletedCohomologyMap (p + 1) (presentationKernelMap S hS)
        ((shiftedSyzygyAddEquiv p S.X₃).symm x) := rfl

theorem shiftedCompleteBoundary_natural (p : ℕ)
    {S T : ShortComplex (Rep.{0} ℤ G)} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (x : ShiftedCompletedCohomology p S.X₃) :
    shiftedCompleteBoundary p T hT (shiftedCompletedCohomologyMap p φ.τ₃ x) =
      shiftedCompletedCohomologyMap (p + 1) φ.τ₁ (shiftedCompleteBoundary p S hS x) := by
  simp only [shiftedCompleteBoundary_apply, shiftedSyzygyEquiv_symm_natural]
  rw [← shiftedCompletedCohomologyMap_comp_apply, ← shiftedCompletedCohomologyMap_comp_apply,
    shiftedCompleteMap_eq_of_stable_eq _ _ _ (presentationKernelMap_stable_natural hS hT φ)]

theorem shiftedCompleteBoundary_comp_f (p : ℕ)
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (x : ShiftedCompletedCohomology p S.X₃) :
    shiftedCompletedCohomologyMap (p + 1) S.f (shiftedCompleteBoundary p S hS x) = 0 := by
  rw [shiftedCompleteBoundary_apply, ← shiftedCompletedCohomologyMap_comp_apply,
    shiftedCompleteMap_zero_of_stable_zero _ _ (presentationKernelMap_f_stable_zero S hS)]
  rfl

theorem shiftedCompleteBoundary_g_comp (p : ℕ)
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (x : ShiftedCompletedCohomology p S.X₂) :
    shiftedCompleteBoundary p S hS (shiftedCompletedCohomologyMap p S.g x) = 0 := by
  rw [shiftedCompleteBoundary_apply, shiftedSyzygyEquiv_symm_natural,
    ← shiftedCompletedCohomologyMap_comp_apply,
    shiftedCompleteMap_zero_of_stable_zero _ _ (presentationKernelMap_g_stable_zero S hS)]
  rfl

theorem shiftedCompleteBoundary_zero_of_section (p : ℕ)
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (s : S.X₃ ⟶ S.X₂) (hs : s ≫ S.g = 𝟙 S.X₃) :
    shiftedCompleteBoundary p S hS = 0 := by
  apply LinearMap.ext
  intro x
  rw [shiftedCompleteBoundary_apply,
    shiftedCompleteMap_zero_of_stable_zero _ _ (presentationKernelMap_stable_zero_of_section S hS s hs)]
  rfl

theorem shiftedCompleteBoundary_bijective_of_projective (p : ℕ)
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) [Projective S.X₂] :
    Function.Bijective (shiftedCompleteBoundary p S hS) := by
  obtain ⟨b, hab, hba⟩ := presentationKernelMap_stable_inverse S hS
  let e := shiftedCompleteStableIso (p + 1) (presentationKernelMap S hS) b hab hba
  have he : Function.Bijective (shiftedCompletedCohomologyMap (p + 1) (presentationKernelMap S hS)) :=
    e.toLinearEquiv.bijective
  exact he.comp (shiftedSyzygyAddEquiv p S.X₃).symm.bijective

end PolycyclicRecognition

end

end OAI
