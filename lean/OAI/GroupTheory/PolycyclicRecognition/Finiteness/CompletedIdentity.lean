import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalizedIdentityConnecting
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CoefficientConnectingNaturality

namespace OAI

/-! # The complete identity detects finite integral cohomological dimension

The class of the augmentation is transported into ordinary cohomology. Its
successive connecting images are the syzygy identity classes. Vanishing of
its image in complete cohomology therefore forces a projective syzygy.
No vanishing from FP-infinity is assumed or asserted.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (G : Type) [Group G]

def normalizedGroupIdentityClass (n : ℕ) :
    normalizedCohomologyStage (trivialIntegral G) n :=
  (coefficientNaturalCohomologyIso (normalizedProjectiveResolution (trivialIntegral G))
    ((iteratedNormalizedSyzygy n).obj (trivialIntegral G)) n).inv
      (normalizedIdentityClass (trivialIntegral G) n)

@[simp]
theorem normalizedGroupIdentityClass_comparison (n : ℕ) :
    (coefficientNaturalCohomologyIso (normalizedProjectiveResolution (trivialIntegral G))
      ((iteratedNormalizedSyzygy n).obj (trivialIntegral G)) n).hom
        (normalizedGroupIdentityClass G n) = normalizedIdentityClass (trivialIntegral G) n := by
  exact ConcreteCategory.congr_hom
    (coefficientNaturalCohomologyIso (normalizedProjectiveResolution (trivialIntegral G))
      ((iteratedNormalizedSyzygy n).obj (trivialIntegral G)) n).inv_hom_id
        (normalizedIdentityClass (trivialIntegral G) n)

theorem normalizedSyzygyConnecting_identity (n : ℕ) :
    normalizedSyzygyConnecting (trivialIntegral G) n (normalizedGroupIdentityClass G n) =
      normalizedGroupIdentityClass G (n + 1) := by
  let P := normalizedProjectiveResolution (trivialIntegral G)
  let S := normalizedSyzygySequence ((iteratedNormalizedSyzygy n).obj (trivialIntegral G))
  let e := coefficientNaturalCohomologyIso P S.X₁ (n + 1)
  apply ((ModuleCat.mono_iff_injective e.hom).mp inferInstance)
  have he := ConcreteCategory.congr_hom
    (coefficientNaturalCohomologyIso_connecting P S
      (normalizedSyzygySequence_shortExact ((iteratedNormalizedSyzygy n).obj
        (trivialIntegral G))) n) (normalizedGroupIdentityClass G n)
  change e.hom (normalizedSyzygyConnecting (trivialIntegral G) n
      (normalizedGroupIdentityClass G n)) = normalizedIdentityConnecting G n
        ((coefficientNaturalCohomologyIso (normalizedProjectiveResolution (trivialIntegral G))
          ((iteratedNormalizedSyzygy n).obj (trivialIntegral G)) n).hom
            (normalizedGroupIdentityClass G n)) at he
  rw [normalizedGroupIdentityClass_comparison] at he
  exact he.trans (normalizedIdentityConnecting_class G n) |>.trans
    (normalizedGroupIdentityClass_comparison G (n + 1)).symm

theorem normalizedCohomologyForward_identity (i j : ℕ) (h : i ≤ j) :
    normalizedCohomologyForward (trivialIntegral G) i j h (normalizedGroupIdentityClass G i) =
      normalizedGroupIdentityClass G j := by
  induction h with
  | refl => exact Nat.leRecOn_self _
  | @step j h ih =>
    change Nat.leRecOn (C := normalizedCohomologyStage (trivialIntegral G)) _
      (fun {k} => (normalizedSyzygyConnecting (trivialIntegral G) k).hom)
        (normalizedGroupIdentityClass G i) = _
    rw [Nat.leRecOn_succ h]
    change normalizedSyzygyConnecting (trivialIntegral G) j
      (normalizedCohomologyForward (trivialIntegral G) i j h
        (normalizedGroupIdentityClass G i)) = _
    rw [ih]
    exact normalizedSyzygyConnecting_identity G j

def completedIdentity : CompletedCohomology (trivialIntegral G) :=
  Module.DirectLimit.of ℤ ℕ _ (normalizedCohomologyForward (trivialIntegral G)) 0
    (normalizedGroupIdentityClass G 0)

theorem completedIdentity_eq_zero_iff :
    completedIdentity G = 0 ↔ HasFiniteIntegralCohomologicalDimension G := by
  constructor
  · intro h
    obtain ⟨j, hj, he⟩ := Module.DirectLimit.of.zero_exact h
    rw [normalizedCohomologyForward_identity] at he
    have hs : normalizedGroupIdentityClass G (j + 1) = 0 := by
      rw [← normalizedSyzygyConnecting_identity, he, map_zero]
    have hc : normalizedIdentityClass (trivialIntegral G) (j + 1) = 0 := by
      rw [← normalizedGroupIdentityClass_comparison, hs, map_zero]
      rfl
    exact finiteDimension_of_normalizedIdentityClass_zero j hc
  · rintro ⟨d, hd⟩
    let := hd
    let := completedCohomology_subsingleton_of_finite_projectiveDimension (trivialIntegral G) d
    exact Subsingleton.elim _ _

theorem completedCohomology_trivial_subsingleton_iff :
    Subsingleton (CompletedCohomology (trivialIntegral G)) ↔
      HasFiniteIntegralCohomologicalDimension G := by
  constructor
  · intro h
    exact (completedIdentity_eq_zero_iff G).mp (h.elim _ _)
  · rintro ⟨d, hd⟩
    let := hd
    exact completedCohomology_subsingleton_of_finite_projectiveDimension (trivialIntegral G) d

end PolycyclicRecognition

end

end OAI
