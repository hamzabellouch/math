import OAI.GroupTheory.PolycyclicRecognition.Algebra.SmallCoefficientIdentityDimension

namespace OAI

/-! # Complete vanishing detects the dimension of the coefficient ring

The unit cocycles are carried by the connecting maps in the tensor tower.
If their completed class vanishes, an actual positive-degree identity class
vanishes and the previous splitting theorem applies.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Module.DirectLimit.module
variable (G : Type) [Group G] [Countable G]

def smallCoefficientGroupIdentity (n : ℕ) : (smallCoefficientTower G).cohomologyStage 0 n :=
  (coefficientNaturalCohomologyIso (normalizedProjectiveResolution (trivialIntegral G))
    ((smallCoefficientTower G).obj n) n).inv (smallCoefficientIdentityClass G n)

theorem smallCoefficientGroupIdentity_comparison (n : ℕ) :
    (coefficientNaturalCohomologyIso (normalizedProjectiveResolution (trivialIntegral G))
      ((smallCoefficientTower G).obj n) n).hom (smallCoefficientGroupIdentity G n) =
      smallCoefficientIdentityClass G n :=
  ConcreteCategory.congr_hom
    (coefficientNaturalCohomologyIso (normalizedProjectiveResolution (trivialIntegral G))
      ((smallCoefficientTower G).obj n) n).inv_hom_id (smallCoefficientIdentityClass G n)

theorem smallCoefficientGroupIdentity_connecting (n : ℕ) :
    ((smallCoefficientTower G).connecting 0 n).hom (smallCoefficientGroupIdentity G n) =
      smallCoefficientGroupIdentity G (n + 1) := by
  let T := smallCoefficientTower G
  let P := normalizedProjectiveResolution (trivialIntegral G)
  let e := coefficientNaturalCohomologyIso P (T.obj (n + 1)) (n + 1)
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  have he := ConcreteCategory.congr_hom
    (coefficientNaturalCohomologyIso_connecting P (T.sequence n) (T.shortExact n) n)
      (smallCoefficientGroupIdentity G n)
  change e.hom (((smallCoefficientTower G).connecting 0 n).hom
    (smallCoefficientGroupIdentity G n)) =
      (resolutionCoefficientSequence_shortExact P (T.sequence n) (T.shortExact n)).δ
        n (n + 1) rfl
        ((coefficientNaturalCohomologyIso P (T.obj n) n).hom
          (smallCoefficientGroupIdentity G n)) at he
  rw [smallCoefficientGroupIdentity_comparison] at he
  exact he.trans (smallCoefficientIdentityClass_connecting G n) |>.trans
    (smallCoefficientGroupIdentity_comparison G (n + 1)).symm

theorem smallCoefficientGroupIdentity_forward (i j : ℕ) (h : i ≤ j) :
    (smallCoefficientTower G).forward 0 i j h (smallCoefficientGroupIdentity G i) =
      smallCoefficientGroupIdentity G j := by
  induction h with
  | refl => exact Nat.leRecOn_self _
  | @step j h ih =>
    change Nat.leRecOn (C := (smallCoefficientTower G).cohomologyStage 0) _
      (fun {k} => ((smallCoefficientTower G).connecting 0 k).hom)
        (smallCoefficientGroupIdentity G i) = _
    rw [Nat.leRecOn_succ h]
    change ((smallCoefficientTower G).connecting 0 j).hom
      ((smallCoefficientTower G).forward 0 i j h (smallCoefficientGroupIdentity G i)) = _
    rw [ih, smallCoefficientGroupIdentity_connecting]

def smallCoefficientCompletedUnit : (smallCoefficientTower G).Cohomology 0 :=
  Module.DirectLimit.of ℤ ℕ _ ((smallCoefficientTower G).forward 0) 0
    (smallCoefficientGroupIdentity G 0)

theorem smallCoefficient_finite_dimension_of_completedUnit_zero
    (h : smallCoefficientCompletedUnit G = 0) :
    ∃ n : ℕ, HasProjectiveDimensionLE (smallCoefficientRepresentation G) n := by
  obtain ⟨j, _, hj⟩ := Module.DirectLimit.of.zero_exact h
  rw [smallCoefficientGroupIdentity_forward] at hj
  have hs : smallCoefficientGroupIdentity G (j + 1) = 0 := by
    rw [← smallCoefficientGroupIdentity_connecting, hj, map_zero]
  have hc : smallCoefficientIdentityClass G (j + 1) = 0 := by
    rw [← smallCoefficientGroupIdentity_comparison, hs, map_zero]
    rfl
  exact ⟨j + 1, smallCoefficient_finite_dimension_of_identityClass_zero G j hc⟩

theorem smallCoefficient_finite_dimension_of_complete_vanishing
    (h : Subsingleton (ShiftedCompletedCohomology 0 (smallCoefficientRepresentation G))) :
    ∃ n : ℕ, HasProjectiveDimensionLE (smallCoefficientRepresentation G) n := by
  apply smallCoefficient_finite_dimension_of_completedUnit_zero G
  let e := tensorNormalizedTowerCompletion (smallCoefficientRepresentation G) 0
  apply e.injective
  exact h.elim _ _

end PolycyclicRecognition

end

end OAI
