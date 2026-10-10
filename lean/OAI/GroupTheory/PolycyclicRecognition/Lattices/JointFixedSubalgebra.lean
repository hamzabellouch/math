import OAI.GroupTheory.PolycyclicRecognition.Algebra.SemisimpleMovingAction
import Mathlib.RingTheory.Nilpotent.Lemmas

namespace OAI

/-! # The joint fixed algebra and its unipotent quotient-lift actions -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] polynomialSubalgebraGroup
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

def jointFixedLieSubalgebra (ss : List (L ≃ₗ⁅ℝ⁆ L)) : LieSubalgebra ℝ L where
  toSubmodule :=
    { carrier := {x | ∀ S ∈ ss, S x = x}
      zero_mem' := by intro S _; exact map_zero S
      add_mem' := by
        intro x y hx hy S hS
        rw [map_add, hx S hS, hy S hS]
      smul_mem' := by
        intro r x hx S hS
        rw [map_smul, hx S hS] }
  lie_mem' := by
    intro x y hx hy S hS
    rw [S.map_lie, hx S hS, hy S hS]

omit [FiniteDimensional ℝ L] in
theorem mem_jointFixedLieSubalgebra (ss : List (L ≃ₗ⁅ℝ⁆ L)) (x : L) :
    x ∈ jointFixedLieSubalgebra ss ↔ ∀ S ∈ ss, S x = x := Iff.rfl

omit [FiniteDimensional ℝ L] in
theorem commuting_lieEquiv_preserves_jointFixed (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (T : L ≃ₗ⁅ℝ⁆ L) (hT : ∀ S ∈ ss, Commute S.toLinearMap T.toLinearMap)
    (x : L) (hx : x ∈ jointFixedLieSubalgebra ss) : T x ∈ jointFixedLieSubalgebra ss := by
  apply (mem_jointFixedLieSubalgebra ss _).mpr
  intro S hS
  have hh : S (T x) = T (S x) := LinearMap.congr_fun (hT S hS).eq x
  rw [hh, (mem_jointFixedLieSubalgebra ss x).mp hx S hS]

def jointFixedLinearAction (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (T : L ≃ₗ⁅ℝ⁆ L) (hT : ∀ S ∈ ss, Commute S.toLinearMap T.toLinearMap) :
    Module.End ℝ (jointFixedLieSubalgebra ss) :=
  T.toLinearMap.restrict (commuting_lieEquiv_preserves_jointFixed ss T hT)

def jointFixedLieAction (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (T : L ≃ₗ⁅ℝ⁆ L) (hT : ∀ S ∈ ss, Commute S.toLinearMap T.toLinearMap) :
    jointFixedLieSubalgebra ss ≃ₗ⁅ℝ⁆ jointFixedLieSubalgebra ss where
  toFun x := ⟨T x, commuting_lieEquiv_preserves_jointFixed ss T hT x x.property⟩
  invFun x := ⟨T.symm x, commuting_lieEquiv_preserves_jointFixed ss T.symm
    (fun S hS => linear_commute_symm T.toLinearEquiv S.toLinearMap (hT S hS)) x x.property⟩
  left_inv x := Subtype.ext (T.symm_apply_apply x)
  right_inv x := Subtype.ext (T.apply_symm_apply x)
  map_add' x y := Subtype.ext (T.map_add x y)
  map_smul' r x := Subtype.ext (T.map_smul r x)
  map_lie' {x y} := Subtype.ext (T.map_lie x y)

omit [FiniteDimensional ℝ L] in
theorem jointFixedLinearAction_unipotent (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (S U T : L ≃ₗ⁅ℝ⁆ L) (hS : S ∈ ss)
    (hT : ∀ R ∈ ss, Commute R.toLinearMap T.toLinearMap)
    (hU : IsNilpotent (U.toLinearMap - 1)) (hSU : Commute S.toLinearMap U.toLinearMap)
    (hTU : T.toLinearMap = S.toLinearMap * U.toLinearMap) :
    IsNilpotent (jointFixedLinearAction ss T hT - 1) := by
  have hUx (x : L) (hx : x ∈ jointFixedLieSubalgebra ss) : T x = U x := by
    have hh : T x = S (U x) := LinearMap.congr_fun hTU x
    have hc : S (U x) = U (S x) := LinearMap.congr_fun hSU.eq x
    rw [hh, hc, (mem_jointFixedLieSubalgebra ss x).mp hx S hS]
  have hUp : ∀ x ∈ (jointFixedLieSubalgebra ss).toSubmodule, U x ∈ jointFixedLieSubalgebra ss := by
    intro x hx
    rw [← hUx x hx]
    exact commuting_lieEquiv_preserves_jointFixed ss T hT x hx
  have hdiffp : ∀ x ∈ (jointFixedLieSubalgebra ss).toSubmodule,
      (U.toLinearMap - 1) x ∈ jointFixedLieSubalgebra ss := by
    intro x hx
    exact (jointFixedLieSubalgebra ss).sub_mem (hUp x hx) hx
  have hn := Module.End.isNilpotent.restrict hdiffp hU
  have he : jointFixedLinearAction ss T hT - 1 = (U.toLinearMap - 1).restrict hdiffp := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change T x - (x : L) = U x - (x : L)
    rw [hUx x x.property]
  rwa [he]

variable [P : PolynomialExponentialCoordinates L]

def jointFixedGroupAction (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (T : L ≃ₗ⁅ℝ⁆ L) (hT : ∀ S ∈ ss, Commute S.toLinearMap T.toLinearMap) :
    MulAut (jointFixedLieSubalgebra ss) :=
  polynomialSubalgebraEquiv _ _ T (commuting_lieEquiv_preserves_jointFixed ss T hT)
    (commuting_lieEquiv_preserves_jointFixed ss T.symm
      (fun S hS => linear_commute_symm T.toLinearEquiv S.toLinearMap (hT S hS)))

end PolycyclicRecognition

end

end OAI
