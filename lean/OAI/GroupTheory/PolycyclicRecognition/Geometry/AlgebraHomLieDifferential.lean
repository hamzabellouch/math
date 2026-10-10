import OAI.GroupTheory.PolycyclicRecognition.Geometry.AutomaticSmoothAlgebraHom
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ChartedVectorFieldBracket
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.NoncommRing

namespace OAI

/-! # The actual differential of an algebra-unit homomorphism

Left-invariant vector fields are related to left multiplication in the
algebra. Preservation of their brackets gives the matrix commutator law.
-/

noncomputable section
namespace PolycyclicRecognition

open Function VectorField
open scoped Manifold ContDiff

variable {E G A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedRing A] [NormedAlgebra ℝ A]

def unitsHomDifferential (ρ : G →* Aˣ) (g : G) : E →L[ℝ] A :=
  mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, A)) (fun x => (ρ x : A)) g

theorem mfderiv_unitsHom_invariant
    (ρ : G →* Aˣ)
    (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, A)) ∞ (fun g => (ρ g : A)))
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (g : G) :
    unitsHomDifferential (E := E) ρ g (mulInvariantVectorField v g) =
      (ρ g : A) * unitsHomDifferential (E := E) ρ 1 v := by
  let f : G → A := fun x => (ρ x : A)
  let L : A →L[ℝ] A := ContinuousLinearMap.mul ℝ A (ρ g : A)
  have hl : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun x : G => g * x) 1 :=
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (a := g) :
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (fun x : G => g * x)).mdifferentiableAt (by simp)
  have h₁ := ((hf (g * 1)).mdifferentiableAt (by simp)).hasMFDerivAt.comp 1 hl.hasMFDerivAt
  have h₂ := L.hasFDerivAt.hasMFDerivAt.comp (1 : G)
    ((hf 1).mdifferentiableAt (by simp)).hasMFDerivAt
  have heq : f ∘ (fun x : G => g * x) = L ∘ f := by
    funext x
    exact congrArg (fun u : Aˣ => (u : A)) (ρ.map_mul g x)
  change HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, A)) (f ∘ (fun x : G => g * x)) 1 _ at h₁
  rw [heq] at h₁
  have hd := h₁.mfderiv.symm.trans h₂.mfderiv
  have hv := congrArg (fun D : E →L[ℝ] A => D v) hd
  have hbase : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, A)) f (g * 1) : E →L[ℝ] A) =
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, A)) f g := by
    congr 1
    exact mul_one g
  change (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, A)) f (g * 1))
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun x : G => g * x) 1) v) =
      L ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, A)) f 1) v) at hv
  rw [hbase] at hv
  exact hv

theorem lieBracket_rightMultiplication (v w a : A) :
    lieBracket ℝ (fun x : A => x * v) (fun x : A => x * w) a =
      a * (v * w - w * v) := by
  let Rv : A →L[ℝ] A := (ContinuousLinearMap.mul ℝ A).flip v
  let Rw : A →L[ℝ] A := (ContinuousLinearMap.mul ℝ A).flip w
  have hv : fderiv ℝ (fun x : A => x * v) a = Rv := Rv.hasFDerivAt.fderiv
  have hw : fderiv ℝ (fun x : A => x * w) a = Rw := Rw.hasFDerivAt.fderiv
  unfold lieBracket
  rw [hv, hw]
  change (a * v) * w - (a * w) * v = a * (v * w - w * v)
  noncomm_ring

theorem unitsHomDifferential_map_bracket [CompleteSpace E]
    (ρ : G →* Aˣ)
    (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, A)) ∞ (fun g => (ρ g : A)))
    (v w : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    unitsHomDifferential (E := E) ρ 1 (⁅v, w⁆ : GroupLieAlgebra (𝓘(ℝ, E)) G) =
      unitsHomDifferential (E := E) ρ 1 v * unitsHomDifferential (E := E) ρ 1 w -
      unitsHomDifferential (E := E) ρ 1 w * unitsHomDifferential (E := E) ρ 1 v := by
  let D := unitsHomDifferential (E := E) ρ 1
  have hb := mfderiv_mlieBracket_of_related (V' := fun a : A => a * D v)
    (W' := fun a : A => a * D w) hf
    (contMDiff_invariantVectorField_infty v) (contMDiff_invariantVectorField_infty w)
    (differentiable_id.mul_const (D v)) (differentiable_id.mul_const (D w))
    (fun x => mfderiv_unitsHom_invariant ρ hf v x)
    (fun x => mfderiv_unitsHom_invariant ρ hf w x) (1 : G)
  simp only [map_one, Units.val_one, lieBracket_rightMultiplication, one_mul] at hb
  change unitsHomDifferential (E := E) ρ 1 (⁅v, w⁆ : GroupLieAlgebra (𝓘(ℝ, E)) G) =
    D v * D w - D w * D v at hb
  exact hb

attribute [local instance 100] LieRing.ofAssociativeRing

def unitsHomLieDifferential [CompleteSpace E]
    (ρ : G →* Aˣ)
    (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, A)) ∞ (fun g => (ρ g : A))) :
    GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ A where
  toLinearMap := (unitsHomDifferential (E := E) ρ 1).toLinearMap
  map_lie' := by
    intro v w
    exact unitsHomDifferential_map_bracket ρ hf v w

theorem hasMFDerivAt_unitsHomLieDifferential [FiniteDimensional ℝ E]
    (ρ : G →* Aˣ)
    (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, A)) ∞ (fun g => (ρ g : A))) :
    HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, A)) (fun g => (ρ g : A)) 1
      (unitsHomLieDifferential ρ hf).toLinearMap.toContinuousLinearMap := by
  apply ((hf 1).mdifferentiableAt (by simp)).hasMFDerivAt.congr_mfderiv
  ext v
  exact congrFun
    (LinearMap.coe_toContinuousLinearMap'
      (unitsHomDifferential (E := E) ρ 1).toLinearMap).symm v

end PolycyclicRecognition

end

end OAI
