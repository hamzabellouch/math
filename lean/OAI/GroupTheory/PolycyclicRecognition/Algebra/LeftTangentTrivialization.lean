import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothExponentialCurve
import Mathlib.Geometry.Manifold.Riemannian.Basic

namespace OAI

/-! # Left translation identifies the tangent fibers

The differential of translation back to the identity is an actual continuous
linear equivalence. Its matrix in any fixed local tangent chart varies
smoothly. These facts supply the frame for the left-invariant metric.
-/

noncomputable section
namespace PolycyclicRecognition

open Bundle Function
open scoped Manifold ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ∞ G]

def leftLogDerivative (g : G) : E →L[ℝ] E :=
  mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => g⁻¹ * h) g

def leftTranslateDerivative (g : G) : E →L[ℝ] E :=
  mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => g * h) 1

theorem leftTranslate_leftLog (g : G) :
    (leftTranslateDerivative (E := E) g).comp (leftLogDerivative g) =
      ContinuousLinearMap.id ℝ E := by
  have he : (fun h : G => g * (g⁻¹ * h)) = id := by ext h; simp
  have hd := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
    (I'' := 𝓘(ℝ, E)) g
    ((contMDiff_mul_left (a := g) (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableAt (by simp))
    ((contMDiff_mul_left (a := g⁻¹) (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableAt (by simp))
  have hid : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => g * (g⁻¹ * h)) g :
      E →L[ℝ] E) = ContinuousLinearMap.id ℝ E := by
    let D : (G → G) → (E →L[ℝ] E) := fun f => mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) f g
    have hi : D id = ContinuousLinearMap.id ℝ E := mfderiv_id
    exact (congrArg D he).trans hi
  have hb : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => g * h) (g⁻¹ * g) :
      E →L[ℝ] E) = leftTranslateDerivative (E := E) g := by
    let D : G → (E →L[ℝ] E) := fun x => mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => g * h) x
    exact congrArg D (inv_mul_cancel g)
  exact (congrArg (fun f : E →L[ℝ] E => f.comp (leftLogDerivative g)) hb).symm.trans
    (hd.symm.trans hid)

theorem leftLog_leftTranslate (g : G) :
    (leftLogDerivative (E := E) g).comp (leftTranslateDerivative g) =
      ContinuousLinearMap.id ℝ E := by
  have he : (fun h : G => g⁻¹ * (g * h)) = id := by ext h; simp
  have hd := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
    (I'' := 𝓘(ℝ, E)) (1 : G)
    ((contMDiff_mul_left (a := g⁻¹) (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableAt (by simp))
    ((contMDiff_mul_left (a := g) (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableAt (by simp))
  have hid : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => g⁻¹ * (g * h)) 1 :
      E →L[ℝ] E) = ContinuousLinearMap.id ℝ E := by
    let D : (G → G) → (E →L[ℝ] E) := fun f => mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) f 1
    have hi : D id = ContinuousLinearMap.id ℝ E := mfderiv_id
    exact (congrArg D he).trans hi
  have ha : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => g⁻¹ * h) (g * 1) :
      E →L[ℝ] E) = leftLogDerivative (E := E) g := by
    let D : G → (E →L[ℝ] E) := fun x => mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => g⁻¹ * h) x
    exact congrArg D (mul_one g)
  exact (congrArg (fun f : E →L[ℝ] E => f.comp (leftTranslateDerivative g)) ha).symm.trans
    (hd.symm.trans hid)

def leftTangentEquiv (g : G) : E ≃L[ℝ] E where
  toFun := leftLogDerivative g
  invFun := leftTranslateDerivative g
  map_add' := (leftLogDerivative g).map_add
  map_smul' := (leftLogDerivative g).map_smul
  left_inv v := congrArg (fun f : E →L[ℝ] E => f v) (leftTranslate_leftLog g)
  right_inv v := congrArg (fun f : E →L[ℝ] E => f v) (leftLog_leftTranslate g)
  continuous_toFun := (leftLogDerivative g).continuous
  continuous_invFun := (leftTranslateDerivative g).continuous

theorem leftLogDerivative_mul (g h : G) :
    (leftLogDerivative (E := E) (g * h)).comp
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun k : G => g * k) h) =
      leftLogDerivative (E := E) h := by
  have he : (fun k : G => (g * h)⁻¹ * (g * k)) = (fun k : G => h⁻¹ * k) := by
    funext k
    simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  have hc := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
    (I'' := 𝓘(ℝ, E)) h
    ((contMDiff_mul_left (a := (g * h)⁻¹) (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableAt (by simp))
    ((contMDiff_mul_left (a := g) (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableAt (by simp))
  let D : (G → G) → (E →L[ℝ] E) := fun f => mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) f h
  exact hc.symm.trans (congrArg D he)

theorem contMDiffAt_leftLogDerivative (g₀ : G) :
    ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E →L[ℝ] E)) ∞
      (inTangentCoordinates (𝓘(ℝ, E)) (𝓘(ℝ, E)) id (fun _ : G => (1 : G))
        (fun g => leftLogDerivative (E := E) g) g₀) g₀ := by
  have hmul : ContMDiff ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (𝓘(ℝ, E)) ∞
      (fun p : G × G => p.1⁻¹ * p.2) := contMDiff_fst.inv.mul contMDiff_snd
  have hd := (hmul (g₀, g₀)).mfderiv (fun g h : G => g⁻¹ * h) id
    contMDiffAt_id (m := ∞) (by simp)
  have heq : inTangentCoordinates (𝓘(ℝ, E)) (𝓘(ℝ, E)) id
      (fun g : G => g⁻¹ * g)
      (fun g => mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => g⁻¹ * h) g) g₀ =
      inTangentCoordinates (𝓘(ℝ, E)) (𝓘(ℝ, E)) id (fun _ : G => (1 : G))
        (fun g => leftLogDerivative (E := E) g) g₀ := by
    funext g
    let B : G → G → (E →L[ℝ] E) := fun y₀ y =>
      (trivializationAt E (TangentSpace (𝓘(ℝ, E))) y₀).continuousLinearMapAt ℝ y
    have hb : B (g₀⁻¹ * g₀) (g⁻¹ * g) = B 1 1 :=
      congrArg₂ B (inv_mul_cancel g₀) (inv_mul_cancel g)
    exact congrArg (fun b : E →L[ℝ] E => b.comp
      ((leftLogDerivative (E := E) g).comp
        ((trivializationAt E (TangentSpace (𝓘(ℝ, E))) g₀).symmL ℝ g))) hb
  have hd' : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E →L[ℝ] E)) ∞
      (inTangentCoordinates (𝓘(ℝ, E)) (𝓘(ℝ, E)) id
        (fun g : G => g⁻¹ * g)
        (fun g => mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => g⁻¹ * h) g) g₀) g₀ := hd
  rw [heq] at hd'
  exact hd'

end PolycyclicRecognition

end

end OAI
