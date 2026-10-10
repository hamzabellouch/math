import OAI.Analysis.Nonexpansive.Basic
import Mathlib.Topology.Constructions

namespace OAI

/-!
# Selfmaps with the topology of pointwise weak convergence

The domain remains the norm subtype.  The codomain is the separate weak
carrier, so the function space has exactly the product weak topology.
Composition converts the inner value back to a domain point algebraically.
-/

noncomputable section

open Set
open scoped Topology

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Actual selfmaps of `K`, with pointwise weak topology on their values. -/
abbrev WeakSelfMap (K : Set X) := K → WeakCarrier K

namespace WeakSelfMap

variable {K : Set X}

def ofNorm (f : K → K) : WeakSelfMap K := fun a => normToWeak K (f a)

def toNorm (f : WeakSelfMap K) : K → K := fun a => (normToWeak K).symm (f a)

@[simp] theorem toNorm_ofNorm (f : K → K) : toNorm (ofNorm f) = f := by
  funext a
  exact (normToWeak K).symm_apply_apply (f a)

@[simp] theorem ofNorm_toNorm (f : WeakSelfMap K) : ofNorm (toNorm f) = f := by
  funext a
  exact (normToWeak K).apply_symm_apply (f a)

theorem toNorm_injective : Function.Injective (toNorm (K := K)) := by
  intro f g h
  simpa only [ofNorm_toNorm] using congrArg ofNorm h

theorem ofNorm_injective : Function.Injective (ofNorm (K := K)) := by
  intro f g h
  simpa only [toNorm_ofNorm] using congrArg toNorm h

/-- Pointwise weak values in their ambient vector space. -/
def weakAmbient (f : WeakSelfMap K) : K → WeakSpace ℝ X := fun a => f a

/-- The same actual values in the original normed space. -/
def normAmbient (f : WeakSelfMap K) : K → X := fun a => (toNorm f a : X)

theorem weakAmbient_injective : Function.Injective (weakAmbient (K := K)) := by
  intro f g h
  funext a
  exact Subtype.ext (congrFun h a)

theorem continuous_weakAmbient : Continuous (weakAmbient (K := K)) :=
  continuous_pi fun a => continuous_subtype_val.comp (continuous_apply a)

theorem continuous_normToWeak (K : Set X) : Continuous (normToWeak K) := by
  exact ((toWeakSpaceCLM ℝ X).continuous.comp continuous_subtype_val).subtype_mk _

/-- Norm-pointwise convergence implies weak-pointwise convergence. -/
theorem continuous_ofNorm : Continuous (ofNorm (K := K)) :=
  continuous_pi fun a => (continuous_normToWeak K).comp (continuous_apply a)

/-- Composition is actual composition of the underlying norm selfmaps. -/
def comp (f g : WeakSelfMap K) : WeakSelfMap K := fun a => f (toNorm g a)

@[simp] theorem toNorm_comp (f g : WeakSelfMap K) :
    toNorm (comp f g) = toNorm f ∘ toNorm g := rfl

@[simp] theorem ofNorm_comp (f g : K → K) :
    ofNorm (f ∘ g) = comp (ofNorm f) (ofNorm g) := by
  funext a
  simp [ofNorm, comp, toNorm]

theorem comp_assoc (f g h : WeakSelfMap K) :
    comp (comp f g) h = comp f (comp g h) := rfl

/-- Only the right argument is fixed.  The inner map need not be weakly continuous. -/
theorem continuous_comp_right (g : WeakSelfMap K) :
    Continuous (fun f : WeakSelfMap K => comp f g) :=
  Pi.continuous_precomp (toNorm g)

/-- Coordinatewise algebraic change from norm values to weak values. -/
def weakify : (K → X) ≃ₗ[ℝ] (K → WeakSpace ℝ X) :=
  LinearEquiv.piCongrRight fun _ => toWeakSpace ℝ X

@[simp] theorem weakify_apply (f : K → X) (a : K) :
    weakify f a = toWeakSpace ℝ X (f a) := rfl

@[simp] theorem weakAmbient_ofNorm (f : K → K) :
    weakAmbient (ofNorm f) = weakify (fun a => (f a : X)) := rfl

theorem convex_weakAmbient_image_ofNorm {B : Set (K → K)}
    (hB : Convex ℝ ((fun f : K → K => fun a => (f a : X)) '' B)) :
    Convex ℝ (weakAmbient '' (ofNorm '' B)) := by
  have heq : weakAmbient '' (ofNorm '' B) =
      weakify '' ((fun f : K → K => fun a => (f a : X)) '' B) := by
    rw [Set.image_image, Set.image_image]
    rfl
  rw [heq]
  exact hB.linear_image weakify.toLinearMap

end WeakSelfMap

end ReflexiveFixedPoints

end

end OAI
