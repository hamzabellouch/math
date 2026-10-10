import OAI.Analysis.Pureness.Stabilization.ZeroIdeal
import Mathlib.Analysis.CStarAlgebra.Hom

namespace OAI
noncomputable section
open scoped ENNReal NNReal CStarAlgebra
namespace CuntzTrace
variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

namespace Positive

def map (f : A →⋆ₙₐ[ℂ] B) (a : Positive A) : Positive B :=
  ⟨f a.1, map_nonneg f a.2⟩
end Positive

namespace ExtendedTrace

def pullback (τ : ExtendedTrace B) (f : A →⋆ₙₐ[ℂ] B) : ExtendedTrace A where
  toFun a := τ (Positive.map f a)
  map_zero := by
    have h : Positive.map f Positive.zero = Positive.zero := Subtype.ext (_root_.map_zero f)
    rw [h, τ.map_zero]
  map_add a b := by
    have h : Positive.map f (Positive.add a b) =
        Positive.add (Positive.map f a) (Positive.map f b) := Subtype.ext (_root_.map_add f _ _)
    rw [h, τ.map_add]
  map_smul r a := by
    have h : Positive.map f (Positive.smul r a) = Positive.smul r (Positive.map f a) := by
      apply Subtype.ext
      change f ((r : ℝ) • a.1) = (r : ℝ) • f a.1
      simpa only [← Complex.coe_smul] using _root_.map_smul f (r : ℂ) a.1
    rw [h, τ.map_smul]
  tracial x := by
    have h₁ : Positive.map f (Positive.starMul x) = Positive.starMul (f x) := by
      apply Subtype.ext
      simp [Positive.map, Positive.starMul, map_mul, map_star]
    have h₂ : Positive.map f (Positive.mulStar x) = Positive.mulStar (f x) := by
      apply Subtype.ext
      simp [Positive.map, Positive.mulStar, map_mul, map_star]
    rw [h₁, h₂, τ.tracial]
  lowerSemicontinuous := τ.lowerSemicontinuous.comp
    (((map_continuous f).comp continuous_subtype_val).subtype_mk _)

@[simp] theorem pullback_apply (τ : ExtendedTrace B) (f : A →⋆ₙₐ[ℂ] B) (a : Positive A) :
    pullback τ f a = τ (Positive.map f a) := rfl

def kernelWeight (f : A →⋆ₙₐ[ℂ] B) : ExtendedTrace A := (zeroIdealWeight B).pullback f

theorem kernelWeight_eq_zero (f : A →⋆ₙₐ[ℂ] B) (a : Positive A) :
    kernelWeight f a = 0 ↔ f a.1 = 0 := zeroIdealWeight_eq_zero B _

theorem kernelWeight_lt_top (f : A →⋆ₙₐ[ℂ] B) (a : Positive A) :
    kernelWeight f a < ∞ ↔ f a.1 = 0 := zeroIdealWeight_lt_top B _

theorem injective_of_surjective_pullback (f : A →⋆ₙₐ[ℂ] B)
    (h : Function.Surjective (fun τ : ExtendedTrace B => τ.pullback f)) :
    Function.Injective f := by
  obtain ⟨τ, hτ⟩ := h (zeroIdealWeight A)
  have hker (x : A) (hx : f x = 0) : x = 0 := by
    have hp : Positive.map f (Positive.starMul x) = Positive.zero := by
      apply Subtype.ext
      simp [Positive.map, Positive.starMul, Positive.zero, _root_.map_mul,
        map_star, hx]
    have hz : zeroIdealWeight A (Positive.starMul x) = 0 := by
      rw [← hτ, pullback_apply, hp]
      exact τ.map_zero
    exact (CStarRing.star_mul_self_eq_zero_iff x).mp
      ((zeroIdealWeight_eq_zero A _).mp hz)
  intro x y hxy
  apply sub_eq_zero.mp
  apply hker
  simp [_root_.map_sub, hxy]

end ExtendedTrace
end CuntzTrace

end

end OAI
