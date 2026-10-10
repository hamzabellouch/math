import Mathlib

namespace OAI

noncomputable section

namespace KKProjectionSupport

noncomputable section

variable {A : Type*} [CStarAlgebra A]

def Partial (v : A) : Prop := v*star v*v = v

theorem partial_initial {v : A} (hv : Partial v) : IsStarProjection (star v*v) := by
  constructor
  · change (star v*v)*(star v*v) = star v*v
    calc
      (star v*v)*(star v*v) = star v*(v*star v*v) := by simp only [mul_assoc]
      _ = star v*v := by rw [hv]
  · change star (star v*v) = star v*v
    simp only [star_mul, star_star]

theorem partial_star {v : A} (hv : Partial v) : Partial (star v) := by
  have h := congrArg star hv
  simpa only [Partial, star_mul, star_star, ← mul_assoc] using h

theorem partial_final {v : A} (hv : Partial v) : IsStarProjection (v*star v) := by
  simpa only [star_star] using partial_initial (partial_star hv)

theorem partial_norm {v : A} (hv : Partial v) : ‖v‖ ≤ 1 := by
  have h := (partial_initial hv).norm_le
  rw [CStarRing.norm_star_mul_self] at h
  nlinarith [norm_nonneg v]

def Extends (v w : A) : Prop := w*(star v*v)=v ∧ star v*w=star v*v

theorem extends_refl {v : A} (hv : Partial v) : Extends v v := by
  exact ⟨by simpa only [Partial, ← mul_assoc] using hv, rfl⟩

theorem extends_initial {v w : A} (h : Extends v w) :
    (star w*w)*(star v*v)=star v*v := by
  have hs : star w*v=star v*v := by
    simpa only [star_mul, star_star] using congrArg star h.2
  rw [mul_assoc, h.1, hs]

theorem extends_initial' {v w : A} (h : Extends v w) :
    (star v*v)*(star w*w)=star v*v := by
  simpa only [star_mul, star_star] using congrArg star (extends_initial h)

theorem extends_trans {v w z : A} (h : Extends v w) (k : Extends w z) : Extends v z := by
  constructor
  · calc
      z*(star v*v) = z*((star w*w)*(star v*v)) := by rw [extends_initial h]
      _ = (z*(star w*w))*(star v*v) := by simp only [mul_assoc]
      _ = v := by rw [k.1, h.1]
  · have hs : star v = (star v*v)*star w := by
      simpa only [star_mul, star_star] using (congrArg star h.1).symm
    calc
      star v*z = ((star v*v)*star w)*z := by conv_lhs => rw [hs]
      _ = (star v*v)*(star w*z) := by simp only [mul_assoc]
      _ = star v*v := by rw [k.2, extends_initial' h]

theorem extends_antisymm {v w : A} (_ : Partial v) (hw : Partial w)
    (h : Extends v w) (k : Extends w v) : v=w := by
  have hp : star v*v=star w*w := (extends_initial' h).symm.trans (extends_initial k)
  calc
    v = w*(star v*v) := h.1.symm
    _ = w := by rw [hp]; simpa only [Partial, ← mul_assoc] using hw

structure PartialIso (A : Type*) [CStarAlgebra A] where
  value : A
  isPartial : Partial value

@[ext] theorem PartialIso.ext {v w : PartialIso A} (h : v.value=w.value) : v=w := by
  cases v; cases w; simp_all

instance : PartialOrder (PartialIso A) where
  le v w := Extends v.value w.value
  le_refl v := extends_refl v.isPartial
  le_trans _ _ _ := extends_trans
  le_antisymm v w h k := PartialIso.ext (extends_antisymm v.isPartial w.isPartial h k)

end

end KKProjectionSupport
end

end OAI
