import OAI.Combinatorics.Ryser.Geometry.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F]

structure PlaneLinearMap (F : Type*) [Field F] where
  xx : F
  xy : F
  yx : F
  yy : F
  determinant_ne_zero : xx * yy - xy * yx ≠ 0

namespace PlaneLinearMap

def determinant (M : PlaneLinearMap F) : F := M.xx * M.yy - M.xy * M.yx

def apply (M : PlaneLinearMap F) (p : Point F) : Point F :=
  (M.xx * p.1 + M.xy * p.2, M.yx * p.1 + M.yy * p.2)

def inverse (M : PlaneLinearMap F) (p : Point F) : Point F :=
  ((M.yy * p.1 - M.xy * p.2) / M.determinant,
    (M.xx * p.2 - M.yx * p.1) / M.determinant)

@[simp] theorem inverse_apply (M : PlaneLinearMap F) (p : Point F) :
    M.inverse (M.apply p) = p := by
  have hd : M.determinant ≠ 0 := M.determinant_ne_zero
  apply Prod.ext <;> dsimp [inverse, apply]
  · field_simp [hd]
    simp only [determinant]
    ring
  · field_simp [hd]
    simp only [determinant]
    ring

@[simp] theorem apply_inverse (M : PlaneLinearMap F) (p : Point F) :
    M.apply (M.inverse p) = p := by
  have hd : M.determinant ≠ 0 := M.determinant_ne_zero
  apply Prod.ext <;> dsimp [inverse, apply]
  · field_simp [hd]
    simp only [determinant]
    ring
  · field_simp [hd]
    simp only [determinant]
    ring

def toEquiv (M : PlaneLinearMap F) : Point F ≃ Point F where
  toFun := M.apply
  invFun := M.inverse
  left_inv := M.inverse_apply
  right_inv := M.apply_inverse

theorem apply_injective (M : PlaneLinearMap F) : Function.Injective M.apply :=
  M.toEquiv.injective

theorem apply_surjective (M : PlaneLinearMap F) : Function.Surjective M.apply :=
  M.toEquiv.surjective

@[simp] theorem apply_zero (M : PlaneLinearMap F) : M.apply (0, 0) = (0, 0) := by
  simp [apply]

theorem apply_sub (M : PlaneLinearMap F) (p q : Point F) :
    M.apply (p - q) = M.apply p - M.apply q := by
  apply Prod.ext <;> simp only [apply, Prod.fst_sub, Prod.snd_sub] <;> ring

theorem apply_smul (M : PlaneLinearMap F) (a : F) (p : Point F) :
    M.apply (a * p.1, a * p.2) =
      (a * (M.apply p).1, a * (M.apply p).2) := by
  apply Prod.ext <;> dsimp [apply] <;> ring

def diagonal (a : F) (ha : a ≠ 0) : PlaneLinearMap F where
  xx := 1
  xy := 0
  yx := 0
  yy := a
  determinant_ne_zero := by simpa using ha

@[simp] theorem diagonal_apply (a : F) (ha : a ≠ 0) (p : Point F) :
    (diagonal a ha).apply p = (p.1, a * p.2) := by
  simp [diagonal, apply]

def extra (u v : F) (huv : u ≠ v) : PlaneLinearMap F where
  xx := 1
  xy := 1
  yx := u
  yy := v
  determinant_ne_zero := by
    simpa only [one_mul] using sub_ne_zero.mpr huv.symm

@[simp] theorem extra_apply (u v : F) (huv : u ≠ v) (p : Point F) :
    (extra u v huv).apply p = (p.1 + p.2, u * p.1 + v * p.2) := by
  simp [extra, apply]

end PlaneLinearMap

section Subfield

variable {k : Type*} [Field k]

def mapPoint (σ : k →+* F) (p : Point k) : Point F := (σ p.1, σ p.2)

theorem mapPoint_injective (σ : k →+* F) : Function.Injective (mapPoint σ) := by
  intro p q hpq
  apply Prod.ext
  · exact σ.injective (congrArg Prod.fst hpq)
  · exact σ.injective (congrArg Prod.snd hpq)

def placedPoint (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (w : Point k) : Point F := b + M.apply (mapPoint σ w)

theorem placedPoint_injective (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) : Function.Injective (placedPoint σ M b) := by
  intro p q hpq
  apply mapPoint_injective σ
  apply M.apply_injective
  exact add_left_cancel hpq

theorem placedPoint_sub (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (p q : Point k) :
    placedPoint σ M b p - placedPoint σ M b q =
      M.apply (mapPoint σ p - mapPoint σ q) := by
  rw [M.apply_sub]
  simp only [placedPoint, add_sub_add_left_eq_sub]

end Subfield

end RyserCoveringCounterexample.Construction

end OAI
