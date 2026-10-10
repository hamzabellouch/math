import Mathlib

namespace OAI

namespace Problem336.ReducedLaplacian

open scoped BigOperators Matrix

variable {V E : Type*}

def EdgeAdj (src dst : E → V) (u v : V) : Prop :=
  ∃ e, (src e = u ∧ dst e = v) ∨ (src e = v ∧ dst e = u)

def Connected (src dst : E → V) : Prop :=
  ∀ u v, Relation.ReflTransGen (EdgeAdj src dst) u v

theorem potential_eq_of_connected (src dst : E → V) (hconn : Connected src dst)
    (x : V → ℝ) (hedge : ∀ e, x (src e) = x (dst e)) (u v : V) : x u = x v := by
  have hp := hconn u v
  induction hp with
  | refl => rfl
  | @tail b c hab hbc ih =>
      apply ih.trans
      obtain ⟨e, h | h⟩ := hbc
      · simpa [h.1, h.2] using hedge e
      · simpa [h.1, h.2] using (hedge e).symm

variable [DecidableEq V]

def extendZero (root : V) (x : {v : V // v ≠ root} → ℝ) (v : V) : ℝ :=
  if hv : v ≠ root then x ⟨v, hv⟩ else 0

@[simp] theorem extendZero_root (root : V) (x : {v : V // v ≠ root} → ℝ) :
    extendZero root x root = 0 := by simp [extendZero]

@[simp] theorem extendZero_subtype (root : V) (x : {v : V // v ≠ root} → ℝ)
    (v : {v : V // v ≠ root}) : extendZero root x v = x v := by
  simp [extendZero, v.property]

def reducedGradient (src dst : E → V) (root : V) :
    Matrix E {v : V // v ≠ root} ℝ :=
  fun e v => (if v.val = src e then 1 else 0) - (if v.val = dst e then 1 else 0)

variable [Fintype V]

lemma sum_indicator_mul (root : V) (x : {v : V // v ≠ root} → ℝ) (v : V) :
    (∑ i : {v : V // v ≠ root}, (if i.val = v then (1 : ℝ) else 0) * x i) =
      extendZero root x v := by
  classical
  by_cases hv : v ≠ root
  · rw [extendZero, dite_eq_left hv]
    rw [Finset.sum_eq_single ⟨v, hv⟩]
    · simp
    · intro b _ hb
      have hb' : b.val ≠ v := fun h => hb (Subtype.ext h)
      simp [hb']
    · simp
  · have hv' : v = root := not_ne_iff.mp hv
    subst v
    rw [extendZero_root]
    apply Finset.sum_eq_zero
    intro i _
    simp [i.property]

theorem reducedGradient_mulVec (src dst : E → V) (root : V)
    (x : {v : V // v ≠ root} → ℝ) (e : E) :
    (reducedGradient src dst root *ᵥ x) e =
      extendZero root x (src e) - extendZero root x (dst e) := by
  simp only [Matrix.mulVec, dotProduct, reducedGradient, sub_mul, Finset.sum_sub_distrib]
  rw [sum_indicator_mul, sum_indicator_mul]

theorem reducedGradient_mulVec_injective (src dst : E → V) (root : V)
    (hconn : Connected src dst) :
    Function.Injective (reducedGradient src dst root).mulVec := by
  intro x y hxy
  have hedge : ∀ e,
      (extendZero root x - extendZero root y) (src e) =
      (extendZero root x - extendZero root y) (dst e) := by
    intro e
    have h := congrFun hxy e
    rw [reducedGradient_mulVec, reducedGradient_mulVec] at h
    simp only [Pi.sub_apply]
    linarith
  funext v
  have h := potential_eq_of_connected src dst hconn
    (extendZero root x - extendZero root y) hedge v.val root
  exact sub_eq_zero.mp (by simpa using h)

variable [Fintype E] [DecidableEq E]

def weightedLaplacian (src dst : E → V) (root : V) (w : E → ℝ) :
    Matrix {v : V // v ≠ root} {v : V // v ≠ root} ℝ :=
  (reducedGradient src dst root)ᵀ * Matrix.diagonal w * reducedGradient src dst root

theorem weightedLaplacian_posDef (src dst : E → V) (root : V) (w : E → ℝ)
    (hconn : Connected src dst) (hw : ∀ e, 0 < w e) :
    (weightedLaplacian src dst root w).PosDef := by
  have hd : (Matrix.diagonal w).PosDef := Matrix.PosDef.diagonal hw
  have h := hd.conjTranspose_mul_mul_same
    (reducedGradient_mulVec_injective src dst root hconn)
  simpa [weightedLaplacian, Matrix.conjTranspose_eq_transpose_of_trivial] using h

theorem weightedLaplacian_isUnit (src dst : E → V) (root : V) (w : E → ℝ)
    (hconn : Connected src dst) (hw : ∀ e, 0 < w e) :
    IsUnit (weightedLaplacian src dst root w) :=
  (weightedLaplacian_posDef src dst root w hconn hw).isUnit

theorem weightedLaplacian_det_ne_zero (src dst : E → V) (root : V) (w : E → ℝ)
    (hconn : Connected src dst) (hw : ∀ e, 0 < w e) :
    (weightedLaplacian src dst root w).det ≠ 0 := by
  exact isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (weightedLaplacian_isUnit src dst root w hconn hw))

end Problem336.ReducedLaplacian

end OAI
