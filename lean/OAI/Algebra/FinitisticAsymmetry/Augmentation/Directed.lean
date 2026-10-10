import Mathlib
import OAI.Algebra.Finitistic.Encoding.DirectedBound
import OAI.Algebra.FinitisticAsymmetry.Model

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace LittleFinitistic.DirectedBound
universe u

namespace DirectedSystem
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] {n : ℕ}
variable (D : DirectedSystem k A n)
abbrev Vertices := {i : Fin n // D.e i ≠ 0}
def coefficient (a : A) (i : D.Vertices) : k := (D.diagonal i a).choose
lemma coefficient_spec (a : A) (i : D.Vertices) :
    D.e i * a * D.e i = D.coefficient a i • D.e i := (D.diagonal i a).choose_spec
lemma coefficient_eq_iff (a : A) (i : D.Vertices) (c : k) :
    D.coefficient a i = c ↔ D.e i * a * D.e i = c • D.e i := by
  rw [D.coefficient_spec]
  exact (smul_left_injective k i.property).eq_iff.symm

lemma corner_mul (a b : A) (i j : Fin n) :
    D.e i * (a * b) * D.e j = ∑ l, (D.e i * a * D.e l) * (D.e l * b * D.e j) := by
  conv_rhs => arg 2; ext l; rw [mul_assoc, ← mul_assoc (D.e l), ← mul_assoc (D.e l), D.idem]
  simp only [← mul_assoc]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, D.complete]
  simp [mul_assoc]

lemma diagonal_mul (a b : A) (i : Fin n) :
    D.e i * (a * b) * D.e i = (D.e i * a * D.e i) * (D.e i * b * D.e i) := by
  rw [D.corner_mul, Finset.sum_eq_single i]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hji | hij
    · rw [D.directed i j hji b, mul_zero]
    · rw [D.directed j i hij a, zero_mul]
  · simp

def augmentation : A →ₐ[k] (D.Vertices → k) where
  toFun := D.coefficient
  map_zero' := by ext i; apply (D.coefficient_eq_iff _ _ _).mpr; simp
  map_one' := by ext i; apply (D.coefficient_eq_iff _ _ _).mpr; simp [D.idem]
  map_add' a b := by
    ext i
    apply (D.coefficient_eq_iff _ _ _).mpr
    simp [mul_add, add_mul, D.coefficient_spec, add_smul]
  map_mul' a b := by
    ext i
    apply (D.coefficient_eq_iff _ _ _).mpr
    rw [D.diagonal_mul, D.coefficient_spec, D.coefficient_spec, smul_mul_smul_comm, D.idem]
    rfl
  commutes' c := by
    ext i
    apply (D.coefficient_eq_iff _ _ _).mpr
    rw [← (Algebra.commutes c (D.e i)), ← Algebra.smul_def, smul_mul_assoc, D.idem]
    rfl

lemma coefficient_vertex (i j : D.Vertices) :
    D.coefficient (D.e i) j = if j = i then 1 else 0 := by
  classical
  apply (D.coefficient_eq_iff _ _ _).mpr
  split_ifs with h
  · subst j; simp [D.idem]
  · rw [D.orthogonal j i (fun hji => h (Subtype.ext hji))]
    simp

lemma augmentation_surjective : Function.Surjective D.augmentation := by
  classical
  intro s
  refine ⟨∑ i : D.Vertices, s i • D.e i, ?_⟩
  ext j
  simp [map_sum, map_smul, augmentation, coefficient_vertex]

lemma mem_augmentation_ker_iff (a : A) :
    a ∈ RingHom.ker D.augmentation.toRingHom ↔ ∀ i : Fin n, D.e i * a * D.e i = 0 := by
  constructor
  · intro ha i
    by_cases hi : D.e i = 0
    · simp [hi]
    · rw [D.coefficient_spec a ⟨i, hi⟩]
      have := congrFun ha ⟨i, hi⟩
      change D.coefficient a ⟨i, hi⟩ = 0 at this
      rw [this, zero_smul]
  · intro ha
    change D.augmentation a = 0
    ext i
    apply (D.coefficient_eq_iff _ _ _).mpr
    simpa using ha i

lemma ker_corner_vanish {a : A} (ha : a ∈ RingHom.ker D.augmentation.toRingHom)
    (i j : Fin n) (hij : i.val < j.val + 1) : D.e i * a * D.e j = 0 := by
  by_cases h : i = j
  · subst j; exact (D.mem_augmentation_ker_iff a).mp ha i
  · exact D.directed j i (by have hne : i.val ≠ j.val := fun hval => h (Fin.ext hval); omega) a

lemma pow_ker_corner_vanish (m : ℕ) {a : A}
    (ha : a ∈ (RingHom.ker D.augmentation.toRingHom) ^ m)
    (i j : Fin n) (hij : i.val < j.val + m) : D.e i * a * D.e j = 0 := by
  induction m generalizing a i j with
  | zero => exact D.directed j i (by simpa using hij) a
  | succ m ih =>
    rw [Submodule.pow_succ] at ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro x hx y hy
      rw [D.corner_mul]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hil : i.val < l.val + m
      · rw [ih hx i l hil, zero_mul]
      · rw [D.ker_corner_vanish hy l j (by omega), mul_zero]
    · intro x y hx hy
      simp [mul_add, add_mul, hx, hy]

lemma augmentation_ker_nilpotent :
    ∃ m : ℕ, (RingHom.ker D.augmentation.toRingHom) ^ m = ⊥ := by
  refine ⟨n, le_bot_iff.mp ?_⟩
  intro a ha
  change a = 0
  have he : (∑ i, D.e i) * a * (∑ j, D.e j) = 0 := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro i _
    exact D.pow_ker_corner_vanish n ha i j (by omega)
  simpa [D.complete] using he
end DirectedSystem
end LittleFinitistic.DirectedBound

end
end

end OAI
