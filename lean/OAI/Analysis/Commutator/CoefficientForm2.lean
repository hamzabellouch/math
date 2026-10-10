import Mathlib
import OAI.Analysis.Commutator.HilbertTensors
import OAI.Analysis.Commutator.CoefficientForm

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison

open PreHilbert Function

variable (E F : PreHilbert) (k l : ℕ)

variable {M : Type*} [AddCommGroup M] [Module ℂ M] [StarAddMonoid M] [StarModule ℂ M]

def coefficient (Y : wordSpace E F k →L[ℂ] wordSpace E F l) (Ω : E)
    (v₀ : M →ₗ[ℂ] E) (v₁ : M →ₗ[ℂ] F) (A : Option (Fin k ⊕ Fin l) → M) : ℂ :=
  inner ℂ (word E F l (v₀ (star (A none))) (fun j => v₁ (star (A (some (.inr j))))))
    (Y (word E F k Ω (fun i => v₁ (A (some (.inl i))))))

variable [DecidableEq (Option (Fin k ⊕ Fin l))]

omit [StarModule ℂ M] in
lemma coefficient_update_none_add
    (Y : wordSpace E F k →L[ℂ] wordSpace E F l) (Ω : E)
    (v₀ : M →ₗ[ℂ] E) (v₁ : M →ₗ[ℂ] F) (A : Option (Fin k ⊕ Fin l) → M) (x y : M) :
    coefficient E F k l Y Ω v₀ v₁ (update A none (x+y)) =
      coefficient E F k l Y Ω v₀ v₁ (update A none x) +
      coefficient E F k l Y Ω v₀ v₁ (update A none y) := by
  simp only [coefficient, update_self, update_of_ne (Option.some_ne_none _),
    star_add, map_add, word_add_left, inner_add_left]

lemma coefficient_update_none_smul
    (Y : wordSpace E F k →L[ℂ] wordSpace E F l) (Ω : E)
    (v₀ : M →ₗ[ℂ] E) (v₁ : M →ₗ[ℂ] F) (A : Option (Fin k ⊕ Fin l) → M) (c : ℂ) (x : M) :
    coefficient E F k l Y Ω v₀ v₁ (update A none (c • x)) =
      c • coefficient E F k l Y Ω v₀ v₁ (update A none x) := by
  simp only [coefficient, update_self, update_of_ne (Option.some_ne_none _),
    star_smul, map_smul, word_smul_left, inner_smul_left]
  simp

omit [StarModule ℂ M] in
lemma coefficient_update_inl
    (Y : wordSpace E F k →L[ℂ] wordSpace E F l) (Ω : E)
    (v₀ : M →ₗ[ℂ] E) (v₁ : M →ₗ[ℂ] F) (A : Option (Fin k ⊕ Fin l) → M)
    (i : Fin k) (x : M) :
    coefficient E F k l Y Ω v₀ v₁ (update A (some (.inl i)) x) =
      inner ℂ (word E F l (v₀ (star (A none))) (fun j => v₁ (star (A (some (.inr j))))))
        (Y (word E F k Ω (update (fun a => v₁ (A (some (.inl a)))) i (v₁ x)))) := by
  have he : (fun a => v₁ (update A (some (.inl i)) x (some (.inl a)))) =
      update (fun a => v₁ (A (some (.inl a)))) i (v₁ x) := by
    funext a
    by_cases ha : a = i <;> simp [ha]
  have hn : (none : Option (Fin k ⊕ Fin l)) ≠ some (.inl i) := by simp
  have hr : ∀ j : Fin l, (some (.inr j) : Option (Fin k ⊕ Fin l)) ≠ some (.inl i) := by simp
  simp only [coefficient, update_of_ne hn, update_of_ne (hr _), he]

omit [StarModule ℂ M] in
lemma coefficient_update_inr
    (Y : wordSpace E F k →L[ℂ] wordSpace E F l) (Ω : E)
    (v₀ : M →ₗ[ℂ] E) (v₁ : M →ₗ[ℂ] F) (A : Option (Fin k ⊕ Fin l) → M)
    (j : Fin l) (x : M) :
    coefficient E F k l Y Ω v₀ v₁ (update A (some (.inr j)) x) =
      inner ℂ (word E F l (v₀ (star (A none)))
        (update (fun b => v₁ (star (A (some (.inr b))))) j (v₁ (star x))))
        (Y (word E F k Ω (fun a => v₁ (A (some (.inl a)))))) := by
  have he : (fun b => v₁ (star (update A (some (.inr j)) x (some (.inr b))))) =
      update (fun b => v₁ (star (A (some (.inr b))))) j (v₁ (star x)) := by
    funext b
    by_cases hb : b = j <;> simp [hb]
  have hn : (none : Option (Fin k ⊕ Fin l)) ≠ some (.inr j) := by simp
  have hr : ∀ i : Fin k, (some (.inl i) : Option (Fin k ⊕ Fin l)) ≠ some (.inr j) := by simp
  simp only [coefficient, update_of_ne hn, update_of_ne (hr _), he]

def coefficientMultilinear
    (Y : wordSpace E F k →L[ℂ] wordSpace E F l) (Ω : E)
    (v₀ : M →ₗ[ℂ] E) (v₁ : M →ₗ[ℂ] F) :
    MultilinearMap ℂ (fun _ : Option (Fin k ⊕ Fin l) => M) ℂ where
  toFun := coefficient E F k l Y Ω v₀ v₁
  map_update_add' := by
    intro inst A i x y
    cases i with
    | none => exact coefficient_update_none_add E F k l Y Ω v₀ v₁ A x y
    | some i =>
      cases i with
      | inl i =>
        simp only [coefficient_update_inl, map_add, word_update_add, inner_add_right]
      | inr j =>
        simp only [coefficient_update_inr, star_add, map_add, word_update_add, inner_add_left]
  map_update_smul' := by
    intro inst A i c x
    cases i with
    | none => exact coefficient_update_none_smul E F k l Y Ω v₀ v₁ A c x
    | some i =>
      cases i with
      | inl i =>
        simp only [coefficient_update_inl, map_smul, word_update_smul, inner_smul_right,
          smul_eq_mul]
      | inr j =>
        simp only [coefficient_update_inr, star_smul, map_smul, word_update_smul,
          inner_smul_left, starRingEnd_apply, star_star, smul_eq_mul]

end Kadison
end

end OAI
