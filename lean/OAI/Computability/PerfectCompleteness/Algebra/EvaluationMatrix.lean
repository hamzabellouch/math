import Mathlib.LinearAlgebra.Pi
import OAI.Computability.PerfectCompleteness.Foundations.FiniteRangeInverse

namespace OAI

section

namespace PerfectCompleteness.EvaluationMatrix

noncomputable section

variable {𝕜 Ω K : Type*} [Field 𝕜] [AddCommGroup K] [Module 𝕜 K]

def evaluation (H : Submodule 𝕜 (Ω → 𝕜)) (x : Ω) : Module.Dual 𝕜 H where
  toFun h := h.val x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem evaluation_apply (H : Submodule 𝕜 (Ω → 𝕜)) (x : Ω) (h : H) :
    evaluation H x h = h.val x := rfl

def evaluate (H : Submodule 𝕜 (Ω → 𝕜)) (X : Module.Dual 𝕜 H →ₗ[𝕜] K) (x : Ω) : K :=
  X (evaluation H x)

def shift (H : Submodule 𝕜 (Ω → 𝕜)) (X : Module.Dual 𝕜 H →ₗ[𝕜] K)
    (a : K) (h : H) : Module.Dual 𝕜 H →ₗ[𝕜] K :=
  X + (Module.Dual.eval 𝕜 H h).smulRight a

@[simp] theorem evaluate_shift (H : Submodule 𝕜 (Ω → 𝕜))
    (X : Module.Dual 𝕜 H →ₗ[𝕜] K) (a : K) (h : H) (x : Ω) :
    evaluate H (shift H X a h) x = evaluate H X x + h.val x • a := rfl

def joint {Z : Type*} (H : Submodule 𝕜 (Ω → 𝕜)) (other : Ω → Z)
    (X : Module.Dual 𝕜 H →ₗ[𝕜] K) (x : Ω) : K × Z :=
  (evaluate H X x, other x)

@[simp] theorem joint_shift {Z : Type*} (H : Submodule 𝕜 (Ω → 𝕜))
    (other : Ω → Z) (X : Module.Dual 𝕜 H →ₗ[𝕜] K) (a : K) (h : H) (x : Ω) :
    joint H other (shift H X a h) x = (evaluate H X x + h.val x • a, other x) := rfl

section Rows

variable (H : Submodule 𝕜 (Ω → 𝕜)) [FiniteDimensional 𝕜 H] {ℓ : Nat}

def rows (X : Module.Dual 𝕜 H →ₗ[𝕜] (Fin ℓ → 𝕜)) : Fin ℓ → H :=
  fun i => (Module.evalEquiv 𝕜 H).symm ((LinearMap.proj i).comp X)

def ofRows (v : Fin ℓ → H) : Module.Dual 𝕜 H →ₗ[𝕜] (Fin ℓ → 𝕜) :=
  LinearMap.pi (fun i => Module.Dual.eval 𝕜 H (v i))

omit [FiniteDimensional 𝕜 H] in
@[simp] theorem ofRows_apply (v : Fin ℓ → H) (q : Module.Dual 𝕜 H) (i : Fin ℓ) :
    ofRows H v q i = q (v i) := rfl

@[simp] theorem ofRows_rows (X : Module.Dual 𝕜 H →ₗ[𝕜] (Fin ℓ → 𝕜)) :
    ofRows H (rows H X) = X := by
  ext q i
  exact Module.apply_evalEquiv_symm_apply 𝕜 H q ((LinearMap.proj i).comp X)

@[simp] theorem rows_ofRows (v : Fin ℓ → H) : rows H (ofRows H v) = v := by
  funext i
  exact (Module.evalEquiv 𝕜 H).symm_apply_apply (v i)

def rowsEquiv : (Module.Dual 𝕜 H →ₗ[𝕜] (Fin ℓ → 𝕜)) ≃ (Fin ℓ → H) where
  toFun := rows H
  invFun := ofRows H
  left_inv := ofRows_rows H
  right_inv := rows_ofRows H

omit [FiniteDimensional 𝕜 H] in
@[simp] theorem evaluate_ofRows (v : Fin ℓ → H) (x : Ω) :
    evaluate H (ofRows H v) x = fun i => (v i).val x := rfl

theorem rows_apply (X : Module.Dual 𝕜 H →ₗ[𝕜] (Fin ℓ → 𝕜)) (i : Fin ℓ) (x : Ω) :
    (rows H X i).val x = evaluate H X x i :=
  Module.apply_evalEquiv_symm_apply 𝕜 H (evaluation H x) ((LinearMap.proj i).comp X)

theorem evaluate_injective :
    Function.Injective (evaluate H : (Module.Dual 𝕜 H →ₗ[𝕜] (Fin ℓ → 𝕜)) → (Ω → Fin ℓ → 𝕜)) := by
  intro X X' h
  apply (rowsEquiv H).injective
  funext i
  apply Subtype.ext
  funext x
  change (rows H X i).val x = (rows H X' i).val x
  rw [rows_apply, rows_apply]
  exact congrFun (congrFun h x) i

end Rows
end
end PerfectCompleteness.EvaluationMatrix

end

end OAI
