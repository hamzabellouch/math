import Mathlib

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.RectangularTensors

open Matrix

variable {𝕜 : Type*} [CommRing 𝕜]

variable {I K L J : Type*} [Fintype I] [Fintype K] [Fintype L] [Fintype J] [DecidableEq J]

def tensor (A : J → Matrix I K 𝕜) : Matrix (J → I) (J → K) 𝕜 :=
  fun a b => ∏ j, A j (a j) (b j)

omit [Fintype I] [Fintype L] in
lemma tensor_mul (A : J → Matrix I K 𝕜) (B : J → Matrix K L 𝕜) :
    tensor (fun j => A j * B j) = tensor A * tensor B := by
  classical
  ext a b
  simp only [tensor, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp only [← Finset.prod_mul_distrib]

omit [Fintype I] [DecidableEq J] in
lemma tensor_one [DecidableEq I] : tensor (fun _ : J => (1 : Matrix I I 𝕜)) = 1 := by
  classical
  ext a b
  simp only [tensor, Matrix.one_apply]
  by_cases h : a = b
  · subst b; simp
  · rw [ite_eq_right h]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

def perm [DecidableEq I] (σ : Equiv.Perm J) : Matrix (J → I) (J → I) 𝕜 :=
  fun a b => if a = b ∘ σ.symm then 1 else 0

lemma tensor_constant_natural [DecidableEq I] [DecidableEq K]
    (X : Matrix I K 𝕜) (σ : Equiv.Perm J) :
    tensor (fun _ : J => X) * perm (𝕜 := 𝕜) (I := K) σ = perm (𝕜 := 𝕜) (I := I) σ * tensor (fun _ : J => X) := by
  classical
  ext a b
  simp only [Matrix.mul_apply, perm, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (b ∘ σ.symm)]
  · rw [ite_eq_left rfl]
    rw [Finset.sum_eq_single (a ∘ σ)]
    · have ha : a = (a ∘ σ) ∘ σ.symm := by ext j; simp
      rw [ite_eq_left ha, one_mul]
      simp only [tensor, Function.comp_apply]
      simpa using (Equiv.prod_comp σ.symm (fun j => X (a (σ j)) (b j)))
    · intro c _ hc
      rw [ite_eq_right (by intro h; apply hc; ext j; simpa using (congrFun h (σ j)).symm),
        zero_mul]
    · simp
  · intro c _ hc
    exact ite_eq_right hc
  · simp

lemma trace_transport [DecidableEq I] [DecidableEq K]
    (X : Matrix I K 𝕜) (Y : Matrix K I 𝕜) (hYX : Y * X = 1)
    (A : J → Matrix K K 𝕜) (σ : Equiv.Perm J) :
    Matrix.trace (perm (𝕜 := 𝕜) (I := I) σ * tensor (fun j => X * A j * Y)) =
      Matrix.trace (perm (𝕜 := 𝕜) (I := K) σ * tensor A) := by
  rw [tensor_mul, tensor_mul]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  rw [← Matrix.mul_assoc (tensor (fun _ : J => Y))
    (perm (𝕜 := 𝕜) (I := I) σ * tensor (fun _ : J => X)) (tensor A)]
  rw [← Matrix.mul_assoc (tensor (fun _ : J => Y)) (perm (𝕜 := 𝕜) (I := I) σ)
    (tensor (fun _ : J => X)), tensor_constant_natural Y σ]
  rw [Matrix.mul_assoc (perm (𝕜 := 𝕜) (I := K) σ), ← tensor_mul]
  simp only [hYX, tensor_one, Matrix.mul_one]

end Kadison.RectangularTensors
end

end OAI
