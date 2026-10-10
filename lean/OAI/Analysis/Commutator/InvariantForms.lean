import Mathlib
import OAI.Analysis.Commutator.SchurWeylDevelopment

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.SchurWeyl

open Matrix

variable {𝕜 : Type*} [CommRing 𝕜]

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def tensorMatrices (A : J → Matrix I I 𝕜) : Matrix (J → I) (J → I) 𝕜 :=
  fun a b => ∏ j, A j (a j) (b j)

omit [DecidableEq I] in
lemma tensorMatrices_mul (A B : J → Matrix I I 𝕜) :
    tensorMatrices (fun j => A j * B j) = tensorMatrices A * tensorMatrices B := by
  classical
  ext a b
  simp only [tensorMatrices, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp only [← Finset.prod_mul_distrib]

omit [Fintype I] [DecidableEq J] in
lemma tensorMatrices_single (a b : J → I) :
    tensorMatrices (fun j => Matrix.single (a j) (b j) (1 : 𝕜)) = Matrix.single a b 1 := by
  classical
  ext c d
  simp only [tensorMatrices, Matrix.single_apply]
  by_cases h : c = a ∧ d = b
  · rcases h with ⟨rfl, rfl⟩; simp
  · rw [ite_eq_right (by simpa [eq_comm] using h)]
    have he : ∃ j, ¬ (a j = c j ∧ b j = d j) := by
      by_contra! hn
      exact h ⟨funext fun j => (hn j).1.symm, funext fun j => (hn j).2.symm⟩
    obtain ⟨j, hj⟩ := he
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

def traceForm (T : Matrix (J → I) (J → I) 𝕜) :
    MultilinearMap 𝕜 (fun _ : J => Matrix I I 𝕜) 𝕜 :=
  ∑ a, ∑ b, T a b • ((MultilinearMap.mkPiRing 𝕜 J 1).compLinearMap
    fun j => Matrix.entryLinearMap 𝕜 𝕜 (b j) (a j))

omit [DecidableEq I] in
lemma traceForm_apply (T : Matrix (J → I) (J → I) 𝕜) (A : J → Matrix I I 𝕜) :
    traceForm T A = Matrix.trace (T * tensorMatrices A) := by
  simp [traceForm, Matrix.trace, Matrix.mul_apply, tensorMatrices,
    _root_.smul_apply, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiRing_apply, smul_eq_mul]

lemma traceForm_single (T : Matrix (J → I) (J → I) 𝕜) (a b : J → I) :
    traceForm T (fun j => Matrix.single (a j) (b j) 1) = T b a := by
  rw [traceForm_apply, tensorMatrices_single, Matrix.trace_mul_single]
  simp

def coefficientMatrix (F : MultilinearMap 𝕜 (fun _ : J => Matrix I I 𝕜) 𝕜) :
    Matrix (J → I) (J → I) 𝕜 :=
  fun a b => F (fun j => Matrix.single (b j) (a j) 1)

lemma traceForm_coefficientMatrix (F : MultilinearMap 𝕜 (fun _ : J => Matrix I I 𝕜) 𝕜) :
    traceForm (coefficientMatrix F) = F := by
  apply Module.Basis.ext_multilinear (fun _ => Matrix.stdBasis 𝕜 I I)
  intro v
  have hb (p : I × I) : Matrix.stdBasis 𝕜 I I p = Matrix.single p.1 p.2 1 := by
    rcases p with ⟨i, j⟩
    exact Matrix.stdBasis_eq_single 𝕜 i j
  simp only [hb, traceForm_single, coefficientMatrix]

lemma coefficientMatrix_traceForm (T : Matrix (J → I) (J → I) 𝕜) :
    coefficientMatrix (traceForm T) = T := by
  ext a b
  exact traceForm_single T b a

lemma traceForm_injective : Function.Injective (traceForm (I := I) (J := J) (𝕜 := 𝕜)) := by
  intro T S h
  simpa only [coefficientMatrix_traceForm] using congrArg coefficientMatrix h

omit [DecidableEq I] in
lemma traceForm_conjugate (T : Matrix (J → I) (J → I) 𝕜)
    (U V : Matrix I I 𝕜) (A : J → Matrix I I 𝕜) :
    traceForm T (fun j => U * A j * V) =
      traceForm (tensorPower V * T * tensorPower U) A := by
  simp only [traceForm_apply, tensorMatrices_mul]
  change Matrix.trace (T * (tensorPower U * tensorMatrices A * tensorPower V)) = _
  simp only [← Matrix.mul_assoc]
  rw [Matrix.trace_mul_cycle]
  simp only [Matrix.mul_assoc]

lemma coefficientMatrix_commute_unitary
    (F : MultilinearMap ℂ (fun _ : J => Matrix I I ℂ) ℂ)
    (hF : ∀ (U : unitary (Matrix I I ℂ)) (A : J → Matrix I I ℂ),
      F (fun j => (U : Matrix I I ℂ) * A j * star (U : Matrix I I ℂ)) = F A)
    (U : unitary (Matrix I I ℂ)) :
    coefficientMatrix F * tensorPower (U : Matrix I I ℂ) =
      tensorPower (U : Matrix I I ℂ) * coefficientMatrix F := by
  have hconj : tensorPower (star (U : Matrix I I ℂ)) * coefficientMatrix F *
      tensorPower (U : Matrix I I ℂ) = coefficientMatrix F := by
    apply traceForm_injective
    apply MultilinearMap.ext
    intro A
    rw [← traceForm_conjugate, traceForm_coefficientMatrix, hF]
  have hu : tensorPower (U : Matrix I I ℂ) * tensorPower (star (U : Matrix I I ℂ)) =
      (1 : Matrix (J → I) (J → I) ℂ) := by
    rw [← tensorPower_mul, ← Unitary.coe_star, Unitary.coe_mul_star_self, tensorPower_one]
  have hh := congrArg (fun T => tensorPower (U : Matrix I I ℂ) * T) hconj
  simpa only [← Matrix.mul_assoc, hu, Matrix.one_mul] using hh

theorem invariant_multilinear_form (b : J → I) (hb : Function.Injective b)
    (F : MultilinearMap ℂ (fun _ : J => Matrix I I ℂ) ℂ)
    (hF : ∀ (U : unitary (Matrix I I ℂ)) (A : J → Matrix I I ℂ),
      F (fun j => (U : Matrix I I ℂ) * A j * star (U : Matrix I I ℂ)) = F A) :
    ∃ c : Equiv.Perm J → ℂ, ∀ A : J → Matrix I I ℂ,
      F A = ∑ σ, c σ * Matrix.trace (permutationMatrix σ * tensorMatrices A) := by
  let T := coefficientMatrix F
  have he : T = ∑ σ : Equiv.Perm J, T (b ∘ σ.symm) b • permutationMatrix σ :=
    commutant_unitary_tensorPower b hb T (coefficientMatrix_commute_unitary F hF)
  refine ⟨fun σ => T (b ∘ σ.symm) b, fun A => ?_⟩
  have ht : F A = Matrix.trace (T * tensorMatrices A) := by
    rw [← traceForm_apply, traceForm_coefficientMatrix]
  calc
    F A = Matrix.trace (T * tensorMatrices A) := ht
    _ = Matrix.trace ((∑ σ : Equiv.Perm J, T (b ∘ σ.symm) b • permutationMatrix σ) *
        tensorMatrices A) := congrArg (fun V => Matrix.trace (V * tensorMatrices A)) he
    _ = _ := by simp [Matrix.sum_mul, Matrix.trace_smul, smul_eq_mul]

end Kadison.SchurWeyl
end

end OAI
