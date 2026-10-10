import Mathlib
import OAI.Computability.MinUncut.PCP.Parity

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

def jointCoefficient (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    (α : Module.Dual F₂ (FaceArray A m n)) (I : Point m n → ℕ) : ℝ :=
  BinaryFourier.coefficient
    (fun B => GaussianHermite.coeff (fun c => gradient f B σ η c x) I) α

def constantArray (k : Row m n → F₂) : FaceArray A m n := fun r => AffineMap.const F₂ A (k r)

omit [Fintype A] in
lemma constantArray_add (B : FaceArray A m n) (k : Row m n → F₂) :
    constantArray k+B = addConstantArray B k := by
  funext r; exact add_comm _ _

lemma hermite_gradient_constantArray (f : FoldedProof A) (B : FaceArray A m n)
    (k : Row m n → F₂) {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ) (x : Point m n) (I : Point m n → ℕ) :
    GaussianHermite.coeff (fun c => gradient f (constantArray k+B) σ η c x) I =
      BinaryFourier.sign ((rowCode k).val x + GaussianHermite.parity (rowCode k).val I) *
        GaussianHermite.coeff (fun c => gradient f B σ η c x) I := by
  simp only [constantArray_add, gradient_addConstantArray f B k hσ,
    GaussianHermite.coeff_const_mul, BinaryFourier.sign_add, mul_assoc]
  rw [GaussianHermite.coeff_diagonal (rowCode k).val (fun c => gradient f B σ η c x) I]

lemma sign_injective : Function.Injective BinaryFourier.sign := by
  intro a b hab
  have h : ∀ x : F₂, x=0 ∨ x=1 := by decide
  rcases h a with rfl | rfl
  · rcases h b with rfl | rfl
    · rfl
    · norm_num at hab
  · rcases h b with rfl | rfl
    · norm_num at hab
    · rfl

theorem joint_row_gauge (f : FoldedProof A) {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ)
    (x : Point m n) (α : Module.Dual F₂ (FaceArray A m n)) (I : Point m n → ℕ)
    (hne : jointCoefficient f σ η x α I ≠ 0) (k : Row m n → F₂) :
    α (constantArray k) = (rowCode k).val x + GaussianHermite.parity (rowCode k).val I := by
  have ht := BinaryFourier.coefficient_translate
    (fun B : FaceArray A m n => GaussianHermite.coeff (fun c => gradient f B σ η c x) I)
    α (constantArray k)
  simp only [hermite_gradient_constantArray f _ k hσ, BinaryFourier.coefficient,
    mul_assoc, ← Finset.mul_expect] at ht
  apply sign_injective
  change _ * jointCoefficient f σ η x α I = _ * jointCoefficient f σ η x α I at ht
  exact mul_right_cancel₀ hne ht.symm

theorem joint_cylinder_gauge (f : FoldedProof A) (σ η : ℝ)
    (x : Point m n) (α : Module.Dual F₂ (FaceArray A m n)) (I : Point m n → ℕ)
    (hne : jointCoefficient f σ η x α I ≠ 0)
    (i j : Fin m) (hij : i ≠ j) (q : Point m n) (a : Forms A) :
    α (cylinderArray i j q a) = 0 := by
  have ht := BinaryFourier.coefficient_translate
    (fun B : FaceArray A m n => GaussianHermite.coeff (fun c => gradient f B σ η c x) I)
    α (cylinderArray i j q a)
  have hg (B : FaceArray A m n) : gradient f (cylinderArray i j q a+B) σ η =
      gradient f B σ η := by rw [add_comm, gradient_cylinder f B i j hij]
  simp only [hg] at ht
  by_contra hn
  have hs : BinaryFourier.character α (cylinderArray i j q a) = -1 := by
    simp [BinaryFourier.character, BinaryFourier.sign, hn]
  rw [hs] at ht
  exact hne (by change jointCoefficient f σ η x α I = -1*jointCoefficient f σ η x α I at ht; linarith)
end MinUncut.Inner

end

end OAI
