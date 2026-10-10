import OAI.GroupTheory.PolycyclicRecognition.Algebra.TensorMultilinearGenerators
import OAI.GroupTheory.PolycyclicRecognition.Algebra.MultilinearCoordinatePair

namespace OAI

/-! # Alternation survives scalar extension, including in characteristic two -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
variable (K : Type) [Field K]
variable {M V : Type} [AddCommGroup M] [Module ℤ M] [AddCommGroup V] [Module K V]

theorem scalarMultilinearExtension_swap {n : ℕ} (F : M [⋀^Fin n]→ₗ[ℤ] V)
    (v : Fin n → K ⊗[ℤ] M) {i j : Fin n} (hij : i ≠ j) :
    scalarMultilinearExtensionOperator K M V n F.toMultilinearMap (v ∘ Equiv.swap i j) =
      -scalarMultilinearExtensionOperator K M V n F.toMultilinearMap v := by
  classical
  let E := scalarMultilinearExtensionOperator K M V n F.toMultilinearMap
  have he : E.domDomCongr (Equiv.swap i j) = -E := by
    apply tensorMultilinear_ext
    intro a
    change E (fun k => scalarTensorUnit K M (a (Equiv.swap i j k))) =
      -E (fun k => scalarTensorUnit K M (a k))
    dsimp only [E]
    rw [scalarMultilinearExtensionOperator_unit, scalarMultilinearExtensionOperator_unit]
    exact F.map_swap a hij
  exact MultilinearMap.congr_fun he v

theorem scalarMultilinearExtension_unit_diagonal {n : ℕ} (F : M [⋀^Fin n]→ₗ[ℤ] V)
    (v : Fin n → K ⊗[ℤ] M) {i j : Fin n} (hij : i ≠ j) (a : M) :
    scalarMultilinearExtensionOperator K M V n F.toMultilinearMap
      (Function.update (Function.update v i (scalarTensorUnit K M a))
        j (scalarTensorUnit K M a)) = 0 := by
  classical
  apply tensorMultilinear_zero_on_generators _ (Finset.univ.erase i |>.erase j)
  intro b
  have he : (fun k => if k ∈ ((Finset.univ.erase i).erase j)
      then scalarTensorUnit K M (b k)
      else (Function.update (Function.update v i (scalarTensorUnit K M a))
        j (scalarTensorUnit K M a)) k) =
      (fun k => scalarTensorUnit K M (Function.update (Function.update b i a) j a k)) := by
    funext k
    by_cases hki : k = i
    · subst k; simp [hij]
    · by_cases hkj : k = j
      · subst k; simp
      · simp [hki, hkj]
  rw [he, scalarMultilinearExtensionOperator_unit]
  exact F.map_eq_zero_of_eq _ (by simp [hij]) hij

theorem scalarMultilinearExtension_diagonal {n : ℕ} (F : M [⋀^Fin n]→ₗ[ℤ] V)
    (v : Fin n → K ⊗[ℤ] M) {i j : Fin n} (hij : i ≠ j) (x : K ⊗[ℤ] M) :
    scalarMultilinearExtensionOperator K M V n F.toMultilinearMap
      (Function.update (Function.update v i x) j x) = 0 := by
  classical
  let E := scalarMultilinearExtensionOperator K M V n F.toMultilinearMap
  let B := multilinearCoordinatePair E v i j hij
  have hswap (x y : K ⊗[ℤ] M) : B x y = -B y x := by
    have h := scalarMultilinearExtension_swap K F
      (Function.update (Function.update v i y) j x) hij
    rw [update_pair_comp_swap _ _ _ hij] at h
    exact h
  change B x x = 0
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    rw [← scalarTensorUnit_smul]
    simp only [map_smul, LinearMap.smul_apply]
    have h : B (scalarTensorUnit K M a) (scalarTensorUnit K M a) = 0 :=
      scalarMultilinearExtension_unit_diagonal K F v hij a
    rw [h, smul_zero, smul_zero]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, hx, hy, zero_add, add_zero]
    rw [hswap x y, add_neg_cancel]

def scalarAlternatingExtension {n : ℕ} (F : M [⋀^Fin n]→ₗ[ℤ] V) :
    (K ⊗[ℤ] M) [⋀^Fin n]→ₗ[K] V where
  toMultilinearMap := scalarMultilinearExtensionOperator K M V n F.toMultilinearMap
  map_eq_zero_of_eq' := by
    intro v i j h hij
    have he : Function.update (Function.update v i (v i)) j (v i) = v := by
      rw [Function.update_eq_self, h, Function.update_eq_self]
    rw [← he]
    exact scalarMultilinearExtension_diagonal K F v hij (v i)

@[simp] theorem scalarAlternatingExtension_unit {n : ℕ} (F : M [⋀^Fin n]→ₗ[ℤ] V)
    (v : Fin n → M) :
    scalarAlternatingExtension K F (fun i => scalarTensorUnit K M (v i)) = F v :=
  scalarMultilinearExtensionOperator_unit K M V n F.toMultilinearMap v

end PolycyclicRecognition

end

end OAI
