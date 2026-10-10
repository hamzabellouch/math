import OAI.GroupTheory.PolycyclicRecognition.Algebra.ScalarExtendedH2CrossProduct
import Mathlib.LinearAlgebra.Multilinear.Curry

namespace OAI

/-! # Extending integral multilinear maps along a scalar extension -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
variable (K : Type) [Field K]
variable (M V : Type) [AddCommGroup M] [Module ℤ M] [AddCommGroup V] [Module K V]

def scalarMultilinearExtensionOperator : (n : ℕ) →
    MultilinearMap ℤ (fun _ : Fin n => M) V →ₗ[ℤ]
      MultilinearMap K (fun _ : Fin n => K ⊗[ℤ] M) V
  | 0 =>
    ((MultilinearMap.constLinearEquivOfIsEmpty K K _ _ :
      V ≃ₗ[K] MultilinearMap K (fun _ : Fin 0 => K ⊗[ℤ] M) V).toLinearMap.restrictScalars ℤ).comp
      (MultilinearMap.constLinearEquivOfIsEmpty ℤ ℤ _ _ :
        V ≃ₗ[ℤ] MultilinearMap ℤ (fun _ : Fin 0 => M) V).symm.toLinearMap
  | n + 1 =>
    ((multilinearCurryLeftEquiv K (fun _ : Fin (n + 1) => K ⊗[ℤ] M) V).symm.toLinearMap.restrictScalars ℤ).comp
      ((scalarExtensionOperator K).comp
        ((LinearMap.compRight ℤ (scalarMultilinearExtensionOperator n)).comp
          (multilinearCurryLeftEquiv ℤ (fun _ : Fin (n + 1) => M) V).toLinearMap))

@[simp] theorem scalarMultilinearExtensionOperator_zero
    (f : MultilinearMap ℤ (fun _ : Fin 0 => M) V) (v : Fin 0 → K ⊗[ℤ] M) :
    scalarMultilinearExtensionOperator K M V 0 f v = f 0 := rfl

@[simp] theorem scalarMultilinearExtensionOperator_succ (n : ℕ)
    (f : MultilinearMap ℤ (fun _ : Fin (n + 1) => M) V)
    (v : Fin (n + 1) → K ⊗[ℤ] M) :
    scalarMultilinearExtensionOperator K M V (n + 1) f v =
      scalarExtensionLinear K ((scalarMultilinearExtensionOperator K M V n).comp f.curryLeft)
        (v 0) (Fin.tail v) := rfl

theorem scalarMultilinearExtensionOperator_tmul (n : ℕ)
    (f : MultilinearMap ℤ (fun _ : Fin n => M) V) (r : Fin n → K) (v : Fin n → M) :
    scalarMultilinearExtensionOperator K M V n f (fun i => r i ⊗ₜ[ℤ] v i) =
      (∏ i, r i) • f v := by
  induction n with
  | zero =>
    simp only [scalarMultilinearExtensionOperator_zero, Finset.univ_eq_empty,
      Finset.prod_empty, one_smul]
    exact congrArg f (Subsingleton.elim _ _)
  | succ n ih =>
    rw [scalarMultilinearExtensionOperator_succ, scalarExtensionLinear_tmul]
    change r 0 • scalarMultilinearExtensionOperator K M V n (f.curryLeft (v 0))
      (fun i => r i.succ ⊗ₜ[ℤ] v i.succ) = _
    rw [ih, smul_smul, Fin.prod_univ_succ, MultilinearMap.curryLeft_apply]
    change _ • f (Fin.cons (v 0) (Fin.tail v)) = _
    rw [Fin.cons_self_tail]

@[simp] theorem scalarMultilinearExtensionOperator_unit (n : ℕ)
    (f : MultilinearMap ℤ (fun _ : Fin n => M) V) (v : Fin n → M) :
    scalarMultilinearExtensionOperator K M V n f (fun i => scalarTensorUnit K M (v i)) = f v := by
  change scalarMultilinearExtensionOperator K M V n f (fun i => (1 : K) ⊗ₜ[ℤ] v i) = f v
  simpa only [Finset.prod_const_one, one_smul] using
    scalarMultilinearExtensionOperator_tmul K M V n f (fun _ => 1) v

end PolycyclicRecognition

end

end OAI
