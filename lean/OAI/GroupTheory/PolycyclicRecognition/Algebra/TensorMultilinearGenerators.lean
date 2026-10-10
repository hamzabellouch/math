import OAI.GroupTheory.PolycyclicRecognition.Algebra.ScalarMultilinearExtension

namespace OAI

/-! # Testing multilinear maps on scalar tensor generators -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
variable {K M V : Type} [Field K] [AddCommGroup M] [Module ℤ M]
  [AddCommGroup V] [Module K V]

theorem scalarTensorUnit_smul (r : K) (a : M) :
    r • scalarTensorUnit K M a = r ⊗ₜ[ℤ] a := by
  change r • ((1 : K) ⊗ₜ[ℤ] a) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem tensorMultilinear_zero_on_generators {n : ℕ}
    (F : MultilinearMap K (fun _ : Fin n => K ⊗[ℤ] M) V)
    (s : Finset (Fin n)) (v : Fin n → K ⊗[ℤ] M)
    (h : ∀ a : Fin n → M,
      F (fun i => if i ∈ s then scalarTensorUnit K M (a i) else v i) = 0) : F v = 0 := by
  classical
  induction s using Finset.induction_on generalizing v with
  | empty => simpa only [Finset.notMem_empty, ↓reduceIte] using h 0
  | @insert i s hi ih =>
    apply ih v
    intro a
    let w : Fin n → K ⊗[ℤ] M :=
      fun j => if j ∈ s then scalarTensorUnit K M (a j) else v j
    have hz (x : K ⊗[ℤ] M) : F (Function.update w i x) = 0 := by
      induction x using TensorProduct.inductionOn with
      | tmul r b =>
        rw [← scalarTensorUnit_smul, F.map_update_smul]
        have he : Function.update w i (scalarTensorUnit K M b) =
            (fun j => if j ∈ insert i s then scalarTensorUnit K M (Function.update a i b j)
              else v j) := by
          funext j
          by_cases hj : j = i
          · subst j; simp [w]
          · simp [w, hj]
        rw [he, h, smul_zero]
      | add x y hx hy => rw [F.map_update_add, hx, hy, add_zero]
    have he : Function.update w i (v i) = w := by
      apply Function.update_eq_self_iff.mpr
      simp [w, hi]
    simpa only [he] using hz (v i)

theorem tensorMultilinear_ext {n : ℕ}
    (F G : MultilinearMap K (fun _ : Fin n => K ⊗[ℤ] M) V)
    (h : ∀ a : Fin n → M,
      F (fun i => scalarTensorUnit K M (a i)) =
        G (fun i => scalarTensorUnit K M (a i))) : F = G := by
  ext v
  apply sub_eq_zero.mp
  apply tensorMultilinear_zero_on_generators (F - G) Finset.univ v
  intro a
  simpa only [Finset.mem_univ, ↓reduceIte, sub_apply, sub_eq_zero] using h a

end PolycyclicRecognition

end

end OAI
