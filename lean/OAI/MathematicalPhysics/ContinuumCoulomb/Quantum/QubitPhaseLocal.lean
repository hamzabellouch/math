import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitPhase

namespace OAI

/-! Rotated mediator couplings are still one-local and have the required
entry parity to keep the physical Hamiltonian real. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def qmaBitZ (e : κ) : Matrix (κ → Fin 2) (κ → Fin 2) ℂ :=
  Matrix.diagonal (fun a => if a e = 1 then -1 else 1)

theorem qmaBitZ_local (e : κ) : QMALocalOn {e} (qmaBitZ e) := by
  apply qmaLocalOn_diagonal
  intro s t h
  rw [h e (Finset.mem_singleton_self e)]

theorem qmaPolarizedFlip_eq (m : κ → Bool) (e : κ) :
    qmaPolarizedFlip m e = if m e = true then
      Complex.I • (qmaBitFlipMatrix e*qmaBitZ e) else qmaBitFlipMatrix e := by
  ext a b
  have hdiag : (qmaBitFlipMatrix e*qmaBitZ e) a b =
      qmaBitFlipMatrix e a b*(if b e = 1 then -1 else 1) := by
    simp [qmaBitZ,Matrix.mul_apply,Matrix.diagonal_apply]
  by_cases hm : m e = true
  · simp only [hm,ite_true,Matrix.smul_apply,smul_eq_mul,hdiag,qmaBitFlipMatrix,qmaPolarizedFlip]
    split_ifs <;> ring
  · simp [qmaPolarizedFlip,qmaBitFlipMatrix,hm]

theorem qmaPolarizedFlip_local (m : κ → Bool) (e : κ) : QMALocalOn {e} (qmaPolarizedFlip m e) := by
  rw [qmaPolarizedFlip_eq]
  split_ifs
  · exact ((qmaBitFlipMatrix_local e).mul (qmaBitZ_local e)).smul Complex.I
  · exact qmaBitFlipMatrix_local e

theorem qmaPolarizedFlip_im_zero (m : κ → Bool) (e : κ) (h : m e = false)
    (a b : κ → Fin 2) : (qmaPolarizedFlip m e a b).im = 0 := by
  simp only [qmaPolarizedFlip,h,Bool.false_eq_true,ite_false]
  split_ifs <;> norm_num

theorem qmaPolarizedFlip_re_zero (m : κ → Bool) (e : κ) (h : m e = true)
    (a b : κ → Fin 2) : (qmaPolarizedFlip m e a b).re = 0 := by
  simp only [qmaPolarizedFlip,h,ite_true]
  split_ifs <;> norm_num

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [Fintype σ] [DecidableEq σ] in
theorem qmaPolarizedTensor_real (m : κ → Bool) (e : κ) (M : Matrix σ σ ℂ)
    (hM : if m e = true then ∀ s t, (M s t).re = 0 else ∀ s t, (M s t).im = 0)
    (p q : σ × (κ → Fin 2)) : ((M ⊗ₖ qmaPolarizedFlip m e) p q).im = 0 := by
  rcases p with ⟨s,a⟩
  rcases q with ⟨t,b⟩
  simp only [Matrix.kronecker_apply,Complex.mul_im]
  cases he : m e
  · simp only [he,Bool.false_eq_true,ite_false] at hM
    rw [hM s t,qmaPolarizedFlip_im_zero m e he]
    ring
  · simp only [he,ite_true] at hM
    rw [hM s t,qmaPolarizedFlip_re_zero m e he]
    ring

end ContinuumCoulomb

end

end OAI
