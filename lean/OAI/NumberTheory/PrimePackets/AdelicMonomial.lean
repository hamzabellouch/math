import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicDiagonalizerDefinitions

namespace OAI

noncomputable section
open scoped MatrixGroups
open Matrix Module Set
namespace PrimeDegreePackets.Adelic

lemma invertibleMatrix_column_nonzero {n : ℕ} (H : GL (Fin n) ℝ) (j : Fin n) :
    ∃ i, H.val i j ≠ 0 := by
  by_contra! hz
  have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A j j) H.inv_val
  simp only [Matrix.mul_apply,Matrix.one_apply_eq] at h
  simp [hz] at h

lemma invertibleMatrix_row_nonzero {n : ℕ} (H : GL (Fin n) ℝ) (i : Fin n) :
    ∃ j, H.val i j ≠ 0 := by
  by_contra! hz
  have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i i) H.val_inv
  simp only [Matrix.mul_apply,Matrix.one_apply_eq] at h
  simp [hz] at h

 

lemma monomial_of_diagonal_intertwiner {n : ℕ} (H : GL (Fin n) ℝ)
    (z v : Fin n → ℝ) (hz : Function.Injective z)
    (hH : Matrix.diagonal z * H.val = H.val * Matrix.diagonal v) :
    ∃ τ : Equiv.Perm (Fin n), ∃ c : (Fin n → ℝ)ˣ,
      ∀ i j, H.val i j = if i = τ j then c.val j else 0 := by
  classical
  have hentry (i j) : z i * H.val i j = H.val i j * v j := by
    simpa only [Matrix.diagonal_mul,Matrix.mul_diagonal] using
      congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) hH
  have heigen (i j) (hij : H.val i j ≠ 0) : z i = v j := by
    apply mul_right_cancel₀ hij
    rw [hentry,mul_comm]
  choose τ hτ using invertibleMatrix_column_nonzero H
  have hsupport (i j) (hij : i ≠ τ j) : H.val i j = 0 := by
    by_contra hne
    exact hij (hz ((heigen i j hne).trans (heigen (τ j) j (hτ j)).symm))
  have hsurj : Function.Surjective τ := by
    intro i
    obtain ⟨j,hj⟩ := invertibleMatrix_row_nonzero H i
    use j
    by_contra he
    exact hj (hsupport i j (Ne.symm he))
  let e : Equiv.Perm (Fin n) := Equiv.ofBijective τ
    ((Fintype.bijective_iff_surjective_and_card τ).mpr ⟨hsurj,rfl⟩)
  let c : (Fin n → ℝ)ˣ :=
    { val := fun j => H.val (τ j) j
      inv := fun j => (H.val (τ j) j)⁻¹
      val_inv := by ext j; exact mul_inv_cancel₀ (hτ j)
      inv_val := by ext j; exact inv_mul_cancel₀ (hτ j) }
  refine ⟨e,c,?_⟩
  intro i j
  change H.val i j = if i = τ j then H.val (τ j) j else 0
  split_ifs with he
  · rw [he]
  · exact hsupport i j he

end PrimeDegreePackets.Adelic

end

end OAI
