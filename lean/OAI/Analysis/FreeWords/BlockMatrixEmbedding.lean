import Mathlib
import OAI.Analysis.FreeWords.MatrixConditionalExpectation
import OAI.Analysis.FreeWords.MatrixTraceUnique

namespace OAI

noncomputable section

namespace KKBlockMatrix

open KKMatrixExpectation

noncomputable section

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def blockHom (ρ : Matrix κ κ ℂ →⋆ₐ[ℂ] A) :
    Matrix (ι×κ) (ι×κ) ℂ →⋆ₐ[ℂ] Matrix ι ι A :=
  { (ρ.toAlgHom.mapMatrix).comp (Matrix.compAlgEquiv ι κ ℂ ℂ).symm.toAlgHom with
    map_star' := by
      intro X
      ext i j
      exact map_star ρ (fun a b => X (j,a) (i,b)) }

omit [StarModule ℂ A] in
@[simp] theorem blockHom_apply (ρ : Matrix κ κ ℂ →⋆ₐ[ℂ] A)
    (X : Matrix (ι×κ) (ι×κ) ℂ) (i j : ι) :
    blockHom ρ X i j=ρ (fun a b => X (i,a) (j,b)) := rfl

omit [StarModule ℂ A] in
theorem blockHom_injective (ρ : Matrix κ κ ℂ →⋆ₐ[ℂ] A) (hρ : Function.Injective ρ) :
    Function.Injective (blockHom (ι := ι) ρ) := by
  intro X Y he
  ext ⟨i,a⟩ ⟨j,b⟩
  exact congrFun (congrFun (hρ (congrFun (congrFun he i) j)) a) b

theorem blockHom_entry_mem (ρ : Matrix κ κ ℂ →⋆ₐ[ℂ] A)
    (X : Matrix (ι×κ) (ι×κ) ℂ) (i j : ι) : blockHom ρ X i j∈ρ.range :=
  ⟨fun a b => X (i,a) (j,b),rfl⟩

theorem blockHom_kronecker {n d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ →⋆ₐ[ℂ] A)
    (b : Matrix (Fin n) (Fin n) ℂ) :
    blockHom ρ (Matrix.kronecker b 1)=numericalHom (A := A) n b := by
  ext i j
  change ρ (fun a c => b i j*(1 : Matrix (Fin d) (Fin d) ℂ) a c)=algebraMap ℂ A (b i j)
  have he : (fun a c => b i j*(1 : Matrix (Fin d) (Fin d) ℂ) a c)=
      algebraMap ℂ (Matrix (Fin d) (Fin d) ℂ) (b i j) := by
    ext a c
    simp [Matrix.algebraMap_eq_diagonal,Matrix.diagonal_apply,Matrix.one_apply]
  rw [he]
  exact ρ.commutes (b i j)

omit [StarModule ℂ A] in
theorem blockHom_trace {n d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ →⋆ₐ[ℂ] A)
    [NeZero d] (τ : A →ₗ[ℂ] ℂ) (hτ1 : τ 1=1) (htr : ∀x y,τ (x*y)=τ (y*x))
    (X : Matrix (Fin n×Fin d) (Fin n×Fin d) ℂ) :
    matrixTraceMap τ n (blockHom ρ X)=((n*d:ℕ):ℂ)⁻¹*Matrix.trace X := by
  change (n:ℂ)⁻¹*(∑i:Fin n,τ (ρ (fun a b => X (i,a) (i,b))))=_
  have he : (∑i:Fin n,τ (ρ (fun a b => X (i,a) (i,b))))=
      ∑i:Fin n,(d:ℂ)⁻¹*(∑a:Fin d,X (i,a) (i,a)) := by
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [Fintype.card_fin,Matrix.trace,Matrix.diag] using KKVariableUltra.matrixHom_trace ρ τ hτ1 htr (fun a b => X (i,a) (i,b))
  rw [he,← Finset.mul_sum]
  simp only [Matrix.trace,Matrix.diag,Fintype.sum_prod_type,Nat.cast_mul,mul_inv_rev]
  ring

end

end KKBlockMatrix
end

end OAI
