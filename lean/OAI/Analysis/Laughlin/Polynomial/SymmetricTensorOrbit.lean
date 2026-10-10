import Mathlib.Logic.Equiv.Fintype
import OAI.Analysis.Laughlin.Polynomial.SymmetricTensorCoordinates

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

noncomputable def tensorPermutation (Q : ℕ) (σ : Equiv.Perm (Fin Q)) :
    (Fin Q → Fin 2) ≃ (Fin Q → Fin 2) where
  toFun a := a ∘ σ
  invFun a := a ∘ σ.symm
  left_inv a := by funext i; simp
  right_inv a := by funext i; simp

 theorem tensorWeight_perm (Q : ℕ) (a : Fin Q → Fin 2) (σ : Equiv.Perm (Fin Q)) :
    tensorWeight Q (a ∘ σ)=tensorWeight Q a := by
  have he : tensorBits Q (a ∘ σ) = (tensorBits Q a).map σ.symm.toEmbedding := by
    ext i
    simp [tensorBits]
  unfold tensorWeight
  rw [he,Finset.card_map]

theorem tensorWeight_eq_exists_perm (Q : ℕ) (a b : Fin Q → Fin 2)
    (h : tensorWeight Q a=tensorWeight Q b) :
    ∃ σ : Equiv.Perm (Fin Q), a ∘ σ=b := by
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_map_finset_eq (tensorBits Q a) (tensorBits Q b) h
  refine ⟨σ.symm,?_⟩
  funext i
  have hm := congrArg (fun s : Finset (Fin Q) => i ∈ s) hσ
  have hh : a (σ.symm i)=1 ↔ b i=1 := by simpa [tensorBits] using Iff.of_eq hm
  apply Fin.ext
  simp only [Fin.ext_iff,Fin.val_one] at hh
  have ha := (a (σ.symm i)).isLt
  have hb := (b i).isLt
  dsimp [Function.comp_def]
  omega

 theorem tensorMatrix_perm (Q : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (a b : Fin Q → Fin 2) (σ : Equiv.Perm (Fin Q)) :
    tensorMatrix Q A (a ∘ σ) (b ∘ σ)=tensorMatrix Q A a b := by
  exact Equiv.prod_comp σ (fun i => A (a i) (b i))

theorem tensorMatrix_preserves_symmetric (Q : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (v : (Fin Q → Fin 2) → ℂ)
    (hv : ∀ a b, tensorWeight Q a=tensorWeight Q b → v a=v b) :
    ∀ a b, tensorWeight Q a=tensorWeight Q b →
      (tensorMatrix Q A *ᵥ v) a=(tensorMatrix Q A *ᵥ v) b := by
  intro a b hab
  obtain ⟨σ,rfl⟩ := tensorWeight_eq_exists_perm Q a b hab
  have he := (tensorPermutation Q σ).sum_comp (fun c => tensorMatrix Q A (a ∘ σ) c*v c)
  change (∑ c, tensorMatrix Q A a c*v c) = ∑ c, tensorMatrix Q A (a ∘ σ) c*v c
  rw [← he]
  apply Finset.sum_congr rfl
  intro c hc
  change tensorMatrix Q A a c*v c = tensorMatrix Q A (a ∘ σ) (c ∘ σ)*v (c ∘ σ)
  rw [tensorMatrix_perm,hv (c ∘ σ) c (tensorWeight_perm Q c σ)]

end Laughlin.Rotation

end OAI
