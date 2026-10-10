import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.PackSplit

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.SeparatedSymmetry
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def reynoldsS (d : I → ℕ) :
    MvPolynomial (Σi,Fin (d i)) ℚ →ₗ[ℚ] S d where
  toFun f := ⟨average (packAction (fun i=>Fin (d i))) f,
    fun σ => rename_average _ σ f⟩
  map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
  map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _

@[simp] lemma reynoldsS_val (d : I → ℕ) (f : S d) : reynoldsS d f.val = f := by
  apply Subtype.ext
  exact average_fixed _ f.val f.property

lemma tensorEquivSum_tmul {α β : Type*} (f : MvPolynomial α ℚ) (g : MvPolynomial β ℚ) :
    tensorEquivSum ℚ α β ℚ (f ⊗ₜ[ℚ] g) = rename Sum.inl f * rename Sum.inr g := by
  let H := tensorEquivSum ℚ α β ℚ
  have hL : H.toAlgHom.comp Algebra.TensorProduct.includeLeft = rename (R:=ℚ) Sum.inl := by
    ext i
    simp [H]
  have hR : H.toAlgHom.comp Algebra.TensorProduct.includeRight = rename (R:=ℚ) Sum.inr := by
    ext i
    simp [H]
  change H (f ⊗ₜ[ℚ] g) = _
  have ht : f ⊗ₜ[ℚ] g = (f ⊗ₜ[ℚ] (1 : MvPolynomial β ℚ)) * ((1 : MvPolynomial α ℚ) ⊗ₜ[ℚ] g) := by
    simp
  rw [ht, map_mul]
  exact congrArg₂ (· * ·) (DFunLike.congr_fun hL f) (DFunLike.congr_fun hR g)

noncomputable def tensorValue (d e : I → ℕ) :
    S d ⊗[ℚ] S e →ₗ[ℚ] MvPolynomial ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i))) ℚ :=
  (tensorEquivSum ℚ _ _ ℚ).toLinearMap ∘ₗ
    TensorProduct.map (symmetricSpace d).val.toLinearMap (symmetricSpace e).val.toLinearMap

omit [Fintype I] [DecidableEq I] in
@[simp] lemma tensorValue_tmul (d e : I → ℕ) (f : S d) (g : S e) :
    tensorValue d e (f ⊗ₜ[ℚ] g) = rename Sum.inl f.val * rename Sum.inr g.val := by
  exact tensorEquivSum_tmul f.val g.val

noncomputable def separateTensor (d e : I → ℕ) :
    MvPolynomial ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i))) ℚ →ₗ[ℚ] S d ⊗[ℚ] S e :=
  TensorProduct.map (reynoldsS d) (reynoldsS e) ∘ₗ
    (tensorEquivSum ℚ _ _ ℚ).symm.toLinearMap

@[simp] lemma separateTensor_product (d e : I → ℕ) (f : S d) (g : S e) :
    separateTensor d e (rename Sum.inl f.val * rename Sum.inr g.val) = f ⊗ₜ[ℚ] g := by
  rw [← tensorEquivSum_tmul]
  simp [separateTensor]

@[simp] lemma separateTensor_tensorValue (d e : I → ℕ) (f : S d ⊗[ℚ] S e) :
    separateTensor d e (tensorValue d e f) = f := by
  induction f using TensorProduct.inductionOn with
  | tmul f g => simp
  | add x y hx hy => simp [hx,hy]

lemma tensorValue_injective (d e : I → ℕ) : Function.Injective (tensorValue d e) := by
  intro f g h
  simpa using congrArg (separateTensor d e) h

lemma tensorValue_separateTensor (d e : I → ℕ)
    (f : MvPolynomial ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i))) ℚ)
    (hf : ∀ σ, rename (sumAction (packAction (fun i=>Fin (d i)))
      (packAction (fun i=>Fin (e i))) σ) f = f) :
    tensorValue d e (separateTensor d e f) = f := by
  have h := invariant_separated_span (packAction (fun i=>Fin (d i)))
    (packAction (fun i=>Fin (e i))) f hf
  clear hf
  induction h using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨f,g,hf,hg,rfl⟩ := hp
    change tensorValue d e (separateTensor d e
      (rename Sum.inl (⟨f,hf⟩ : S d).val * rename Sum.inr (⟨g,hg⟩ : S e).val)) = _
    rw [separateTensor_product,tensorValue_tmul]
  | zero => simp
  | add x y hx hy ihx ihy => simp [ihx,ihy]
  | smul c x hx ih => simp [ih]

noncomputable def restrictTensor {d e : I → ℕ} (A : Cut d e) : S (d+e) →ₗ[ℚ] S d ⊗[ℚ] S e :=
  separateTensor d e ∘ₗ (rename (cutSplit A).symm).toLinearMap ∘ₗ
    (symmetricSpace (d+e)).val.toLinearMap

@[simp] lemma tensorValue_restrictTensor {d e : I → ℕ} (A : Cut d e) (f : S (d+e)) :
    tensorValue d e (restrictTensor A f) = rename (cutSplit A).symm f.val := by
  exact tensorValue_separateTensor d e _ (split_symmetric A f)

lemma restrictTensor_independent {d e : I → ℕ} (A B : Cut d e) (f : S (d+e)) :
    restrictTensor A f = restrictTensor B f := by
  apply tensorValue_injective
  rw [tensorValue_restrictTensor,tensorValue_restrictTensor]
  apply rename_injective (cutSplit B) (cutSplit B).injective
  rw [split_symmetric_independent]
  simp only [rename_rename]
  simp

noncomputable def restrictQuotientAt (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e : I → ℕ} (A : Cut d e) (z w : ℚ) :
    S (d+e) →ₗ[ℚ] B a μ d ⊗[ℚ] B a μ e :=
  TensorProduct.map
    ((destabilizingSpace a μ d).mkQ ∘ₗ translationS d z)
    ((destabilizingSpace a μ e).mkQ ∘ₗ translationS e w) ∘ₗ restrictTensor A

lemma restrictQuotientAt_independent (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e : I → ℕ} (A B : Cut d e) (z w : ℚ) :
    restrictQuotientAt a μ A z w = restrictQuotientAt a μ B z w := by
  apply LinearMap.ext
  intro f
  simp only [restrictQuotientAt,LinearMap.comp_apply,restrictTensor_independent A B]

end ElementaryPositivity.RawShuffle

end

end OAI
