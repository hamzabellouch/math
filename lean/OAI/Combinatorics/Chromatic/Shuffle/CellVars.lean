import Mathlib
import OAI.Combinatorics.Chromatic.Walls.ShuffleTensorLinear

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.SeparatedSymmetry
open scoped TensorProduct
variable {I : Type*}

abbrev CellVars (d e : I → ℕ) := (Σi,Fin (d i)) ⊕ (Σi,Fin (e i))
abbrev CellGroup (d e : I → ℕ) :=
  (∀ i,Equiv.Perm (Fin (d i))) × (∀ i,Equiv.Perm (Fin (e i)))

def cellAction (d e : I → ℕ) : CellGroup d e →* Equiv.Perm (CellVars d e) :=
  sumAction (packAction (fun i=>Fin (d i))) (packAction (fun i=>Fin (e i)))

noncomputable def fourValue (d₁ e₁ d₂ e₂ : I → ℕ) :
    (S d₁ ⊗[ℚ] S e₁) ⊗[ℚ] (S d₂ ⊗[ℚ] S e₂) →ₗ[ℚ]
      MvPolynomial (CellVars d₁ e₁ ⊕ CellVars d₂ e₂) ℚ :=
  (tensorEquivSum ℚ _ _ ℚ).toLinearMap ∘ₗ
    TensorProduct.map (tensorValue d₁ e₁) (tensorValue d₂ e₂)

@[simp] lemma fourValue_tmul (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : S d₁ ⊗[ℚ] S e₁) (g : S d₂ ⊗[ℚ] S e₂) :
    fourValue d₁ e₁ d₂ e₂ (f ⊗ₜ[ℚ] g) =
      rename Sum.inl (tensorValue d₁ e₁ f) * rename Sum.inr (tensorValue d₂ e₂ g) :=
  tensorEquivSum_tmul _ _

variable [Fintype I] [DecidableEq I]

noncomputable def separateFour (d₁ e₁ d₂ e₂ : I → ℕ) :
    MvPolynomial (CellVars d₁ e₁ ⊕ CellVars d₂ e₂) ℚ →ₗ[ℚ]
      (S d₁ ⊗[ℚ] S e₁) ⊗[ℚ] (S d₂ ⊗[ℚ] S e₂) :=
  TensorProduct.map (separateTensor d₁ e₁) (separateTensor d₂ e₂) ∘ₗ
    (tensorEquivSum ℚ _ _ ℚ).symm.toLinearMap

@[simp] lemma separateFour_product (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : MvPolynomial (CellVars d₁ e₁) ℚ) (g : MvPolynomial (CellVars d₂ e₂) ℚ) :
    separateFour d₁ e₁ d₂ e₂ (rename Sum.inl f * rename Sum.inr g) =
      separateTensor d₁ e₁ f ⊗ₜ[ℚ] separateTensor d₂ e₂ g := by
  rw [← tensorEquivSum_tmul]
  simp [separateFour]

lemma fourValue_separateFour (d₁ e₁ d₂ e₂ : I → ℕ)
    (p : MvPolynomial (CellVars d₁ e₁ ⊕ CellVars d₂ e₂) ℚ)
    (hp : ∀ σ, rename (sumAction (cellAction d₁ e₁) (cellAction d₂ e₂) σ) p = p) :
    fourValue d₁ e₁ d₂ e₂ (separateFour d₁ e₁ d₂ e₂ p) = p := by
  have hh := invariant_separated_span (cellAction d₁ e₁) (cellAction d₂ e₂) p hp
  clear hp
  induction hh using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨f,g,hf,hg,rfl⟩ := hp
    rw [separateFour_product,fourValue_tmul,
      tensorValue_separateTensor d₁ e₁ f hf,tensorValue_separateTensor d₂ e₂ g hg]
  | zero => rw [(separateFour d₁ e₁ d₂ e₂).map_zero, (fourValue d₁ e₁ d₂ e₂).map_zero]
  | add f g hf hg ihf ihg => simp only [map_add,ihf,ihg]
  | smul c f hf ih => simp only [map_smul,ih]

@[simp] lemma separateFour_fourValue (d₁ e₁ d₂ e₂ : I → ℕ)
    (p : (S d₁ ⊗[ℚ] S e₁) ⊗[ℚ] (S d₂ ⊗[ℚ] S e₂)) :
    separateFour d₁ e₁ d₂ e₂ (fourValue d₁ e₁ d₂ e₂ p) = p := by
  induction p using TensorProduct.inductionOn with
  | tmul f g => simp only [fourValue_tmul,separateFour_product,separateTensor_tensorValue]
  | add f g hf hg => simp only [map_add,hf,hg]

lemma fourValue_injective (d₁ e₁ d₂ e₂ : I → ℕ) :
    Function.Injective (fourValue d₁ e₁ d₂ e₂) :=
  Function.LeftInverse.injective (separateFour_fourValue d₁ e₁ d₂ e₂)

noncomputable def cellTransfer (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    MvPolynomial (CellVars d₁ e₁ ⊕ CellVars d₂ e₂) ℚ →ₗ[ℚ]
      S (d₁+e₁) ⊗[ℚ] S (d₂+e₂) :=
  twoTargetTransfer a d₁ e₁ d₂ e₂ ∘ₗ separateFour d₁ e₁ d₂ e₂

lemma quotient_cellTransfer_zero (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d₁ e₁ d₂ e₂ : I → ℕ)
    (h : (d₁≠0 ∧ e₁≠0 ∧ μ d₁ > μ (d₁+e₁)) ∨
         (d₂≠0 ∧ e₂≠0 ∧ μ d₂ > μ (d₂+e₂)))
    (p : MvPolynomial (CellVars d₁ e₁ ⊕ CellVars d₂ e₂) ℚ) :
    quotientTensor a μ (d₁+e₁) (d₂+e₂) (cellTransfer a d₁ e₁ d₂ e₂ p) = 0 :=
  quotient_twoTargetTransfer_zero a μ d₁ e₁ d₂ e₂ h _

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.SeparatedSymmetry
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def renameInjFraction {α β : Type*} (f : α → β) (hf : Function.Injective f) :
    FractionRing (MvPolynomial α ℚ) →+* FractionRing (MvPolynomial β ℚ) :=
  IsFractionRing.lift (g := (algebraMap (MvPolynomial β ℚ)
    (FractionRing (MvPolynomial β ℚ))).comp (rename f).toRingHom)
    ((IsFractionRing.injective (MvPolynomial β ℚ) _).comp (MvPolynomial.rename_injective f hf))

@[simp] lemma renameInjFraction_algebraMap {α β : Type*} (f : α → β) (hf : Function.Injective f)
    (p : MvPolynomial α ℚ) :
    renameInjFraction f hf (algebraMap _ (FractionRing (MvPolynomial α ℚ)) p) =
      algebraMap _ (FractionRing (MvPolynomial β ℚ)) (rename f p) := by
  exact IsFractionRing.lift_algebraMap (g := (algebraMap (MvPolynomial β ℚ)
    (FractionRing (MvPolynomial β ℚ))).comp (rename f).toRingHom) _ _

noncomputable def localizeTensor (d e : I → ℕ) :
    S d ⊗[ℚ] S e →ₗ[ℚ] FractionRing (MvPolynomial (CellVars d e) ℚ) where
  toFun f := algebraMap _ _ (tensorValue d e f)
  map_add' := by intro f g; rw [map_add,map_add]
  map_smul' := by
    intro r f
    rw [map_smul]
    exact map_rat_smul (algebraMap (MvPolynomial (CellVars d e) ℚ)
      (FractionRing (MvPolynomial (CellVars d e) ℚ))) r _

lemma localizeTensor_injective (d e : I → ℕ) : Function.Injective (localizeTensor d e) := by
  intro f g h
  apply tensorValue_injective d e
  exact IsFractionRing.injective _ (FractionRing (MvPolynomial (CellVars d e) ℚ)) h

noncomputable def cutKernel (a : I → I → ℕ) {d e : I → ℕ} (A : Cut d e) :
    FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ) :=
  algebraMap _ _ (∏ i, ∏ j,cutFactor A i j (a i j)) /
    algebraMap _ _ (cutDenominator A)

lemma tensorShuffle_kernel (a : I → I → ℕ) {d e : I → ℕ}
    (p : MvPolynomial (CellVars d e) ℚ) : tensorShuffle a p =
      ∑ A : Cut d e, algebraMap _ _ (rename (cutSplit A) p) * cutKernel a A := by
  simp only [tensorShuffle,LinearMap.coe_mk,AddHom.coe_mk,map_mul,cutKernel,mul_div_assoc]

noncomputable def doubleTensorShuffle (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    MvPolynomial (CellVars d₁ e₁ ⊕ CellVars d₂ e₂) ℚ →ₗ[ℚ]
      FractionRing (MvPolynomial (CellVars (d₁+e₁) (d₂+e₂)) ℚ) where
  toFun p := ∑ A : Cut d₁ e₁, ∑ B : Cut d₂ e₂,
    algebraMap _ _ (rename (Sum.map (cutSplit A) (cutSplit B)) p) *
    renameInjFraction Sum.inl Sum.inl_injective (cutKernel a A) *
    renameInjFraction Sum.inr Sum.inr_injective (cutKernel a B)
  map_add' := by
    intro p q
    simp only [map_add,add_mul,Finset.sum_add_distrib]
  map_smul' := by
    let : DistribSMul ℚ (FractionRing (MvPolynomial (CellVars (d₁+e₁) (d₂+e₂)) ℚ)) :=
      (inferInstance : Module ℚ (FractionRing (MvPolynomial (CellVars (d₁+e₁) (d₂+e₂)) ℚ))).toDistribMulAction.toDistribSMul
    intro r p
    simp only [map_smul,map_rat_smul,smul_mul_assoc,Finset.smul_sum,RingHom.id_apply]

lemma doubleTensorShuffle_product (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : MvPolynomial (CellVars d₁ e₁) ℚ) (g : MvPolynomial (CellVars d₂ e₂) ℚ) :
    doubleTensorShuffle a d₁ e₁ d₂ e₂ (rename Sum.inl f * rename Sum.inr g) =
      renameInjFraction Sum.inl Sum.inl_injective (tensorShuffle a f) *
      renameInjFraction Sum.inr Sum.inr_injective (tensorShuffle a g) := by
  rw [tensorShuffle_kernel,tensorShuffle_kernel]
  simp only [map_sum,map_mul,renameInjFraction_algebraMap,
    Finset.sum_mul,Finset.mul_sum,doubleTensorShuffle,LinearMap.coe_mk,AddHom.coe_mk,
    rename_rename]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro B hB
  change
    (algebraMap _ _ (rename (Sum.inl ∘ cutSplit A) f) *
      algebraMap _ _ (rename (Sum.inr ∘ cutSplit B) g)) * _ * _ = _
  ring

lemma doubleTensorShuffle_fourValue (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : (S d₁ ⊗[ℚ] S e₁) ⊗[ℚ] (S d₂ ⊗[ℚ] S e₂)) :
    doubleTensorShuffle a d₁ e₁ d₂ e₂ (fourValue d₁ e₁ d₂ e₂ f) =
      localizeTensor (d₁+e₁) (d₂+e₂) (twoTargetTransfer a d₁ e₁ d₂ e₂ f) := by
  induction f using TensorProduct.inductionOn with
  | tmul f g =>
    rw [fourValue_tmul,doubleTensorShuffle_product,tensorShuffle_tensorValue,
      tensorShuffle_tensorValue]
    simp only [localizeS_apply,
      twoTargetTransfer,TensorProduct.map_tmul,localizeTensor,LinearMap.coe_mk,AddHom.coe_mk,
      tensorValue_tmul,map_mul]
    exact congrArg₂ (· * ·)
      (renameInjFraction_algebraMap Sum.inl Sum.inl_injective _)
      (renameInjFraction_algebraMap Sum.inr Sum.inr_injective _)
  | add f g hf hg =>
    rw [(fourValue d₁ e₁ d₂ e₂).map_add,
      (doubleTensorShuffle a d₁ e₁ d₂ e₂).map_add,
      (twoTargetTransfer a d₁ e₁ d₂ e₂).map_add,
      (localizeTensor (d₁+e₁) (d₂+e₂)).map_add,hf,hg]

lemma doubleTensorShuffle_invariant (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (p : MvPolynomial (CellVars d₁ e₁ ⊕ CellVars d₂ e₂) ℚ)
    (hp : ∀ σ, rename (sumAction (cellAction d₁ e₁) (cellAction d₂ e₂) σ) p = p) :
    doubleTensorShuffle a d₁ e₁ d₂ e₂ p =
      localizeTensor (d₁+e₁) (d₂+e₂) (cellTransfer a d₁ e₁ d₂ e₂ p) := by
  change _ = localizeTensor _ _ (twoTargetTransfer _ _ _ _ _ (separateFour _ _ _ _ p))
  rw [← doubleTensorShuffle_fourValue, fourValue_separateFour d₁ e₁ d₂ e₂ p hp]

end ElementaryPositivity.RawShuffle

end

end OAI
