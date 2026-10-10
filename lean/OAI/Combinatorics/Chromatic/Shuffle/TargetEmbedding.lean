import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.SumPackCut

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,DecidableEq (A i)]

noncomputable def targetEmbedding {d e : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization d (left p)) (T : Realization e (right p)) :
    CellVars d e ↪ (Σi,A i) where
  toFun := Sum.elim (realizationMap R) (realizationMap T)
  inj' := by
    rintro (x|x) (y|y) h
    · exact congrArg Sum.inl (realizationMap_injective R h)
    · rcases x with ⟨i,x⟩
      rcases y with ⟨j,y⟩
      have hij := congrArg Sigma.fst h
      change i=j at hij
      subst j
      have hxy : (R i x).val = (T i y).val := eq_of_heq (Sigma.mk.inj_iff.mp h).2
      exact (Finset.disjoint_left.mp (p i).property.1 (R i x).property
        (hxy.symm ▸ (T i y).property)).elim
    · rcases x with ⟨i,x⟩
      rcases y with ⟨j,y⟩
      have hij := congrArg Sigma.fst h
      change i=j at hij
      subst j
      have hxy : (T i x).val = (R i y).val := eq_of_heq (Sigma.mk.inj_iff.mp h).2
      exact (Finset.disjoint_left.mp (p i).property.1 (R i y).property
        (hxy ▸ (T i x).property)).elim
    · exact congrArg Sum.inr (realizationMap_injective T h)

omit [Fintype I] [DecidableEq I] in
lemma gridEmbedding_square {d₁ e₁ d₂ e₂ : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization (d₁+e₁) (left p))
    (T : Realization (d₂+e₂) (right p)) (u : Cut d₁ e₁) (v : Cut d₂ e₂) :
    targetEmbedding p R T ∘ Sum.map (cutSplit u) (cutSplit v) ∘ fourPackEquiv d₁ e₁ d₂ e₂ =
      packEmbedding (gridEmbedding p R T u v) := by
  funext z
  rcases z with ⟨i,z⟩
  rcases z with (x|x) <;> rcases x with (x|x) <;> rfl

lemma gridPolynomial_four_realization (a : I → I → ℕ) {d e : I → ℕ} (f : S d) (g : S e)
    {d₁ e₁ d₂ e₂ : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization (d₁+e₁) (left p))
    (T : Realization (d₂+e₂) (right p)) (u : Cut d₁ e₁) (v : Cut d₂ e₂) :
    rename (targetEmbedding p R T) (rename (Sum.map (cutSplit u) (cutSplit v))
      (fourGridPolynomial a f g d₁ e₁ d₂ e₂)) =
      gridPolynomial a f g p (cutRealizationEquiv R u).val (cutRealizationEquiv T v).val := by
  simp only [fourGridPolynomial,rename_rename]
  change rename (targetEmbedding p R T ∘ Sum.map (cutSplit u) (cutSplit v) ∘
    fourPackEquiv d₁ e₁ d₂ e₂) _ = _
  rw [gridEmbedding_square,gridPolynomial_realization]

omit [Fintype I] [DecidableEq I] in
lemma targetEmbedding_algebraMap {d e : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization d (left p)) (T : Realization e (right p))
    (P : MvPolynomial (CellVars d e) ℚ) :
    renameInjFraction (targetEmbedding p R T) (targetEmbedding p R T).injective
      (algebraMap _ (FractionRing (MvPolynomial (CellVars d e) ℚ)) P) =
    algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (rename (targetEmbedding p R T) P) :=
  renameInjFraction_algebraMap (targetEmbedding p R T) (targetEmbedding p R T).injective P

lemma targetEmbedding_left_kernel (a : I → I → ℕ)
    {d₁ e₁ d₂ e₂ : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization (d₁+e₁) (left p))
    (T : Realization (d₂+e₂) (right p)) (u : Cut d₁ e₁) :
    renameInjFraction (targetEmbedding p R T) (targetEmbedding p R T).injective
      (renameInjFraction Sum.inl Sum.inl_injective (cutKernel a u)) =
      kernel (pairKernel a) (left (cutRealizationEquiv R u).val)
        (right (cutRealizationEquiv R u).val) := by
  have hpoly (P : MvPolynomial (Σ i, Fin (d₁ i + e₁ i)) ℚ) :
    renameInjFraction (targetEmbedding p R T) (targetEmbedding p R T).injective
      (renameInjFraction (Sum.inl : (Σ i, Fin (d₁ i + e₁ i)) → CellVars (d₁+e₁) (d₂+e₂)) Sum.inl_injective
        (algebraMap _ (FractionRing (MvPolynomial (Σ i, Fin (d₁ i + e₁ i)) ℚ)) P)) =
    algebraMap _ (FractionRing (MvPolynomial (Σ i,A i) ℚ)) (rename (realizationMap R) P) := by
    have h₁ := renameInjFraction_algebraMap
      (Sum.inl : (Σ i, Fin (d₁ i + e₁ i)) → CellVars (d₁+e₁) (d₂+e₂)) Sum.inl_injective P
    have h₂ := renameInjFraction_algebraMap (targetEmbedding p R T) (targetEmbedding p R T).injective
      (rename (Sum.inl : (Σ i, Fin (d₁ i + e₁ i)) → CellVars (d₁+e₁) (d₂+e₂)) P)
    calc
      _ = _ := congrArg (renameInjFraction (targetEmbedding p R T) (targetEmbedding p R T).injective) h₁
      _ = _ := h₂
      _ = _ := by rw [rename_rename]; rfl
  simp only [cutKernel,map_div₀,hpoly]
  rw [mapped_cut_kernel]

lemma targetEmbedding_right_kernel (a : I → I → ℕ)
    {d₁ e₁ d₂ e₂ : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization (d₁+e₁) (left p))
    (T : Realization (d₂+e₂) (right p)) (v : Cut d₂ e₂) :
    renameInjFraction (targetEmbedding p R T) (targetEmbedding p R T).injective
      (renameInjFraction Sum.inr Sum.inr_injective (cutKernel a v)) =
      kernel (pairKernel a) (left (cutRealizationEquiv T v).val)
        (right (cutRealizationEquiv T v).val) := by
  have hpoly (P : MvPolynomial (Σ i, Fin (d₂ i + e₂ i)) ℚ) :
    renameInjFraction (targetEmbedding p R T) (targetEmbedding p R T).injective
      (renameInjFraction (Sum.inr : (Σ i, Fin (d₂ i + e₂ i)) → CellVars (d₁+e₁) (d₂+e₂)) Sum.inr_injective
        (algebraMap _ (FractionRing (MvPolynomial (Σ i, Fin (d₂ i + e₂ i)) ℚ)) P)) =
    algebraMap _ (FractionRing (MvPolynomial (Σ i,A i) ℚ)) (rename (realizationMap T) P) := by
    have h₁ := renameInjFraction_algebraMap
      (Sum.inr : (Σ i, Fin (d₂ i + e₂ i)) → CellVars (d₁+e₁) (d₂+e₂)) Sum.inr_injective P
    have h₂ := targetEmbedding_algebraMap p R T
      (rename (Sum.inr : (Σ i, Fin (d₂ i + e₂ i)) → CellVars (d₁+e₁) (d₂+e₂)) P)
    calc
      _ = _ := congrArg (renameInjFraction (targetEmbedding p R T) (targetEmbedding p R T).injective) h₁
      _ = _ := h₂
      _ = _ := by rw [rename_rename]; rfl
  simp only [cutKernel,map_div₀,hpoly]
  rw [mapped_cut_kernel]

lemma grid_shape_transfer [∀ i,Fintype (A i)] (a : I → I → ℕ)
    {d e : I → ℕ} (f : S d) (g : S e)
    {d₁ e₁ d₂ e₂ : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization (d₁+e₁) (left p))
    (T : Realization (d₂+e₂) (right p)) :
    (∑ q : SizedCut d₁ (left p),∑ r : SizedCut d₂ (right p),
      algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (gridPolynomial a f g p q.val r.val) *
        kernel (pairKernel a) (left q.val) (right q.val) *
        kernel (pairKernel a) (left r.val) (right r.val)) =
    renameInjFraction (targetEmbedding p R T) (targetEmbedding p R T).injective
      (localizeTensor (d₁+e₁) (d₂+e₂)
        (cellTransfer a d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂))) := by
  rw [← fourGridPolynomial_transfer,doubleTensorShuffle]
  simp only [LinearMap.coe_mk,AddHom.coe_mk,map_sum,map_mul,
    targetEmbedding_left_kernel,targetEmbedding_right_kernel]
  rw [← (cutRealizationEquiv R).sum_comp]
  apply Finset.sum_congr rfl
  intro u hu
  rw [← (cutRealizationEquiv T).sum_comp]
  apply Finset.sum_congr rfl
  intro v hv
  apply congrArg (fun z => z *
    kernel (pairKernel a) (left (cutRealizationEquiv R u).val) (right (cutRealizationEquiv R u).val) *
    kernel (pairKernel a) (left (cutRealizationEquiv T v).val) (right (cutRealizationEquiv T v).val))
  symm
  calc
    _ = _ := renameInjFraction_algebraMap (targetEmbedding p R T) (targetEmbedding p R T).injective _
    _ = _ := congrArg (algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)))
      (gridPolynomial_four_realization a f g p R T u v)

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,DecidableEq (A i)]

noncomputable def castTensor {d e d' e' : I → ℕ} (h : d=d') (k : e=e') :
    S d ⊗[ℚ] S e →ₗ[ℚ] S d' ⊗[ℚ] S e' := by
  subst d'
  subst e'
  exact LinearMap.id

lemma quotientTensor_cast_zero (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e d' e' : I → ℕ} (h : d=d') (k : e=e') (t : S d ⊗[ℚ] S e)
    (ht : quotientTensor a μ d e t = 0) :
    quotientTensor a μ d' e' (castTensor h k t) = 0 := by
  subst d'
  subst e'
  exact ht

noncomputable def targetValueAt {d e : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization d (left p)) (T : Realization e (right p)) :
    S d ⊗[ℚ] S e →+ FractionRing (MvPolynomial (Σi,A i) ℚ) where
  toFun t := renameInjFraction (targetEmbedding p R T) (targetEmbedding p R T).injective
    (localizeTensor d e t)
  map_zero' := by rw [map_zero,map_zero]
  map_add' := by intro f g; rw [map_add,map_add]

omit [Fintype I] [DecidableEq I] in
@[simp] lemma targetValueAt_apply {d e : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization d (left p)) (T : Realization e (right p))
    (f : S d ⊗[ℚ] S e) :
    targetValueAt p R T f = renameInjFraction (targetEmbedding p R T) (targetEmbedding p R T).injective
      (localizeTensor d e f) := rfl

lemma targetValueAt_injective {d e : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization d (left p)) (T : Realization e (right p)) :
    Function.Injective (targetValueAt p R T) :=
  (renameInjFraction (targetEmbedding p R T) (targetEmbedding p R T).injective).injective.comp
    (localizeTensor_injective d e)

omit [DecidableEq I] in
lemma targetValueAt_tmul {d e : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization d (left p)) (T : Realization e (right p))
    (f : S d) (g : S e) :
    targetValueAt p R T (f ⊗ₜ[ℚ] g) = labeledValue f (left p) * labeledValue g (right p) := by
  rw [labeledValue_eq R,labeledValue_eq T]
  simp only [targetValueAt_apply,LinearMap.coe_mk,AddHom.coe_mk,localizeTensor,tensorValue_tmul,
    targetEmbedding_algebraMap,map_mul,rename_rename,valueAt]
  rfl

omit [DecidableEq I] in
lemma targetValueAt_independent {d e : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R R' : Realization d (left p)) (T T' : Realization e (right p)) :
    targetValueAt p R T = targetValueAt p R' T' := by
  apply AddMonoidHom.ext
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul f g => rw [targetValueAt_tmul,targetValueAt_tmul]
  | add f g hf hg => simp only [map_add,hf,hg]

omit [DecidableEq I] in
lemma targetValueAt_cast {d e d' e' : I → ℕ} (h : d=d') (k : e=e') {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization d (left p)) (R' : Realization d' (left p))
    (T : Realization e (right p)) (T' : Realization e' (right p)) (t : S d ⊗[ℚ] S e) :
    targetValueAt p R' T' (castTensor h k t) = targetValueAt p R T t := by
  subst d'
  subst e'
  rw [targetValueAt_independent p R' R T' T]
  rfl

omit [Fintype I] [DecidableEq I] in
lemma targetValueAt_mul {d e : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization d (left p)) (T : Realization e (right p))
    (f g : S d ⊗[ℚ] S e) :
    targetValueAt p R T (f*g) = targetValueAt p R T f * targetValueAt p R T g := by
  change renameInjFraction (targetEmbedding p R T) (targetEmbedding p R T).injective
    (algebraMap (MvPolynomial (CellVars d e) ℚ) (FractionRing (MvPolynomial (CellVars d e) ℚ))
      (tensorValue d e (f*g))) = _
  rw [tensorValue_mul,map_mul,map_mul]
  rfl

end ElementaryPositivity.RawShuffle

end

end OAI
