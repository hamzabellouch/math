import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.CrossDifference
import OAI.Combinatorics.Chromatic.Shuffle.GridShapeTensor
import OAI.Combinatorics.Chromatic.Walls.Mass

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
open ElementaryPositivity.SlopeArithmetic
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

omit [Fintype I] [DecidableEq I] in
lemma canonical_source_card (d₁ e₁ d₂ e₂ : I → ℕ) (i : I) :
    ((left (canonicalLeftCut d₁ e₁ d₂ e₂) i) ∪
      (left (canonicalRightCut d₁ e₁ d₂ e₂) i)).card = d₁ i + d₂ i := by
  have hd : Disjoint (left (canonicalLeftCut d₁ e₁ d₂ e₂) i)
      (left (canonicalRightCut d₁ e₁ d₂ e₂) i) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    rcases x with (x|x) <;>
      simp [canonicalLeftCut,canonicalRightCut,sumPackCut,embedPackCut,left] at hx hy
  rw [Finset.card_union_of_disjoint hd]
  simp [canonicalLeftCut,canonicalRightCut,sumPackCut,embedPackCut,left]

lemma fourGridPolynomial_zero_of_source_mismatch (a : I → I → ℕ) {d e : I → ℕ}
    (f : S d) (g : S e) (d₁ e₁ d₂ e₂ : I → ℕ) (hd : d₁+d₂ ≠ d) :
    fourGridPolynomial a f g d₁ e₁ d₂ e₂ = 0 := by
  have hf : labeledPolynomial f (fun i=>left (canonicalLeftCut d₁ e₁ d₂ e₂) i ∪
      left (canonicalRightCut d₁ e₁ d₂ e₂) i) = 0 := by
    apply dite_eq_right
    intro h
    apply hd
    funext i
    exact (canonical_source_card d₁ e₁ d₂ e₂ i).symm.trans (h i)
  simp [fourGridPolynomial,canonicalGridPolynomial,gridPolynomial,hf]

omit [∀ i,Fintype (A i)] in
lemma quotient_gridShapeTensor_zero (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e α β : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (u : CutShape (left p)) (v : CutShape (right p)) (hd : d≠0)
    (hα : slope c η α = slope c η β) (hμ : slope c η d > slope c η α) :
    quotientTensor a (slope c η) α β (gridShapeTensor a f g p R T u v) = 0 := by
  unfold gridShapeTensor
  apply quotientTensor_cast_zero
  by_cases hsum : (fun i=>(u i).val) + (fun i=>(v i).val) = d
  · apply quotient_cellTransfer_zero
    apply destabilized_target c η hc
    · rw [(shape_add_complement u).trans (realization_card R),
        (shape_add_complement v).trans (realization_card T)]
      exact hα
    · rw [hsum]; exact hd
    · rw [hsum,(shape_add_complement u).trans (realization_card R)]
      exact hμ
  · rw [fourGridPolynomial_zero_of_source_mismatch a f g _ _ _ _ hsum,map_zero,map_zero]

omit [∀ i,Fintype (A i)] in
lemma quotient_gridTensor_zero (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e α β : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p)) (hd : d≠0)
    (hα : slope c η α = slope c η β) (hμ : slope c η d > slope c η α) :
    quotientTensor a (slope c η) α β (gridTensor a f g p R T) = 0 := by
  simp only [gridTensor,map_sum]
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro v hv
  exact quotient_gridShapeTensor_zero a c η hc f g p R T u v hd hα hμ

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

noncomputable def crossSign (d e : I → ℕ) : ℚ :=
  ∏ i, ∏ _ : Fin (d i), ∏ _ : Fin (e i), (-1:ℚ)

omit [DecidableEq I] [∀ i,Fintype (A i)] in
lemma sameDen_realization {d e : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization d (left p)) (T : Realization e (right p)) :
    sameDen (left p) (right p) =
    ∏ i,∏ x : Fin (d i), ∏ y : Fin (e i),
      (X (realizationMap T ⟨i,y⟩) - X (realizationMap R ⟨i,x⟩)) := by
  unfold sameDen
  apply Finset.prod_congr rfl
  intro i hi
  rw [← PackEnumeration.map_univ (R i),← PackEnumeration.map_univ (T i)]
  simp only [Finset.prod_map,diagonal,realizationMap]
  rfl

omit [DecidableEq I] [∀ i,Fintype (A i)] in
lemma targetEmbedding_crossDifference {d e : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization d (left p)) (T : Realization e (right p)) :
    rename (targetEmbedding p R T) (crossDifference d e) =
      C (crossSign d e) * sameDen (left p) (right p) := by
  rw [sameDen_realization p R T]
  simp only [crossDifference,map_prod,map_sub,rename_X,crossSign,map_neg,map_one]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro x hx
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro y hy
  change X (realizationMap R ⟨i,x⟩) - X (realizationMap T ⟨i,y⟩) =
    -1 * (X (realizationMap T ⟨i,y⟩) - X (realizationMap R ⟨i,x⟩))
  ring

omit [∀ i,Fintype (A i)] in
lemma targetValueAt_crossTensor {d e : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization d (left p)) (T : Realization e (right p)) :
    targetValueAt p R T (crossTensor d e) = crossSign d e •
      algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (sameDen (left p) (right p)) := by
  change renameInjFraction (targetEmbedding p R T) (targetEmbedding p R T).injective
    (algebraMap (MvPolynomial (CellVars d e) ℚ) (FractionRing (MvPolynomial (CellVars d e) ℚ))
      (tensorValue d e (crossTensor d e))) = _
  rw [tensorValue_crossTensor]
  have hh := targetEmbedding_algebraMap p R T (crossDifference d e)
  calc
    _ = _ := hh
    _ = _ := by
      rw [targetEmbedding_crossDifference, ← smul_eq_C_mul]
      exact map_rat_smul (algebraMap (MvPolynomial (Σi,A i) ℚ)
        (FractionRing (MvPolynomial (Σi,A i) ℚ))).toAddMonoidHom _ _

omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] in
lemma targetValueAt_smul {d e : I → ℕ} {s : Pack (A:=A)}
    (p : PackConvolution.Cut s) (R : Realization d (left p)) (T : Realization e (right p))
    (r : ℚ) (t : S d ⊗[ℚ] S e) :
    targetValueAt p R T (r • t) = r • targetValueAt p R T t :=
  map_rat_smul (targetValueAt p R T) r t

lemma cleared_restrictTensor (a : I → I → ℕ) {d e α β : I → ℕ} (h : d+e=α+β)
    (f : S d) (g : S e) {s : Pack (A:=A)} (R : Realization (α+β) s) (u : Cut α β) :
    crossTensor α β * restrictTensor u (castS h (shufflePolynomial a f g)) =
      crossSign α β • gridTensor a f g (cutRealizationEquiv R u).val
        (leftRealization R u) (rightRealization R u) := by
  apply targetValueAt_injective (cutRealizationEquiv R u).val (leftRealization R u) (rightRealization R u)
  rw [targetValueAt_mul,targetValueAt_crossTensor,targetValueAt_restrictTensor,
    targetValueAt_smul,targetValueAt_gridTensor,labeledValue_cast]
  exact smul_mul_assoc _ _ _

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def relativeTaylorB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    B a μ d ⊗[ℚ] B a μ e →ₐ[ℚ] Polynomial (B a μ d ⊗[ℚ] B a μ e) :=
  let L : B a μ d →ₐ[ℚ] Polynomial (B a μ d ⊗[ℚ] B a μ e) :=
    (Polynomial.mapAlgHom (Algebra.TensorProduct.includeLeft : B a μ d →ₐ[ℚ] B a μ d ⊗[ℚ] B a μ e)).comp (taylorB a μ d)
  let R : B a μ e →ₐ[ℚ] Polynomial (B a μ d ⊗[ℚ] B a μ e) :=
    Polynomial.CAlgHom.comp (Algebra.TensorProduct.includeRight : B a μ e →ₐ[ℚ] B a μ d ⊗[ℚ] B a μ e)
  Algebra.TensorProduct.lift (S:=ℚ) L R (fun x y => mul_comm (L x) (R y))

@[simp] lemma relativeTaylorB_tmul (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (f : B a μ d) (g : B a μ e) :
    relativeTaylorB a μ d e (f ⊗ₜ[ℚ] g) =
      Polynomial.map (Algebra.TensorProduct.includeLeft : B a μ d →ₐ[ℚ] B a μ d ⊗[ℚ] B a μ e).toRingHom (taylorB a μ d f) *
      Polynomial.C ((1 : B a μ d) ⊗ₜ[ℚ] g) := by
  simp only [relativeTaylorB]
  rfl

lemma quotientTensor_tmul (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (f : S d) (g : S e) :
    quotientTensor a μ d e (f ⊗ₜ[ℚ] g) = quotientAlg a μ d f ⊗ₜ[ℚ] quotientAlg a μ e g := rfl

lemma relativeTaylor_quotient (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (t : S d ⊗[ℚ] S e) :
    Polynomial.map (quotientTensor a μ d e).toRingHom (relativeTaylor d e t) =
      relativeTaylorB a μ d e (quotientTensor a μ d e t) := by
  induction t using TensorProduct.inductionOn with
  | tmul f g =>
    rw [relativeTaylor_tmul,quotientTensor_tmul,relativeTaylorB_tmul,taylorB_mk,
      Polynomial.map_mul,Polynomial.map_C]
    have hr : (quotientTensor a μ d e).toRingHom (1 ⊗ₜ[ℚ] g) = 1 ⊗ₜ[ℚ] quotientAlg a μ e g := by
      change quotientAlg a μ d 1 ⊗ₜ[ℚ] quotientAlg a μ e g = _
      rw [map_one]
    rw [hr]
    congr 1
    rw [Polynomial.map_map,Polynomial.map_map]
    congr 1
  | add f g hf hg => simp only [map_add,Polynomial.map_add,hf,hg]

lemma quotient_relativeTaylor_zero (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (t : S d ⊗[ℚ] S e) (h : quotientTensor a μ d e t = 0) :
    Polynomial.map (quotientTensor a μ d e).toRingHom (relativeTaylor d e t) = 0 := by
  rw [relativeTaylor_quotient,h,map_zero]

lemma quotient_crossTensor_cancel (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (t : S d ⊗[ℚ] S e) (h : quotientTensor a μ d e (crossTensor d e * t) = 0) :
    quotientTensor a μ d e t = 0 := by
  have ht := quotient_relativeTaylor_zero a μ d e (crossTensor d e * t) h
  rw [map_mul,Polynomial.map_mul] at ht
  have hz : Polynomial.map (quotientTensor a μ d e).toRingHom (relativeTaylor d e t) = 0 :=
    (crossClearing_cancel a μ d e _).mp ht
  have he := congrArg (fun p : Polynomial (B a μ d ⊗[ℚ] B a μ e) => p.eval 0) hz
  rw [← show algebraMap ℚ (B a μ d ⊗[ℚ] B a μ e) 0 = 0 from map_zero _] at he
  rw [eval_map_rat,relativeTaylor_eval] at he
  have htr : TensorProduct.map (translationS d 0) (LinearMap.id : S e →ₗ[ℚ] S e) t = t := by
    clear h ht hz he
    induction t using TensorProduct.inductionOn with
    | tmul f g => simp [translationS]
    | add f g hf hg => simp only [map_add,hf,hg]
  simpa only [htr,Polynomial.eval_zero,Polynomial.coeff_zero] using he

end ElementaryPositivity.RawShuffle

end

end OAI
