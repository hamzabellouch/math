import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.TargetEmbedding

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)] in
lemma realization_card {d : I → ℕ} {s : Pack (A:=A)} (R : Realization d s) :
    (fun i=>(s i).card) = d := by
  funext i
  simpa using (Fintype.card_congr (R i)).symm

omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] in
lemma targetEmbedding_realization {d e : I → ℕ} {s : Pack (A:=A)}
    (R : Realization (d+e) s) (u : Cut d e) :
    targetEmbedding (cutRealizationEquiv R u).val (leftRealization R u) (rightRealization R u) =
      (cutSplit u).toEmbedding.trans
        (⟨realizationMap R, realizationMap_injective R⟩ : (Σi,Fin ((d+e) i)) ↪ (Σi,A i)) := by
  apply Function.Embedding.ext
  intro z
  rcases z with x|x <;> rfl

omit [∀ i,Fintype (A i)] in
lemma targetValueAt_restrictTensor {d e : I → ℕ} {s : Pack (A:=A)}
    (R : Realization (d+e) s) (u : Cut d e) (f : S (d+e)) :
    targetValueAt (cutRealizationEquiv R u).val (leftRealization R u) (rightRealization R u)
      (restrictTensor u f) = labeledValue f s := by
  rw [labeledValue_eq R]
  change renameInjFraction
    (targetEmbedding (cutRealizationEquiv R u).val (leftRealization R u) (rightRealization R u))
    (targetEmbedding (cutRealizationEquiv R u).val (leftRealization R u) (rightRealization R u)).injective
    (algebraMap (MvPolynomial (CellVars d e) ℚ) (FractionRing (MvPolynomial (CellVars d e) ℚ))
      (tensorValue d e (restrictTensor u f))) = _
  rw [tensorValue_restrictTensor,targetEmbedding_algebraMap]
  simp only [rename_rename,targetEmbedding_realization,Function.Embedding.coe_trans,
    Equiv.coe_toEmbedding]
  change algebraMap _ _ (rename ((realizationMap R ∘ cutSplit u) ∘ (cutSplit u).symm) f.val) = _
  have hfun : (realizationMap R ∘ cutSplit u) ∘ (cutSplit u).symm = realizationMap R := by
    funext x
    simp
  rw [hfun]
  rfl

noncomputable def gridShapeTensor (a : I → I → ℕ) {d e α β : I → ℕ}
    (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (u : CutShape (left p)) (v : CutShape (right p)) : S α ⊗[ℚ] S β :=
  castTensor ((shape_add_complement u).trans (realization_card R))
    ((shape_add_complement v).trans (realization_card T))
    (cellTransfer a (fun i=>(u i).val) (shapeComplement u)
      (fun i=>(v i).val) (shapeComplement v)
      (fourGridPolynomial a f g (fun i=>(u i).val) (shapeComplement u)
        (fun i=>(v i).val) (shapeComplement v)))

lemma targetValueAt_gridShapeTensor (a : I → I → ℕ) {d e α β : I → ℕ}
    (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (u : CutShape (left p)) (v : CutShape (right p)) :
    targetValueAt p R T (gridShapeTensor a f g p R T u v) =
      ∑ q : SizedCut (fun i=>(u i).val) (left p),
      ∑ r : SizedCut (fun i=>(v i).val) (right p),
        algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (gridPolynomial a f g p q.val r.val) *
          kernel (pairKernel a) (left q.val) (right q.val) *
          kernel (pairKernel a) (left r.val) (right r.val) := by
  rw [gridShapeTensor,targetValueAt_cast _ _ p (shapeRealization u) R (shapeRealization v) T]
  exact (grid_shape_transfer a f g p (shapeRealization u) (shapeRealization v)).symm

noncomputable def gridTensor (a : I → I → ℕ) {d e α β : I → ℕ}
    (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p)) : S α ⊗[ℚ] S β :=
  ∑ u : CutShape (left p),∑ v : CutShape (right p),gridShapeTensor a f g p R T u v

lemma targetValueAt_gridTensor (a : I → I → ℕ) {d e α β : I → ℕ}
    (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p)) :
    targetValueAt p R T (gridTensor a f g p R T) =
      algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (sameDen (left p) (right p)) *
        labeledValue (shufflePolynomial a f g) s := by
  rw [labeledValue_shuffle]
  have hf : labeledValue (A:=A) f = fun t=>algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (labeledPolynomial f t) := by
    funext t; exact (labeledPolynomial_algebraMap f t).symm
  have hg : labeledValue (A:=A) g = fun t=>algebraMap _ (FractionRing (MvPolynomial (Σi,A i) ℚ)) (labeledPolynomial g t) := by
    funext t; exact (labeledPolynomial_algebraMap g t).symm
  rw [hf,hg,shuffle_grid_cleared, sum_grid_by_shape p]
  simp only [gridTensor,map_sum,targetValueAt_gridShapeTensor,gridPolynomial]

end ElementaryPositivity.RawShuffle

end

end OAI
