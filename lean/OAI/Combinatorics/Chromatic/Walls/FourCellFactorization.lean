import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.SumPackCut

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
open ElementaryPositivity.SeparatedSymmetry
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

def firstColumn (d₁ e₁ d₂ e₂ : I → ℕ) (i : I) :
    (Fin (d₁ i) ⊕ Fin (d₂ i)) ↪ FourPacks d₁ e₁ d₂ e₂ i :=
  Function.Embedding.sumMap Function.Embedding.inl Function.Embedding.inl

def secondColumn (d₁ e₁ d₂ e₂ : I → ℕ) (i : I) :
    (Fin (e₁ i) ⊕ Fin (e₂ i)) ↪ FourPacks d₁ e₁ d₂ e₂ i :=
  Function.Embedding.sumMap Function.Embedding.inr Function.Embedding.inr

omit [Fintype I] [DecidableEq I] in
lemma canonical_first_column (d₁ e₁ d₂ e₂ : I → ℕ) :
    (fun i=>left (canonicalLeftCut d₁ e₁ d₂ e₂) i ∪
      left (canonicalRightCut d₁ e₁ d₂ e₂) i) =
      embedPack (firstColumn d₁ e₁ d₂ e₂) (fun _=>Finset.univ) := by
  funext i
  ext x
  rcases x with ((x|x)|(x|x)) <;>
    simp [canonicalLeftCut,canonicalRightCut,left,embedPackCut,sumPackCut,
      embedPack,firstColumn,Finset.mem_map,Function.Embedding.sumMap]

omit [Fintype I] [DecidableEq I] in
lemma canonical_second_column (d₁ e₁ d₂ e₂ : I → ℕ) :
    (fun i=>right (canonicalLeftCut d₁ e₁ d₂ e₂) i ∪
      right (canonicalRightCut d₁ e₁ d₂ e₂) i) =
      embedPack (secondColumn d₁ e₁ d₂ e₂) (fun _=>Finset.univ) := by
  funext i
  ext x
  rcases x with ((x|x)|(x|x)) <;>
    simp [canonicalLeftCut,canonicalRightCut,right,embedPackCut,sumPackCut,
      embedPack,secondColumn,Finset.mem_map,Function.Embedding.sumMap]

noncomputable def cutUnivRealization {d e : I → ℕ} (A : Cut d e) :
    Realization (d+e) (A:=fun i=>Fin (d i) ⊕ Fin (e i)) (fun _=>Finset.univ) :=
  fun i=>(packSplit A i).symm.trans (Equiv.subtypeUnivEquiv (fun _=>Finset.mem_univ _)).symm

lemma labeledPolynomial_univ_restrict {d e : I → ℕ} (A : Cut d e) (f : S (d+e)) :
    labeledPolynomial (A:=fun i=>Fin (d i) ⊕ Fin (e i)) f (fun _=>Finset.univ) =
      rename (Equiv.sigmaSumDistrib _ _).symm (tensorValue d e (restrictTensor A f)) := by
  rw [labeledPolynomial_eq (cutUnivRealization A),tensorValue_restrictTensor,rename_rename]
  congr 2
  funext x
  obtain ⟨y,rfl⟩ := (cutSplit A).surjective x
  simp only [Function.comp_apply,Equiv.symm_apply_apply]
  cases y with
  | inl x =>
    change (⟨x.1, (packSplit A x.1).symm (packSplit A x.1 (.inl x.2))⟩ : Σi,Fin (d i) ⊕ Fin (e i))=_
    rw [Equiv.symm_apply_apply]
    rfl
  | inr x =>
    change (⟨x.1, (packSplit A x.1).symm (packSplit A x.1 (.inr x.2))⟩ : Σi,Fin (d i) ⊕ Fin (e i))=_
    rw [Equiv.symm_apply_apply]
    rfl

def firstColumnVars (d₁ e₁ d₂ e₂ : I → ℕ) :
    CellVars d₁ d₂ → CellVars d₁ e₁ ⊕ CellVars d₂ e₂
  | Sum.inl x => Sum.inl (Sum.inl x)
  | Sum.inr x => Sum.inr (Sum.inl x)

def secondColumnVars (d₁ e₁ d₂ e₂ : I → ℕ) :
    CellVars e₁ e₂ → CellVars d₁ e₁ ⊕ CellVars d₂ e₂
  | Sum.inl x => Sum.inl (Sum.inr x)
  | Sum.inr x => Sum.inr (Sum.inr x)

lemma fourGridPolynomial_factor (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (A : Cut d₁ d₂) (B : Cut e₁ e₂) (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
    fourGridPolynomial a f g d₁ e₁ d₂ e₂ =
      rename (firstColumnVars d₁ e₁ d₂ e₂) (tensorValue d₁ d₂ (restrictTensor A f)) *
      rename (secondColumnVars d₁ e₁ d₂ e₂) (tensorValue e₁ e₂ (restrictTensor B g)) *
      rename (fourPackEquiv d₁ e₁ d₂ e₂)
        (crossKernelPolynomial a (canonicalGridCut d₁ e₁ d₂ e₂)
          (canonicalLeftCut d₁ e₁ d₂ e₂) (canonicalRightCut d₁ e₁ d₂ e₂)) := by
  unfold fourGridPolynomial canonicalGridPolynomial gridPolynomial
  rw [canonical_first_column,canonical_second_column,←embed_labeledPolynomial,
    ←embed_labeledPolynomial,labeledPolynomial_univ_restrict A,labeledPolynomial_univ_restrict B]
  simp only [map_mul,rename_rename]
  congr 2
  · congr 2
    funext x
    cases x <;> rfl
  · congr 2
    funext x
    cases x <;> rfl

end ElementaryPositivity.RawShuffle

end

end OAI
