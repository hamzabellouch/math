import Mathlib
import OAI.Analysis.Commutator.HilbertDiagonal
import OAI.Analysis.Commutator.TensorActions
import OAI.Analysis.Commutator.FreeWordDecomposition

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.FreeWordAction

open FreeWordTensor FreeMoments

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (α : ι → A ≃⋆ₐ[ℂ] A)
  (hmem : ∀ i a, a∈S i → α i a∈S i)
  (hτ : ∀ i a, t.functional (α i a)=t.functional a)

def letter (a : Letter S t.functional.toLinearMap) : Letter S t.functional.toLinearMap where
  color := a.color
  val := α a.color a.val
  mem := hmem _ _ a.mem
  centered := (hτ _ _).trans a.centered

@[simp] lemma letter_color (a : Letter S t.functional.toLinearMap) :
    (letter t S α hmem hτ a).color=a.color := rfl

@[simp] lemma letter_val (a : Letter S t.functional.toLinearMap) :
    (letter t S α hmem hτ a).val=α a.color a.val := rfl

lemma reduced_map {w : List (Letter S t.functional.toLinearMap)} (hw : Reduced w) :
    Reduced (w.map (letter t S α hmem hτ)) := (List.isChain_map _).mpr hw

def letterLinear (i : ι) : letterSpace t S i →ₗ[ℂ] letterSpace t S i where
  toFun x := ⟨t.functional.toPreGNS (α i (letterValue t S i x)),
    hmem _ _ x.property.1, by exact (hτ _ _).trans x.property.2⟩
  map_add' x y := by apply Subtype.ext; simp [map_add]
  map_smul' c x := by apply Subtype.ext; simp [map_smul]

lemma letterLinear_value (i : ι) (x : letterSpace t S i) :
    letterValue t S i (letterLinear t S α hmem hτ i x)=α i (letterValue t S i x) := rfl

lemma letterLinear_inner (i : ι) (x y : letterSpace t S i) :
    inner ℂ (letterLinear t S α hmem hτ i x) (letterLinear t S α hmem hτ i y)=inner ℂ x y := by
  rw [inner_letter,inner_letter,letterLinear_value,letterLinear_value,←map_star,←map_mul,hτ]

def letterIso (i : ι) : letterSpace t S i →ₗᵢ[ℂ] letterSpace t S i where
  toLinearMap := letterLinear t S α hmem hτ i
  norm_map' x := by
    rw [norm_eq_sqrt_re_inner (𝕜:=ℂ),norm_eq_sqrt_re_inner (𝕜:=ℂ),
      letterLinear_inner]

def tensorIso : ∀ is : List ι, tensor t S is →ₗᵢ[ℂ] tensor t S is
  | [] => LinearIsometry.id
  | i::is => TensorProduct.mapIsometry (letterIso t S α hmem hτ i) (tensorIso is)

def mapParams : ∀ is, Params t S is → Params t S is
  | [], _ => PUnit.unit
  | i::is, x => (letterIso t S α hmem hτ i x.1,mapParams is x.2)

lemma tensorIso_pure : ∀ is (x : Params t S is),
    tensorIso t S α hmem hτ is (pure t S is x)=pure t S is (mapParams t S α hmem hτ is x)
  | [], _ => rfl
  | i::is,x => by
      change (letterIso t S α hmem hτ i x.1) ⊗ₜ[ℂ]
        (tensorIso t S α hmem hτ is (pure t S is x.2)) = _
      rw [tensorIso_pure is x.2]
      rfl

lemma mapParams_letters : ∀ is (x : Params t S is),
    letters t S is (mapParams t S α hmem hτ is x)=
      (letters t S is x).map (letter t S α hmem hτ)
  | [], _ => rfl
  | i::is,x => by
      change asLetter t S i (letterIso t S α hmem hτ i x.1) :: _ = _ :: _
      congr 1
      exact mapParams_letters is x.2

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

def action : t.functional.GNS →ₗᵢ[ℂ] t.functional.GNS :=
  HilbertDiagonal.onSum (wordSpace t S) (wordInclusion t S hfree)
    (isHilbertSum_of_generation t S hfree hgen)
    (fun is => completionIsometry (tensorIso t S α hmem hτ is.val))

lemma action_word (w : List (Letter S t.functional.toLinearMap)) (hw : Reduced w) :
    action t S α hmem hτ hfree hgen (t.functional.toPreGNS (word w) : t.functional.GNS) =
      (t.functional.toPreGNS (word (w.map (letter t S α hmem hτ))) : t.functional.GNS) := by
  let is : ColorSeq ι := ⟨w.map Letter.color,(List.isChain_map _).mpr hw⟩
  have hv : (t.functional.toPreGNS (word w) : t.functional.GNS)=
      wordInclusion t S hfree is (pure t S is.val (paramsOfLetters t S w) : wordSpace t S is) := by
    change _=wordEmbedding t S hfree is.val is.property _
    rw [wordEmbedding_coe,readPre_pure]
    simp only [is,letters_paramsOfLetters]
  rw [hv]
  unfold action
  rw [HilbertDiagonal.onSum_insert,completionIsometry_coe,tensorIso_pure]
  change wordEmbedding t S hfree is.val is.property _ = _
  rw [wordEmbedding_coe,readPre_pure,mapParams_letters]
  simp only [is,letters_paramsOfLetters]

end Kadison.FreeWordAction

end

end
end

end OAI
