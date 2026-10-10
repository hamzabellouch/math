import Mathlib
import OAI.Analysis.Commutator.BicommutantOrbit
import OAI.Analysis.Commutator.FreeWordTensor

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology

namespace Kadison.FreeWordTensor

open scoped InnerProductSpace _root_.Topology

open UniformSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

def boundedLetter (a : FreeMoments.Letter S t.functional.toLinearMap) :
    letterSpace t S a.color :=
  ⟨t.functional.toPreGNS a.val, by exact ⟨a.mem, a.centered⟩⟩

@[simp] lemma asLetter_boundedLetter (a : FreeMoments.Letter S t.functional.toLinearMap) :
    asLetter t S a.color (boundedLetter t S a) = a := by cases a; rfl

def paramsOfLetters : (w : List (FreeMoments.Letter S t.functional.toLinearMap)) →
    Params t S (w.map FreeMoments.Letter.color)
  | [] => PUnit.unit
  | a :: w => (boundedLetter t S a, paramsOfLetters w)

@[simp] lemma letters_paramsOfLetters :
    ∀ w : List (FreeMoments.Letter S t.functional.toLinearMap),
      letters t S (w.map FreeMoments.Letter.color) (paramsOfLetters t S w) = w
  | [] => rfl
  | a :: w => by
    change asLetter t S a.color (boundedLetter t S a) ::
      letters t S (w.map FreeMoments.Letter.color) (paramsOfLetters t S w) = a :: w
    rw [asLetter_boundedLetter, letters_paramsOfLetters w]

variable (hfree : FreeMoments.Free S t.functional.toLinearMap)

noncomputable def hilbertWordSpan : Submodule ℂ t.functional.GNS :=
  ⨆ is : ColorSeq ι, LinearMap.range (wordInclusion t S hfree is).toLinearMap

lemma bounded_word_mem (w : List (FreeMoments.Letter S t.functional.toLinearMap))
    (hw : FreeMoments.Reduced w) :
    (t.functional.toPreGNS (FreeMoments.word w) : t.functional.GNS) ∈
      hilbertWordSpan t S hfree := by
  let is : ColorSeq ι := ⟨w.map FreeMoments.Letter.color, (List.isChain_map _).mpr hw⟩
  apply Submodule.mem_iSup_of_mem is
  use (pure t S is.val (paramsOfLetters t S w) : wordSpace t S is)
  change wordEmbedding t S hfree is.val is.property _ = _
  rw [wordEmbedding_coe, readPre_pure]
  simp only [is, letters_paramsOfLetters]

lemma generated_mem_span {a : A} (ha : a ∈ iSup S) :
    (t.functional.toPreGNS a : t.functional.GNS) ∈ hilbertWordSpan t S hfree := by
  have ha' : a ∈ FreeMoments.wordSpan S t.functional.toLinearMap := by
    change a ∈ (FreeMoments.reducedAlgebra S (fun a => map_star t.functional a) t.normalized)
    rw [FreeMoments.reducedAlgebra_eq_iSup]
    exact ha
  clear ha
  induction ha' using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨w, hw, rfl⟩ := ha
    exact bounded_word_mem t S hfree w hw
  | zero => simp only [map_zero, Completion.coe_zero, Submodule.zero_mem]
  | add a b _ _ ha hb => simpa only [map_add, Completion.coe_add] using
      (hilbertWordSpan t S hfree).add_mem ha hb
  | smul c a _ ha => simpa only [map_smul, Completion.coe_smul] using
      (hilbertWordSpan t S hfree).smul_mem c ha

def generatedOperators : StarSubalgebra ℂ (t.functional.GNS →L[ℂ] t.functional.GNS) :=
  (iSup S).map t.functional.gnsStarAlgHom

lemma total_words_from_generation
    (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators t S : Set _))) :
    (hilbertWordSpan t S hfree).topologicalClosure = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  induction x using Completion.induction_on with
  | hp => exact (hilbertWordSpan t S hfree).isClosed_topologicalClosure
  | ih x =>
    let ξ : t.functional.GNS := (t.functional.toPreGNS 1 : t.functional.GNS)
    have h := Kadison.bicommutant_mem_cyclicSubspace (generatedOperators t S)
      (hgen (t.functional.ofPreGNS x)) ξ
    have heq : t.functional.gnsStarAlgHom (t.functional.ofPreGNS x) ξ =
        (x : t.functional.GNS) := by
      simp [ξ, PositiveLinearMap.gnsStarAlgHom]
    rw [heq] at h
    apply Submodule.topologicalClosure_mono ?_ h
    rintro y ⟨a, ha, rfl⟩
    obtain ⟨b, hb, rfl⟩ := ha
    simpa [ξ, PositiveLinearMap.gnsStarAlgHom] using generated_mem_span t S hfree hb

theorem isHilbertSum_of_generation
    (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators t S : Set _))) :
    IsHilbertSum ℂ (wordSpace t S) (wordInclusion t S hfree) := by
  apply IsHilbertSum.mk (wordFamily_orthogonal t S hfree)
  change ⊤ ≤ (hilbertWordSpan t S hfree).topologicalClosure
  rw [total_words_from_generation t S hfree hgen]

end Kadison.FreeWordTensor
end

end OAI
