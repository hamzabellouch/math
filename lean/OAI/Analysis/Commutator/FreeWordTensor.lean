import Mathlib
import OAI.Analysis.Commutator.FreeMoments

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

namespace Kadison.FreeWordTensor

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

structure FaithfulState (A : Type) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] where
  functional : A →ₚ[ℂ] ℂ
  normalized : functional 1 = 1
  faithful : ∀ a : A, functional (star a * a) = 0 → a = 0

variable (t : FaithfulState A)

abbrev preSpace := t.functional.PreGNS

noncomputable instance faithfulNormed : NormedAddCommGroup (preSpace t) :=
  NormedAddCommGroup.ofSeparation fun x hx => by
    apply t.functional.ofPreGNS.injective
    change t.functional.ofPreGNS x = 0
    apply t.faithful
    have hs := t.functional.preGNS_norm_sq x
    rw [hx] at hs
    simpa using hs.symm

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A)

def letterSpace (i : ι) : Submodule ℂ (preSpace t) where
  carrier := {x | t.functional.ofPreGNS x ∈ S i ∧ t.functional (t.functional.ofPreGNS x) = 0}
  zero_mem' := by simp
  add_mem' := by rintro x y ⟨hx, hx0⟩ ⟨hy, hy0⟩; simp [map_add, add_mem hx hy, hx0, hy0]
  smul_mem' := by
    rintro c x ⟨hx, hx0⟩
    exact ⟨by simpa using SMulMemClass.smul_mem c hx, by simp [hx0]⟩

def letterValue (i : ι) : letterSpace t S i →ₗ[ℂ] A :=
  t.functional.ofPreGNS.toLinearMap.comp (letterSpace t S i).subtype

def asLetter (i : ι) (x : letterSpace t S i) : FreeMoments.Letter S t.functional.toLinearMap where
  color := i
  val := letterValue t S i x
  mem := x.property.1
  centered := x.property.2

structure Space where
  carrier : Type
  [normed : NormedAddCommGroup carrier]
  [inner : InnerProductSpace ℂ carrier]

attribute [instance] Space.normed Space.inner

instance : CoeSort Space Type := ⟨Space.carrier⟩

@[reducible] noncomputable def tensor : List ι → Space
  | [] => ⟨ℂ⟩
  | i :: is => ⟨letterSpace t S i ⊗[ℂ] tensor is⟩

@[reducible] def Params : List ι → Type
  | [] => PUnit
  | i :: is => letterSpace t S i × Params is

noncomputable def pure : ∀ is, Params t S is → tensor t S is
  | [], _ => (1 : ℂ)
  | _ :: is, x => x.1 ⊗ₜ[ℂ] pure is x.2

def letters : ∀ is, Params t S is → List (FreeMoments.Letter S t.functional.toLinearMap)
  | [], _ => []
  | i :: is, x => asLetter t S i x.1 :: letters is x.2

@[simp] lemma letters_colors : ∀ is (x : Params t S is),
    (letters t S is x).map FreeMoments.Letter.color = is
  | [], _ => rfl
  | _ :: is, x => by simp [letters, asLetter, letters_colors is x.2]

lemma letters_reduced (is : List ι) (x : Params t S is) (his : is.IsChain (· ≠ ·)) :
    FreeMoments.Reduced (letters t S is x) := by
  rw [← letters_colors t S is x] at his
  exact (List.isChain_map _).mp his

noncomputable def read : ∀ is, tensor t S is →ₗ[ℂ] A
  | [] => Algebra.linearMap ℂ A
  | i :: is => (TensorProduct.lift (LinearMap.mul ℂ A)).comp
      (TensorProduct.map (letterValue t S i) (read is))

@[simp] lemma read_pure : ∀ is (x : Params t S is),
    read t S is (pure t S is x) = FreeMoments.word (letters t S is x)
  | [], _ => by
    change algebraMap ℂ A 1 = 1
    exact map_one _
  | i :: is, x => by
    change letterValue t S i x.1 * read t S is (pure t S is x.2) =
      letterValue t S i x.1 * FreeMoments.word (letters t S is x.2)
    rw [read_pure is x.2]

lemma span_pure (is : List ι) :
    Submodule.span ℂ (Set.range (pure t S is)) = ⊤ := by
  induction is with
  | nil =>
    apply Submodule.eq_top_iff'.mpr
    intro z
    have h : (1 : ℂ) ∈ Submodule.span ℂ (Set.range (pure t S [])) :=
      Submodule.subset_span ⟨PUnit.unit, rfl⟩
    simpa using (Submodule.span ℂ (Set.range (pure t S []))).smul_mem z h
  | cons i is ih =>
    apply Submodule.eq_top_iff'.mpr
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | tmul x y =>
      have hy : y ∈ Submodule.span ℂ (Set.range (pure t S is)) := by rw [ih]; trivial
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨v, rfl⟩ := hy
        exact Submodule.subset_span ⟨(x,v), rfl⟩
      | zero => simp only [TensorProduct.tmul_zero, Submodule.zero_mem]
      | add y z _ _ hy hz =>
        simpa only [TensorProduct.tmul_add] using
          (Submodule.span ℂ (Set.range (pure t S (i::is)))).add_mem hy hz
      | smul c y _ hy =>
        simpa only [TensorProduct.tmul_smul] using
          (Submodule.span ℂ (Set.range (pure t S (i::is)))).smul_mem c hy

lemma inner_letter (i : ι) (x y : letterSpace t S i) :
    inner ℂ x y = t.functional (star (letterValue t S i x) * letterValue t S i y) := by
  rfl

lemma inner_pure : ∀ is (x y : Params t S is),
    inner ℂ (pure t S is x) (pure t S is y) =
      FreeMoments.gram (letters t S is x) (letters t S is y)
  | [], _, _ => by simp [pure, letters, FreeMoments.gram]
  | i :: is, x, y => by
    change inner ℂ (x.1 ⊗ₜ[ℂ] pure t S is x.2) (y.1 ⊗ₜ[ℂ] pure t S is y.2) = _
    rw [TensorProduct.inner_tmul, inner_pure is x.2 y.2, inner_letter]
    simp [FreeMoments.gram, letters, asLetter]

noncomputable def readPre (is : List ι) : tensor t S is →ₗ[ℂ] preSpace t :=
  t.functional.toPreGNS.toLinearMap.comp (read t S is)

@[simp] lemma readPre_pure (is : List ι) (x : Params t S is) :
    readPre t S is (pure t S is x) =
      t.functional.toPreGNS (FreeMoments.word (letters t S is x)) := by
  change t.functional.toPreGNS (read t S is (pure t S is x)) = _
  rw [read_pure]

variable (hfree : FreeMoments.Free S t.functional.toLinearMap)

include hfree

lemma inner_readPre_pure (is : List ι) (his : is.IsChain (· ≠ ·))
    (x y : Params t S is) :
    inner ℂ (readPre t S is (pure t S is x)) (readPre t S is (pure t S is y)) =
      inner ℂ (pure t S is x) (pure t S is y) := by
  rw [readPre_pure, readPre_pure, inner_pure]
  exact FreeMoments.gram_word (fun a => map_star t.functional a) t.normalized hfree _ _
    (letters_reduced t S is x his) (letters_reduced t S is y his)

lemma inner_readPre (is : List ι) (his : is.IsChain (· ≠ ·))
    (x y : tensor t S is) :
    inner ℂ (readPre t S is x) (readPre t S is y) = inner ℂ x y := by
  have hx : x ∈ Submodule.span ℂ (Set.range (pure t S is)) := by rw [span_pure]; trivial
  have hy : y ∈ Submodule.span ℂ (Set.range (pure t S is)) := by rw [span_pure]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      exact inner_readPre_pure t S hfree is his v w
    | zero => simp
    | add y z _ _ hy hz => simp only [map_add, inner_add_right, hy, hz]
    | smul c y _ hy => simp only [map_smul, inner_smul_right, hy]
  | zero => simp
  | add x z _ _ hx hz => simp only [map_add, inner_add_left, hx, hz]
  | smul c x _ hx => simp only [map_smul, inner_smul_left, hx]

noncomputable def readIsometry (is : List ι) (his : is.IsChain (· ≠ ·)) :
    tensor t S is →ₗᵢ[ℂ] preSpace t :=
  (readPre t S is).isometryOfInner (inner_readPre t S hfree is his)

noncomputable def wordEmbedding (is : List ι) (his : is.IsChain (· ≠ ·)) :
    Completion (tensor t S is) →ₗᵢ[ℂ] t.functional.GNS where
  toLinearMap := (readIsometry t S hfree is his).toContinuousLinearMap.completion.toLinearMap
  norm_map' x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x => simp

@[simp] lemma wordEmbedding_coe (is : List ι) (his : is.IsChain (· ≠ ·))
    (x : tensor t S is) :
    wordEmbedding t S hfree is his (x : Completion (tensor t S is)) =
      (readPre t S is x : t.functional.GNS) := by
  change (readIsometry t S hfree is his).toContinuousLinearMap.completion _ = _
  simp [readIsometry]

lemma inner_readPre_pure_ne (is js : List ι)
    (his : is.IsChain (· ≠ ·)) (hjs : js.IsChain (· ≠ ·)) (hne : is ≠ js)
    (x : Params t S is) (y : Params t S js) :
    inner ℂ (readPre t S is (pure t S is x)) (readPre t S js (pure t S js y)) = 0 := by
  rw [readPre_pure, readPre_pure]
  change t.functional.toLinearMap (star (FreeMoments.word (letters t S is x)) *
    FreeMoments.word (letters t S js y)) = 0
  rw [FreeMoments.gram_word (fun a => map_star t.functional a) t.normalized hfree _ _
    (letters_reduced t S is x his) (letters_reduced t S js y hjs)]
  apply FreeMoments.gram_zero_of_colors_ne
  simpa only [letters_colors] using hne

lemma inner_readPre_ne (is js : List ι)
    (his : is.IsChain (· ≠ ·)) (hjs : js.IsChain (· ≠ ·)) (hne : is ≠ js)
    (x : tensor t S is) (y : tensor t S js) :
    inner ℂ (readPre t S is x) (readPre t S js y) = 0 := by
  have hx : x ∈ Submodule.span ℂ (Set.range (pure t S is)) := by rw [span_pure]; trivial
  have hy : y ∈ Submodule.span ℂ (Set.range (pure t S js)) := by rw [span_pure]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      exact inner_readPre_pure_ne t S hfree is js his hjs hne v w
    | zero => simp
    | add y z _ _ hy hz => simp only [map_add, inner_add_right, hy, hz, add_zero]
    | smul c y _ hy => simp only [map_smul, inner_smul_right, hy, mul_zero]
  | zero => simp
  | add x z _ _ hx hz => simp only [map_add, inner_add_left, hx, hz, add_zero]
  | smul c x _ hx => simp only [map_smul, inner_smul_left, hx, mul_zero]

lemma wordEmbedding_orthogonal (is js : List ι)
    (his : is.IsChain (· ≠ ·)) (hjs : js.IsChain (· ≠ ·)) (hne : is ≠ js)
    (x : Completion (tensor t S is)) (y : Completion (tensor t S js)) :
    inner ℂ (wordEmbedding t S hfree is his x) (wordEmbedding t S hfree js hjs y) = 0 := by
  induction x, y using Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    rw [wordEmbedding_coe, wordEmbedding_coe, Completion.inner_coe]
    exact inner_readPre_ne t S hfree is js his hjs hne x y

def ColorSeq (ι : Type*) := {is : List ι // is.IsChain (· ≠ ·)}

abbrev wordSpace (is : ColorSeq ι) := Completion (tensor t S is.val)

noncomputable def wordInclusion (is : ColorSeq ι) : wordSpace t S is →ₗᵢ[ℂ] t.functional.GNS :=
  wordEmbedding t S hfree is.val is.property

lemma wordFamily_orthogonal :
    OrthogonalFamily ℂ (wordSpace t S) (wordInclusion t S hfree) := by
  intro is js hne x y
  exact wordEmbedding_orthogonal t S hfree is.val js.val is.property js.property
    (fun h => hne (Subtype.ext h)) x y

end Kadison.FreeWordTensor
end

end OAI
