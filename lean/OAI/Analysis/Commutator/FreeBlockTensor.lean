import Mathlib
import OAI.Analysis.Commutator.FreeBlockWords2

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

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor FreeCreation UniformSpace

open scoped InnerProductSpace TensorProduct

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable {i j : ι}

def factorSpace (i : ι) : Submodule ℂ (preSpace t) where
  carrier := {x | t.functional.ofPreGNS x ∈ S i}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy; simpa using add_mem hx hy
  smul_mem' := by intro c x hx; simpa using SMulMemClass.smul_mem c hx

def factorValue (i : ι) : factorSpace t S i →ₗ[ℂ] A :=
  t.functional.ofPreGNS.toLinearMap.comp (factorSpace t S i).subtype

abbrev spaceTensor (E F : Space) : Space := ⟨E ⊗[ℂ] F⟩

@[reducible] def blockTensor (i j : ι) : ℕ → Space
  | 0 => ⟨factorSpace t S j⟩
  | n+1 => spaceTensor ⟨letterSpace t S j⟩ (spaceTensor ⟨letterSpace t S i⟩ (blockTensor i j n))

@[reducible] def BlockParams (i j : ι) : ℕ → Type
  | 0 => factorSpace t S j
  | n+1 => Letters t S i j × BlockParams i j n

def blockPure : ∀ n, BlockParams t S i j n → blockTensor t S i j n
  | 0, z => z
  | n+1, x => x.1.1 ⊗ₜ[ℂ] (x.1.2 ⊗ₜ[ℂ] blockPure n x.2)

def paramLetters : ∀ n, BlockParams t S i j n → List (Letters t S i j)
  | 0, _ => []
  | n+1, x => x.1 :: paramLetters n x.2

def paramEnd : ∀ n, BlockParams t S i j n → factorSpace t S j
  | 0, z => z
  | n+1, x => paramEnd n x.2

@[simp] lemma paramLetters_length : ∀ n (x : BlockParams t S i j n),
    (paramLetters t S n x).length=n
  | 0, _ => rfl
  | n+1, x => by simp [paramLetters, paramLetters_length n x.2]

def blockRead : ∀ n, blockTensor t S i j n →ₗ[ℂ] A
  | 0 => factorValue t S j
  | n+1 => (TensorProduct.lift (LinearMap.mul ℂ A)).comp
      (TensorProduct.map (letterValue t S j)
        ((TensorProduct.lift (LinearMap.mul ℂ A)).comp
          (TensorProduct.map (letterValue t S i) (blockRead n))))

@[simp] lemma blockRead_pure : ∀ n (x : BlockParams t S i j n),
    blockRead t S n (blockPure t S n x) =
      blockValue t S (paramLetters t S n x) (factorValue t S j (paramEnd t S n x))
  | 0, _ => rfl
  | n+1, x => by
    change letterValue t S j x.1.1 * (letterValue t S i x.1.2 *
      blockRead t S n (blockPure t S n x.2)) = _
    rw [blockRead_pure n x.2]
    rfl

lemma span_blockPure (n : ℕ) :
    Submodule.span ℂ (Set.range (blockPure t S (i := i) (j := j) n))=⊤ := by
  induction n with
  | zero => simp [blockPure]
  | succ n ih =>
    apply Submodule.eq_top_iff'.mpr
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | tmul a w =>
      induction w using TensorProduct.inductionOn with
      | add x y hx hy => simpa only [TensorProduct.tmul_add] using
          (Submodule.span ℂ (Set.range (blockPure t S (i := i) (j := j) (n+1)))).add_mem hx hy
      | tmul d w =>
        have hw : w ∈ Submodule.span ℂ (Set.range (blockPure t S (i := i) (j := j) n)) := by rw [ih]; trivial
        induction hw using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨v,rfl⟩ := hw
          exact Submodule.subset_span ⟨((a,d),v),rfl⟩
        | zero => simp only [TensorProduct.tmul_zero, Submodule.zero_mem]
        | add x y _ _ hx hy => simpa only [TensorProduct.tmul_add] using
            (Submodule.span ℂ (Set.range (blockPure t S (i := i) (j := j) (n+1)))).add_mem hx hy
        | smul c w _ hw => simpa only [TensorProduct.tmul_smul] using
            (Submodule.span ℂ (Set.range (blockPure t S (i := i) (j := j) (n+1)))).smul_mem c hw

def blockReadPre (n : ℕ) : blockTensor t S i j n →ₗ[ℂ] preSpace t :=
  t.functional.toPreGNS.toLinearMap.comp (blockRead t S n)

@[simp] lemma blockReadPre_pure (n : ℕ) (x : BlockParams t S i j n) :
    (blockReadPre t S n (blockPure t S n x) : t.functional.GNS) =
      blockVector t S (paramLetters t S n x) (factorValue t S j (paramEnd t S n x)) := by
  change (t.functional.toPreGNS (blockRead t S n (blockPure t S n x)) : t.functional.GNS)=_
  rw [blockRead_pure]
  rfl

variable (hfree : Free S t.functional.toLinearMap) (hij : i≠j)

include hfree hij

lemma inner_blockReadPre_pure : ∀ n (x y : BlockParams t S i j n),
    inner ℂ (blockReadPre t S n (blockPure t S n x))
      (blockReadPre t S n (blockPure t S n y)) =
      inner ℂ (blockPure t S n x) (blockPure t S n y)
  | 0, x, y => by
    change inner ℂ (t.functional.toPreGNS (t.functional.ofPreGNS (x : preSpace t)))
      (t.functional.toPreGNS (t.functional.ofPreGNS (y : preSpace t))) = inner ℂ x y
    simp
  | n+1, x, y => by
    rw [←Completion.inner_coe, blockReadPre_pure, blockReadPre_pure]
    change inner ℂ (blockVector t S (x.1::paramLetters t S n x.2)
      (factorValue t S j (paramEnd t S n x.2)))
      (blockVector t S (y.1::paramLetters t S n y.2)
        (factorValue t S j (paramEnd t S n y.2))) = _
    rw [blockVector_cons_gram t S hfree hij _ _ _ _
      (z := factorValue t S j (paramEnd t S n x.2))
      (v := factorValue t S j (paramEnd t S n y.2))
      (paramEnd t S n x.2).property (paramEnd t S n y.2).property]
    rw [←blockReadPre_pure, ←blockReadPre_pure, Completion.inner_coe,
      inner_blockReadPre_pure n x.2 y.2]
    simp only [blockPure, TensorProduct.inner_tmul, mul_assoc]

lemma inner_blockReadPre (n : ℕ) (x y : blockTensor t S i j n) :
    inner ℂ (blockReadPre t S n x) (blockReadPre t S n y) = inner ℂ x y := by
  have hx : x ∈ Submodule.span ℂ (Set.range (blockPure t S (i := i) (j := j) n)) := by rw [span_blockPure]; trivial
  have hy : y ∈ Submodule.span ℂ (Set.range (blockPure t S (i := i) (j := j) n)) := by rw [span_blockPure]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v,rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨w,rfl⟩ := hy; exact inner_blockReadPre_pure t S hfree hij n v w
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, inner_add_right, hx, hy]
    | smul c y _ hy => simp only [map_smul, inner_smul_right, hy]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, inner_add_left, hx, hy]
  | smul c x _ hx => simp only [map_smul, inner_smul_left, hx]

def blockIsometry (n : ℕ) : blockTensor t S i j n →ₗᵢ[ℂ] preSpace t :=
  (blockReadPre t S n).isometryOfInner (inner_blockReadPre t S hfree hij n)

def blockEmbedding (n : ℕ) : Completion (blockTensor t S i j n) →ₗᵢ[ℂ] t.functional.GNS where
  toLinearMap := (blockIsometry t S hfree hij n).toContinuousLinearMap.completion.toLinearMap
  norm_map' x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x => simp

end Kadison.FreeBlocks
end

end OAI
