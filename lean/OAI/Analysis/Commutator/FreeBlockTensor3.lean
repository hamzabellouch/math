import Mathlib
import OAI.Analysis.Commutator.FreeBlockTensor2

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

variable {i j : ι} (hcolors : ∀ c : ι, c=i ∨ c=j)

def factorOf (i : ι) (a : A) (ha : a∈S i) : factorSpace t S i :=
  ⟨t.functional.toPreGNS a, by simpa [factorSpace] using ha⟩

def letterOf (i : ι) (a : A) (ha : a∈S i) (ha0 : t.functional a=0) : letterSpace t S i :=
  ⟨t.functional.toPreGNS a, by simpa [letterSpace] using And.intro ha ha0⟩

@[simp] lemma factorValue_factorOf (i : ι) (a : A) (ha : a∈S i) :
    factorValue t S i (factorOf t S i a ha)=a := by simp [factorValue, factorOf]

@[simp] lemma letterValue_letterOf (i : ι) (a : A) (ha : a∈S i) (ha0 : t.functional a=0) :
    letterValue t S i (letterOf t S i a ha ha0)=a := by simp [letterValue, letterOf]

include hcolors in
lemma tail_word_as_block (w : List (Letter t S)) (hw : Reduced w)
    (hiw : CanPrepend t S i w) :
    ∃ (n : ℕ) (p : BlockParams t S i j n), word w = blockRead t S n (blockPure t S n p) := by
  induction w using List.twoStepInduction with
  | nil =>
    refine ⟨0, factorOf t S j 1 (one_mem _), ?_⟩
    exact (factorValue_factorOf t S j 1 (one_mem _)).symm
  | singleton a =>
    have hai : i≠a.color := by simpa [CanPrepend] using hiw
    have haj : a.color=j := (hcolors a.color).resolve_left (Ne.symm hai)
    refine ⟨0, factorOf t S j a.val (haj ▸ a.mem), ?_⟩
    simp only [word_cons, word_nil, mul_one, blockRead, blockPure, factorValue_factorOf]
  | cons_cons a b w ih =>
    have hai : i≠a.color := by simpa [CanPrepend] using hiw
    have haj : a.color=j := (hcolors a.color).resolve_left (Ne.symm hai)
    have hbi : b.color=i := (hcolors b.color).resolve_right (by
      intro hbj; exact hw.rel (haj.trans hbj.symm))
    have hiw' : CanPrepend t S i w := by
      cases w with
      | nil => simp [CanPrepend]
      | cons c w => simpa [CanPrepend, hbi] using hw.tail.rel
    obtain ⟨n,p,hp⟩ := ih hw.tail.tail hiw'
    let aa := letterOf t S j a.val (haj ▸ a.mem) a.centered
    let bb := letterOf t S i b.val (hbi ▸ b.mem) b.centered
    refine ⟨n+1, ((aa,bb),p), ?_⟩
    change a.val*(b.val*word w) = letterValue t S j aa *
      (letterValue t S i bb * blockRead t S n (blockPure t S n p))
    simp only [aa, bb, letterValue_letterOf, hp]

include hcolors in
lemma word_as_endpoint (w : List (Letter t S)) (hw : Reduced w) :
    ∃ (n : ℕ) (x : endpointTensor t S i j n),
      (t.functional.toPreGNS (word w))=endpointRead t S n x := by
  classical
  by_cases hiw : CanPrepend t S i w
  · obtain ⟨n,p,hp⟩ := tail_word_as_block t S hcolors w hw hiw
    refine ⟨n, factorOf t S i 1 (one_mem _) ⊗ₜ[ℂ] blockPure t S n p, ?_⟩
    change t.functional.toPreGNS (word w) = t.functional.toPreGNS
      (factorValue t S i (factorOf t S i 1 (one_mem _))*blockRead t S n (blockPure t S n p))
    rw [factorValue_factorOf, one_mul, hp]
  · cases w with
    | nil => exact False.elim (hiw (by simp [CanPrepend]))
    | cons a w =>
      have hai : a.color=i := by simpa [CanPrepend] using (show i=a.color by simpa [CanPrepend] using hiw).symm
      have hiw' : CanPrepend t S i w := by
        cases w with
        | nil => simp [CanPrepend]
        | cons b w => simpa [CanPrepend, hai] using hw.rel
      obtain ⟨n,p,hp⟩ := tail_word_as_block t S hcolors w hw.tail hiw'
      refine ⟨n, factorOf t S i a.val (hai ▸ a.mem) ⊗ₜ[ℂ] blockPure t S n p, ?_⟩
      change t.functional.toPreGNS (a.val*word w) = t.functional.toPreGNS
        (factorValue t S i (factorOf t S i a.val (hai ▸ a.mem))*blockRead t S n (blockPure t S n p))
      rw [factorValue_factorOf, hp]

end Kadison.FreeBlocks
end

end OAI
