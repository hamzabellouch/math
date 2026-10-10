import Mathlib
import OAI.Analysis.Commutator.FreeSymmetry15
import OAI.Analysis.Commutator.FreeSymmetry8
import OAI.Analysis.Commutator.FreeSymmetry9

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
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap
open scoped InnerProductSpace ENNReal
open scoped ComplexOrder InnerProductSpace TensorProduct
open UniformSpace ContinuousLinearMap

namespace Kadison.TracialGNS

open PreHilbert HilbertTensor

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b)=τ (b*a)) (h1 : τ 1=1)

variable (J : ℕ → Type*) [∀ k, NormedAddCommGroup (J k)]
  [∀ k, InnerProductSpace ℂ (J k)] [∀ k, CompleteSpace (J k)]

abbrev sumLevel (k : ℕ) := Completion (wordSpace (fullSpace τ) (zeroSpace τ) k ⊗[ℂ] J k)

instance sumLevelNormed (k : ℕ) : NormedAddCommGroup (sumLevel τ J k) :=
  inferInstanceAs (NormedAddCommGroup (Completion (wordSpace (fullSpace τ) (zeroSpace τ) k ⊗[ℂ] J k)))

instance sumLevelInner (k : ℕ) : InnerProductSpace ℂ (sumLevel τ J k) :=
  inferInstanceAs (InnerProductSpace ℂ (Completion (wordSpace (fullSpace τ) (zeroSpace τ) k ⊗[ℂ] J k)))

instance sumLevelComplete (k : ℕ) : CompleteSpace (sumLevel τ J k) :=
  inferInstanceAs (CompleteSpace (Completion (wordSpace (fullSpace τ) (zeroSpace τ) k ⊗[ℂ] J k)))

def sumLeft (a : A) (k : ℕ) : sumLevel τ J k →L[ℂ] sumLevel τ J k :=
  HilbertTensor.map (wordLeft τ a k) 1

def sumConjugation (u : unitary A) (k : ℕ) : sumLevel τ J k →L[ℂ] sumLevel τ J k :=
  HilbertTensor.map (wordConjugation τ hτ u k).toContinuousLinearMap 1

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : ∀ k, sumLevel τ J k →ₗᵢ[ℂ] H) (hU : IsHilbertSum ℂ (sumLevel τ J) U)

variable (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]

variable (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)

variable (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)

variable (he : ∀ n m (h : n ≤ m) a, φ m (e h a)=φ n a)

variable (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))

variable (hgen : ∀ a : A, τ.gnsStarAlgHom a ∈ Set.centralizer (Set.centralizer
  (stageAlgebra τ I φ : Set (τ.GNS →L[ℂ] τ.GNS))))

variable (L : A → H →L[ℂ] H)

variable (W : ∀ n, unitary (Matrix (I n) (I n) ℂ) → H →L[ℂ] H)

variable (hL : ∀ a k, (L a).comp (U k).toContinuousLinearMap =
  (U k).toContinuousLinearMap.comp (sumLeft τ J a k))

variable (hW : ∀ n u k, (W n u).comp (U k).toContinuousLinearMap =
  (U k).toContinuousLinearMap.comp
    (sumConjugation τ hτ J (stageUnitary (φ n) u) k))

variable (G : H →L[ℂ] H)

variable (hGL : ∀ a, G.comp (L a)=(L a).comp G)

variable (hGW : ∀ n u, G.comp (W n u)=(W n u).comp G)

omit [∀ k, CompleteSpace (J k)] [∀ n, Nonempty (I n)] in
include hU hW hGW in
lemma actual_block_conjugation (k l n : ℕ) (u : unitary (Matrix (I n) (I n) ℂ)) :
    (ActualHilbertSum.block (sumLevel τ J) U G l k).comp
      (sumConjugation τ hτ J (stageUnitary (φ n) u) k) =
    (sumConjugation τ hτ J (stageUnitary (φ n) u) l).comp
      (ActualHilbertSum.block (sumLevel τ J) U G l k) := by
  exact ActualHilbertSum.block_covariant_of_insert (sumLevel τ J) U hU G (W n u)
    (fun k => sumConjugation τ hτ J (stageUnitary (φ n) u) k)
    (hGW n u) (hW n u) l k

omit [∀ k, CompleteSpace (J k)] in
include hU hL hGL in
lemma actual_block_left (k l : ℕ) (a : A) :
    (ActualHilbertSum.block (sumLevel τ J) U G l k).comp (sumLeft τ J a k) =
    (sumLeft τ J a l).comp (ActualHilbertSum.block (sumLevel τ J) U G l k) := by
  exact ActualHilbertSum.block_covariant_of_insert (sumLevel τ J) U hU G (L a)
    (fun k => sumLeft τ J a k) (hGL a) (hL a) l k

omit [∀ k, CompleteSpace (J k)] in
include h1 hU he hsize hgen hL hW hGL hGW in
lemma actual_block_classification (k l : ℕ) :
    ∀ a : J k, ∀ b : J l, ∃ c : (Fin k ≃ Fin l) → ℂ,
      scalarSlice (ActualHilbertSum.block (sumLevel τ J) U G l k) a b =
        ∑ σ, c σ • (wordReindex (fullSpace τ) (zeroSpace τ) σ).toContinuousLinearMap := by
  exact word_multiplicity_slices τ hτ h1 _ I φ e he hsize
    (dense_stages_of_bicommutant_generation τ I φ e he hgen)
    (actual_block_conjugation τ hτ J U hU I φ W hW G hGW k l)
    (actual_block_left τ J U hU L hL G hGL k l)

include h1 hU he hsize hgen hL hW hGL hGW in
theorem actual_word_structure : ∃ B : ∀ k, J k →L[ℂ] J k,
    (∀ k, ‖B k‖ ≤ ‖G‖) ∧
    (∀ k (d : fullSpace τ) (x : zeroSpace τ) (a : J k),
      G (U k (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) a)) =
        U k (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) (B k a))) ∧
    (∀ k (d : fullSpace τ) (x : zeroSpace τ) (a : J k),
      G.adjoint (U k (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) a)) =
        U k (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) ((B k).adjoint a))) := by
  classical
  have hclass := actual_block_classification τ hτ h1 J U hU I φ e he hsize hgen L W hL hW G hGL hGW
  have hoff : ∀ i j, i≠j → ActualHilbertSum.block (sumLevel τ J) U G i j=0 := by
    intro i j hij
    exact word_multiplicity_offlevel τ _ hij.symm (hclass j i)
  obtain ⟨z,hz⟩ := exists_unit_centered_letter τ hτ h1 I φ (by
    obtain ⟨n,_,hn⟩ := hsize 0 2
    exact ⟨n,hn⟩)
  have hex (k : ℕ) := word_multiplicity_both τ h1
    (ActualHilbertSum.block (sumLevel τ J) U G k k) (hclass k k) z hz
  choose B hB hG hGa using hex
  refine ⟨B,fun k => (hB k).trans (ActualHilbertSum.norm_block_le (sumLevel τ J) U G k k),?_,?_⟩
  · intro k d x a
    have hr := congrArg (fun T : sumLevel τ J k →L[ℂ] H =>
      T (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) a))
      (ActualHilbertSum.reduces_of_offdiagonal (sumLevel τ J) U hU G hoff k)
    exact hr.trans (congrArg (U k) (hG k d x a))
  · intro k d x a
    have hr := congrArg (fun T : sumLevel τ J k →L[ℂ] H =>
      T (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) a))
      (ActualHilbertSum.adjoint_reduces_of_offdiagonal (sumLevel τ J) U hU G hoff k)
    exact hr.trans (congrArg (U k) (hGa k d x a))

end Kadison.TracialGNS
end

end OAI
