import Mathlib
import OAI.Analysis.Commutator.FreeSymmetry7
import OAI.Analysis.Commutator.StageGeneration
import OAI.Analysis.Commutator.TensorAdjoints

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

namespace Kadison.TracialGNS

open PreHilbert HilbertTensor

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b) = τ (b*a)) (h1 : τ 1 = 1)

variable (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]

variable (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)

include hτ h1 φ in
lemma exists_unit_centered_letter (hsize : ∃ n, 2 ≤ Fintype.card (I n)) :
    ∃ z : zeroSpace τ, ‖z‖ = 1 := by
  classical
  obtain ⟨n, hn⟩ := hsize
  have hc : Fintype.card (Fin 2) ≤ Fintype.card (I n) := by simpa using hn
  obtain ⟨b⟩ := (Function.Embedding.nonempty_of_card_le hc)
  let a : Unit ↪ I n := ⟨fun _ => b 1, fun _ _ _ => Subsingleton.elim _ _⟩
  have ha : ∀ j, a j ≠ b 0 := fun _ => b.injective.ne (by decide : (1 : Fin 2) ≠ 0)
  exact ⟨centeredStageVector τ (φ n) (MatrixAlphabet.normalizedLetter (b 0) (b 1)),
    (normalizedLetter_orthonormal τ hτ h1 (φ n) (b 0) a ha).norm_eq_one ()⟩

include h1 in
theorem invariant_intertwiner {k l : ℕ}
    (Y : wordSpace (fullSpace τ) (zeroSpace τ) k →L[ℂ]
      wordSpace (fullSpace τ) (zeroSpace τ) l)
    (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
    (he : ∀ n m (h : n ≤ m) a, φ m (e h a) = φ n a)
    (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
    (hgen : ∀ a : A, τ.gnsStarAlgHom a ∈ Set.centralizer (Set.centralizer
      (stageAlgebra τ I φ : Set (τ.GNS →L[ℂ] τ.GNS))))
    (hY : ∀ n (u : unitary (Matrix (I n) (I n) ℂ)),
      Y.comp (wordConjugation τ hτ (stageUnitary (φ n) u) k).toContinuousLinearMap =
        (wordConjugation τ hτ (stageUnitary (φ n) u) l).toContinuousLinearMap.comp Y)
    (hleft : ∀ a : A, Y.comp (wordLeft τ a k) = (wordLeft τ a l).comp Y) :
    ∃ c : (Fin k ≃ Fin l) → ℂ,
      Y = ∑ σ, c σ • (wordReindex (fullSpace τ) (zeroSpace τ) σ).toContinuousLinearMap :=
  word_intertwiner τ hτ h1 Y I φ e he hsize
    (dense_stages_of_bicommutant_generation τ I φ e he hgen) hY hleft

include h1 in
theorem word_multiplicity_both {k : ℕ} {J : Type*}
    [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
    (T : Completion (wordSpace (fullSpace τ) (zeroSpace τ) k ⊗[ℂ] J) →L[ℂ]
      Completion (wordSpace (fullSpace τ) (zeroSpace τ) k ⊗[ℂ] J))
    (hclass : ∀ a b : J, ∃ c : Equiv.Perm (Fin k) → ℂ,
      scalarSlice T a b = ∑ σ, c σ •
        (wordReindex (fullSpace τ) (zeroSpace τ) σ).toContinuousLinearMap)
    (z : zeroSpace τ) (hz : ‖z‖ = 1) :
    ∃ B : J →L[ℂ] J, ‖B‖ ≤ ‖T‖ ∧
      (∀ (d : fullSpace τ) (x : zeroSpace τ) (a : J),
        T (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) a) =
          pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) (B a)) ∧
      (∀ (d : fullSpace τ) (x : zeroSpace τ) (a : J),
        T.adjoint (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) a) =
          pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) (B.adjoint a)) := by
  let v := word (fullSpace τ) (zeroSpace τ) k (vacuum τ) (fun _ => z)
  have hv : ‖v‖ = 1 := by
    simp only [v, norm_word, vacuum_norm τ h1, hz, Finset.prod_const_one, mul_one]
  refine ⟨multiplicityCompression T v, norm_multiplicityCompression_le T v hv, ?_, ?_⟩
  · intro d x a
    apply repeated_pair T (fun σ : Equiv.Perm (Fin k) =>
      (wordReindex (fullSpace τ) (zeroSpace τ) σ).toContinuousLinearMap) hclass v _ hv
    · intro σ
      simp only [v, LinearIsometry.coe_toContinuousLinearMap, wordReindex_word, Function.comp_def]
    · intro σ
      simp only [LinearIsometry.coe_toContinuousLinearMap, wordReindex_word, Function.comp_def]
  · intro d x a
    apply repeated_pair_adjoint T (wordReindex (fullSpace τ) (zeroSpace τ)) hclass v _ hv
    · intro σ
      simp only [v, wordReindex_word, Function.comp_def]
    · intro σ
      simp only [wordReindex_word, Function.comp_def]

end Kadison.TracialGNS
end

end OAI
