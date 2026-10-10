import Mathlib
import OAI.Analysis.Commutator.CycleEmbeddings2
import OAI.Analysis.Commutator.MatrixGNS
import OAI.Analysis.Commutator.TensorActions

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.TracialGNS

open PreHilbert

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

abbrev fullSpace : PreHilbert := ⟨τ.GNS⟩

abbrev zeroSpace : PreHilbert := ⟨centeredSpace (vacuum τ)⟩

noncomputable def wordConjugation (u : unitary A) (k : ℕ) :
    wordSpace (fullSpace τ) (zeroSpace τ) k →ₗᵢ[ℂ]
      wordSpace (fullSpace τ) (zeroSpace τ) k :=
  wordMap (fullSpace τ) (zeroSpace τ) (conjugation τ hτ u)
    (centeredIsometry (vacuum τ) (conjugation τ hτ u) (conjugation_vacuum τ hτ u)) k

variable {k l : ℕ}

variable (Y : wordSpace (fullSpace τ) (zeroSpace τ) k →L[ℂ]
  wordSpace (fullSpace τ) (zeroSpace τ) l)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

noncomputable def stageCoefficient (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) :
    MultilinearMap ℂ (fun _ : Option (Fin k ⊕ Fin l) => Matrix I I ℂ) ℂ :=
  coefficientMultilinear (fullSpace τ) (zeroSpace τ) k l Y (vacuum τ)
    (stageVector τ φ) (centeredStageVector τ φ)

omit [Nonempty I] in
include h1 in
lemma stageCoefficient_invariant (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)
    (u : unitary (Matrix I I ℂ))
    (hY : Y.comp (wordConjugation τ hτ (stageUnitary φ u) k).toContinuousLinearMap =
      (wordConjugation τ hτ (stageUnitary φ u) l).toContinuousLinearMap.comp Y)
    (v : Option (Fin k ⊕ Fin l) → Matrix I I ℂ) :
    stageCoefficient τ Y φ (fun i => (u : Matrix I I ℂ) * v i * star (u : Matrix I I ℂ)) =
      stageCoefficient τ Y φ v := by
  apply coefficient_invariant (fullSpace τ) (zeroSpace τ) k l Y (vacuum τ)
    (stageVector τ φ) (centeredStageVector τ φ) (conjugation τ hτ (stageUnitary φ u))
    (centeredIsometry (vacuum τ) (conjugation τ hτ (stageUnitary φ u))
      (conjugation_vacuum τ hτ _)) (fun a => (u : Matrix I I ℂ) * a * star (u : Matrix I I ℂ))
  · intro a
    simp only [star_mul, star_star, mul_assoc]
  · intro a
    exact (stage_conjugation τ hτ φ u a).symm
  · intro a
    exact (centered_stage_conjugation τ hτ h1 φ u a).symm
  · exact conjugation_vacuum τ hτ _
  · exact hY

variable {K : Type*} [Fintype K] [DecidableEq K] [Nonempty K]

omit [Nonempty I] [Nonempty K] in
lemma stageCoefficient_compatible (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)
    (ψ : Matrix K K ℂ →⋆ₐ[ℂ] A) (e : Matrix I I ℂ →⋆ₐ[ℂ] Matrix K K ℂ)
    (he : ∀ a, ψ (e a) = φ a) (v : Option (Fin k ⊕ Fin l) → Matrix I I ℂ) :
    stageCoefficient τ Y ψ (fun i => e (v i)) = stageCoefficient τ Y φ v := by
  change coefficient (fullSpace τ) (zeroSpace τ) k l Y (vacuum τ)
    (stageVector τ ψ) (centeredStageVector τ ψ) (fun i => e (v i)) =
    coefficient (fullSpace τ) (zeroSpace τ) k l Y (vacuum τ)
      (stageVector τ φ) (centeredStageVector τ φ) v
  simp only [coefficient, stageVector, centeredStageVector, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom, map_star, he]

include h1 in
theorem stageCoefficient_expansion (I : ℕ → Type*)
    [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
    (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)
    (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
    (he : ∀ n m (h : n ≤ m) a, φ m (e h a) = φ n a)
    (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
    (hY : ∀ n (u : unitary (Matrix (I n) (I n) ℂ)),
      Y.comp (wordConjugation τ hτ (stageUnitary (φ n) u) k).toContinuousLinearMap =
        (wordConjugation τ hτ (stageUnitary (φ n) u) l).toContinuousLinearMap.comp Y) :
    ∃ c : Equiv.Perm (Option (Fin k ⊕ Fin l)) → ℂ,
      ∀ n (v : Option (Fin k ⊕ Fin l) → Matrix (I n) (I n) ℂ),
        stageCoefficient τ Y (φ n) v = ∑ σ, c σ * SchurWeyl.cycleTrace σ v := by
  apply SchurWeyl.matrix_union_expansion I (fun h => (e h).toAlgHom) hsize
    (fun n => stageCoefficient τ Y (φ n))
  · intro n u v
    exact stageCoefficient_invariant τ hτ h1 Y (φ n) u (hY n u) v
  · intro n m h v
    exact stageCoefficient_compatible τ Y (φ n) (φ m) (e h) (he n m h) v

end Kadison.TracialGNS
end

end OAI
