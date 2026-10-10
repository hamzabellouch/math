import Mathlib
import OAI.Analysis.Commutator.EndpointGNS2
import OAI.Analysis.Commutator.EndpointRankOne

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

open PreHilbert

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

variable {k l : ℕ}

variable (Y : wordSpace (fullSpace τ) (zeroSpace τ) k →L[ℂ]
  wordSpace (fullSpace τ) (zeroSpace τ) l)

include h1 in
theorem stageCoefficient_cycleCutoff (I : ℕ → Type*)
    [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
    (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)
    (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
    (he : ∀ n m (h : n ≤ m) a, φ m (e h a) = φ n a)
    (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
    (hY : ∀ n (u : unitary (Matrix (I n) (I n) ℂ)),
      Y.comp (wordConjugation τ hτ (stageUnitary (φ n) u) k).toContinuousLinearMap =
        (wordConjugation τ hτ (stageUnitary (φ n) u) l).toContinuousLinearMap.comp Y)
    (hleft : ∀ a : A, Y.comp (wordLeft τ a k) = (wordLeft τ a l).comp Y) :
    ∃ c : Equiv.Perm (Option (Fin k ⊕ Fin l)) → ℂ,
      (∀ n (v : Option (Fin k ⊕ Fin l) → Matrix (I n) (I n) ℂ),
        stageCoefficient τ Y (φ n) v = ∑ σ, c σ * SchurWeyl.cycleTrace σ v) ∧
      ∀ σ, 2 * SchurWeyl.cycleCount σ < Fintype.card (Option (Fin k ⊕ Fin l)) + 1 → c σ = 0 := by
  classical
  obtain ⟨c, hc⟩ := stageCoefficient_expansion τ hτ h1 Y I φ e he hsize hY
  refine ⟨c, hc, ?_⟩
  intro σ hσ
  let J := Option (Fin k ⊕ Fin l)
  choose j hj using fun n => hsize 0 (max n (Fintype.card J))
  have hjJ (n) : Fintype.card J ≤ Fintype.card (I (j n)) :=
    (le_max_right n (Fintype.card J)).trans (hj n).2
  let b (n) : J ↪ I (j n) := Classical.choice (Function.Embedding.nonempty_of_card_le (hjJ n))
  apply SchurWeyl.endpoint_coefficients_vanish_of_rank_one (fun n => I (j n))
    (none : J) (fun n => b n) (fun n => (b n).injective)
    (fun n => stageCoefficient τ Y (φ (j n))) c ‖Y‖ (ContinuousLinearMap.opNorm_nonneg Y) (fun n => hc (j n))
  · intro n ρ
    exact stageCoefficient_rank_one τ hτ h1 Y (φ (j n)) hleft (b n) ρ
  · intro B
    exact ⟨B, (le_max_left B (Fintype.card J)).trans (hj B).2⟩
  · exact hσ

end Kadison.TracialGNS
end

end OAI
