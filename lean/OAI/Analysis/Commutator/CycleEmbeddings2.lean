import Mathlib
import OAI.Analysis.Commutator.CycleEmbeddings

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.SchurWeyl

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem matrix_union_expansion (I : ℕ → Type*)
    [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
    (φ : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →ₐ[ℂ] Matrix (I m) (I m) ℂ)
    (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
    (F : ∀ n, MultilinearMap ℂ (fun _ : J => Matrix (I n) (I n) ℂ) ℂ)
    (hinv : ∀ n (u : unitary (Matrix (I n) (I n) ℂ)) (A : J → Matrix (I n) (I n) ℂ),
      F n (fun j => (u : Matrix (I n) (I n) ℂ) * A j * star (u : Matrix (I n) (I n) ℂ)) = F n A)
    (hcomp : ∀ n m (h : n ≤ m) (A : J → Matrix (I n) (I n) ℂ),
      F m (fun j => φ h (A j)) = F n A) :
    ∃ c : Equiv.Perm J → ℂ, ∀ n (A : J → Matrix (I n) (I n) ℂ),
      F n A = ∑ σ, c σ * cycleTrace σ A := by
  classical
  obtain ⟨n₀, _, hn₀⟩ := hsize 0 (Fintype.card J)
  let b : J ↪ I n₀ := Classical.choice (Function.Embedding.nonempty_of_card_le hn₀)
  obtain ⟨c, hc, _⟩ := invariant_multilinear_form_normalized b b.injective (F n₀) (hinv n₀)
  refine ⟨c, ?_⟩
  intro n A
  obtain ⟨m, hnm, hm⟩ := hsize (max n n₀) (Fintype.card J)
  have hn : n ≤ m := (le_max_left n n₀).trans hnm
  have hn₀m : n₀ ≤ m := (le_max_right n n₀).trans hnm
  let b' : J ↪ I m := Classical.choice (Function.Embedding.nonempty_of_card_le hm)
  obtain ⟨d, hd, _⟩ := invariant_multilinear_form_normalized b' b'.injective (F m) (hinv m)
  have hcd : c = d := by
    apply stable_cycle_coefficients_map (φ hn₀m) b b.injective
    intro B
    rw [← hc, ← hd, hcomp]
  rw [← hcomp n m hn A, hd]
  simp only [← hcd, cycleTrace_map]

end Kadison.SchurWeyl
end

end OAI
