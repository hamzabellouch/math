import Mathlib
import OAI.Analysis.Commutator.CyclePairTrace3
import OAI.Analysis.Commutator.EndpointGNS
import OAI.Analysis.Commutator.FinitePairings3
import OAI.Analysis.Commutator.HermitianAlphabet
import OAI.Analysis.Commutator.HermitianAlphabet2

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

variable {k l : ℕ} (Y : wordSpace (fullSpace τ) (zeroSpace τ) k →L[ℂ]
  wordSpace (fullSpace τ) (zeroSpace τ) l)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)

lemma stage_pairing_expansion (d : Equiv.Perm (Option (TailSlots k l)) → ℂ)
    (hd : ∀ σ, 2 * SchurWeyl.cycleCount σ < Fintype.card (Option (TailSlots k l)) + 1 → d σ = 0)
    (hexp : ∀ v : Option (TailSlots k l) → Matrix I I ℂ,
      stageCoefficient τ Y φ v = ∑ σ, d σ * SchurWeyl.cycleTrace σ v)
    (v : TailSlots k l → Matrix I I ℂ) (hv : ∀ j, Matrix.trace (v j) = 0) :
    stageCoefficient τ Y φ (fun o => o.elim (1 : Matrix I I ℂ) v) =
      ∑ σ : Pairing (TailSlots k l), d (SchurWeyl.endpointPairingPerm σ) *
        Pairing.contraction σ (fun X Z => (Fintype.card I : ℂ)⁻¹ * Matrix.trace (X * Z)) v := by
  have hh := SchurWeyl.centered_expansion_contractions d hd
    (fun o : Option (TailSlots k l) => o.elim (1 : Matrix I I ℂ) v) (fun j => hv j)
  have hm : (Fintype.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [Option.elim_none, Option.elim_some, Matrix.trace_one,
    inv_mul_cancel₀ hm, one_mul] at hh
  exact (hexp (fun o : Option (TailSlots k l) => o.elim (1 : Matrix I I ℂ) v)).trans hh

omit [Nonempty I] in
lemma stage_alphabet_coefficient {J : Type*} [DecidableEq J]
    (c : Pairing (TailSlots k l) → ℂ)
    (hexp : ∀ v : TailSlots k l → Matrix I I ℂ, (∀ j, Matrix.trace (v j) = 0) →
      stageCoefficient τ Y φ (fun o => o.elim (1 : Matrix I I ℂ) v) =
        ∑ σ, c σ * Pairing.contraction σ
          (fun X Z => (Fintype.card I : ℂ)⁻¹ * Matrix.trace (X * Z)) v)
    (a : J → Matrix I I ℂ) (ha : ∀ j, star (a j) = a j)
    (hat : ∀ j, Matrix.trace (a j) = 0)
    (hai : ∀ i j, (Fintype.card I : ℂ)⁻¹ * Matrix.trace (a i * a j) =
      if i = j then 1 else 0) (v : TailSlots k l → J) :
    inner ℂ (word (fullSpace τ) (zeroSpace τ) l (vacuum τ)
      (fun j => centeredStageVector τ φ (a (v (.inr j)))))
      (Y (word (fullSpace τ) (zeroSpace τ) k (vacuum τ)
        (fun i => centeredStageVector τ φ (a (v (.inl i)))))) =
      ∑ σ, c σ * Pairing.contraction σ (fun i j => if i = j then 1 else 0) v := by
  have hh := hexp (fun j => a (v j)) (fun j => hat (v j))
  change coefficient (fullSpace τ) (zeroSpace τ) k l Y (vacuum τ)
    (stageVector τ φ) (centeredStageVector τ φ)
    (fun o : Option (Fin k ⊕ Fin l) => o.elim (1 : Matrix I I ℂ) (fun j => a (v j))) =
    ∑ σ, c σ * Pairing.contraction σ
      (fun X Z => (Fintype.card I : ℂ)⁻¹ * Matrix.trace (X * Z)) (fun j => a (v j)) at hh
  dsimp only [coefficient, Option.elim_none, Option.elim_some] at hh
  simp only [star_one, stage_vacuum, ha] at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  simp only [Pairing.contraction, hai]

include hτ h1 in
theorem stage_pairing_same_side_zero (Is : ℕ → Type*)
    [∀ n, Fintype (Is n)] [∀ n, DecidableEq (Is n)] [∀ n, Nonempty (Is n)]
    (φs : ∀ n, Matrix (Is n) (Is n) ℂ →⋆ₐ[ℂ] A)
    (hsize : ∀ q : ℕ, ∃ n, q ≤ Fintype.card (Is n))
    (c : Pairing (TailSlots k l) → ℂ)
    (hexp : ∀ n (v : TailSlots k l → Matrix (Is n) (Is n) ℂ),
      (∀ j, Matrix.trace (v j) = 0) →
      stageCoefficient τ Y (φs n) (fun o => o.elim (1 : Matrix (Is n) (Is n) ℂ) v) =
        ∑ σ, c σ * Pairing.contraction σ
          (fun X Z => (Fintype.card (Is n) : ℂ)⁻¹ * Matrix.trace (X * Z)) v)
    (σ : Pairing (TailSlots k l))
    (hsame : (∃ a b : Fin k, σ (.inl a) = .inl b) ∨
      (∃ a b : Fin l, σ (.inr a) = .inr b)) : c σ = 0 := by
  classical
  have hbound (N : ℕ) : (N+1 : ℝ) * ‖c σ‖ ^ 2 ≤ ‖Y‖ ^ 2 := by
    let J := TailSlots k l × Fin (N+1)
    obtain ⟨n, hn⟩ := hsize (Fintype.card (Option J))
    let b : Option J ↪ Is n := Classical.choice (Function.Embedding.nonempty_of_card_le hn)
    let bt : J ↪ Is n := ⟨fun j => b (some j), fun x y h => Option.some.inj (b.injective h)⟩
    have hb (j : J) : bt j ≠ b none := by
      intro h
      exact Option.some_ne_none j (b.injective h)
    let a : J → Matrix (Is n) (Is n) ℂ := fun j => MatrixAlphabet.normalizedLetter (b none) (bt j)
    let h : J → zeroSpace τ := fun j => centeredStageVector τ (φs n) (a j)
    have horth : Orthonormal ℂ h := normalizedLetter_orthonormal τ hτ h1 (φs n) (b none) bt hb
    have ha (j) : star (a j) = a j := MatrixAlphabet.star_normalizedLetter _ _
    have hat (j) : Matrix.trace (a j) = 0 := MatrixAlphabet.trace_normalizedLetter _ _ (hb j)
    have hai (i j) : (Fintype.card (Is n) : ℂ)⁻¹ * Matrix.trace (a i * a j) =
        if i = j then 1 else 0 := by
      rw [MatrixAlphabet.normalized_trace_mul _ _ _ (hb i) (hb j)]
      simp only [EmbeddingLike.apply_eq_iff_eq]
    have he (v : TailSlots k l → J) :=
      stage_alphabet_coefficient τ Y (φs n) c (hexp n) a ha hat hai v
    rcases hsame with ⟨i, j, hij⟩ | ⟨i, j, hij⟩
    · exact finite_pairing_source_bound (fullSpace τ) (zeroSpace τ) k l N
        (vacuum τ) (vacuum_norm τ h1) Y c h horth he σ i j hij
    · exact finite_pairing_test_bound (fullSpace τ) (zeroSpace τ) k l N
        (vacuum τ) (vacuum_norm τ h1) Y c h horth he σ i j hij
  by_contra hc
  have hz : 0 < ‖c σ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hc)
  obtain ⟨N, hN⟩ := exists_nat_gt (‖Y‖ ^ 2 / ‖c σ‖ ^ 2)
  have hgt : ‖Y‖ ^ 2 < (N : ℝ) * ‖c σ‖ ^ 2 := (div_lt_iff₀ hz).mp hN
  have hh := hbound N
  nlinarith

end Kadison.TracialGNS
end

end OAI
