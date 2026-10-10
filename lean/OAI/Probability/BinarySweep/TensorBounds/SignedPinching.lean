import Mathlib
import OAI.Probability.BinarySweep.TensorBounds.EvenPostselection
import OAI.Probability.BinarySweep.MatrixBounds.SparsePinching

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder
open Equiv Equiv.Perm Matrix

namespace BinaryCoordinateSweeps.Signed
open Density

variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

lemma pinch_trace {I J : Type*} [Fintype I] [DecidableEq J] (f : I → J) (M : Matrix I I ℂ) :
    (pinch f M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, pinch, ite_true]

omit [Fintype A] [DecidableEq A] in
lemma comp_parity_eq_iff (p : A → Bool) (x y : Fin n → A) (g : Equiv.Perm (Fin n)) :
    p ∘ (x ∘ g) = p ∘ (y ∘ g) ↔ p ∘ x = p ∘ y := by
  constructor
  · intro h
    funext i
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using congrFun h (g.symm i)
  · intro h
    exact congrArg (fun f => f ∘ g) h

omit [Fintype A] [DecidableEq A] in
lemma pinch_block (p : A → Bool) (M : Matrix (Fin n → A) (Fin n → A) ℂ)
    (x y : Fin n → A) (h : p ∘ x ≠ p ∘ y) :
    pinch (fun w => p ∘ w) M x y = 0 := ite_eq_right h

omit [Fintype A] [DecidableEq A] in
lemma pinch_invariant (p : A → Bool) (M : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hM : Invariant p M) (g : Equiv.Perm (Fin n)) (x y : Fin n → A) :
    pinch (fun w => p ∘ w) M (x ∘ g) (y ∘ g) = pinch (fun w => p ∘ w) M x y := by
  simp only [pinch, comp_parity_eq_iff]
  split_ifs with h
  · exact invariant_same_parity p M hM g x y h
  · rfl

omit [DecidableEq A] in
lemma signed_sparse_pinching (p : A → Bool) (M : Matrix (Fin n → A) (Fin n → A) ℂ)
    (hM : M.PosSemidef) (hInv : Invariant p M) :
    (((n+1 : ℕ)^((Fintype.card A)^2) : ℂ) • pinch (fun w => p ∘ w) M - M).PosSemidef := by
  let R : (Fin n → Bool) → (Fin n → Bool) → Prop :=
    fun a b => hamming a b ≤ (Fintype.card A)^2
  have hR : ∀ ⦃left right⦄, R left right → R right left := by
    intro a b h
    change hamming b a ≤ (Fintype.card A)^2
    rw [hamming_symm b a]
    exact h
  have hD : ∀ a : Fin n → Bool, (Finset.univ.filter (R a)).card ≤
      (n+1)^((Fintype.card A)^2) := by
    intro a
    simpa only [Fintype.card_fin] using hamming_degree a ((Fintype.card A)^2)
  have hz : ∀ x y : Fin n → A, ¬R (p ∘ x) (p ∘ y) → M x y = 0 := by
    intro x y h
    by_contra hn
    exact h (invariant_mismatch_card p M hInv x y hn)
  simpa only [Nat.cast_pow] using
    sparse_pinching (fun w => p ∘ w) R hR ((n+1)^((Fintype.card A)^2)) hD hM hz

theorem signed_psd_postselection (n : ℕ) (hn : 0 < n) (p : A → Bool)
    (M : Matrix (Fin n → A) (Fin n → A) ℂ) (hM : M.PosSemidef) (hInv : Invariant p M) :
    ((((n+1 : ℕ)^((Fintype.card A)^2) : ℂ) * M.trace) •
      (∑ c : WordType (MatchedPair p) n, ∑ t : MatchedPair p → ZMod (n+1),
        matrixTensorPower n (reducedPhaseDensity n (matchedEmbedding p) c t)) - M).PosSemidef := by
  let Q := pinch (fun w => p ∘ w) M
  have hQ := pinch_posSemidef (fun w => p ∘ w) hM
  have hd := even_block_postselection n hn p Q hQ (pinch_block p M) (pinch_invariant p M hInv)
  rw [pinch_trace] at hd
  have hc : (0 : ℂ) ≤ ((n+1 : ℕ)^((Fintype.card A)^2) : ℂ) := by
    exact_mod_cast Nat.zero_le ((n+1)^((Fintype.card A)^2))
  have hh := (hd.smul hc).add (signed_sparse_pinching p M hM hInv)
  simp only [smul_sub, smul_smul] at hh
  convert hh using 1; dsimp only [Q]; abel

end BinaryCoordinateSweeps.Signed

end

end OAI
