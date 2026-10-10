import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseSignedPartial
import OAI.Combinatorics.KMedian.Rounding.RationalSignedTerminal
import OAI.Combinatorics.KMedian.Sparse.SparseBind

namespace OAI

section
section
namespace MetricKMedian.SparseSignedRounding
open Finset
open RationalWeightedStep (point fractional)
open SparseWeightedPartial (features features_single features_pair)
variable {n : ℕ}

def kernel (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1)
    (a : Fin (SparseSignedPartial.run u p n).length) : SparseIntegerLaw (Vector ℚ n) :=
  RationalSignedTerminal.terminal u (SparseSignedPartial.run u p n).states[a.val]
    (SparseSignedPartial.run_invariants u p hp n a).1

def round (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) : SparseIntegerLaw (Vector ℚ n) :=
  (SparseSignedPartial.run u p n).bindCompress (kernel u p hp) features

theorem round_length (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) :
    (round u p hp).length ≤ n+n*n+1 :=
  ((SparseSignedPartial.run u p n).bindCompress_spec (kernel u p hp) features).1

theorem round_mean (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (i : Fin n) :
    (round u p hp).moment (fun q => point q i)=point p i := by
  have hh := ((SparseSignedPartial.run u p n).bindCompress_spec (kernel u p hp)
    features).2.2 (finSumFinEquiv (Sum.inl i))
  simp only [features_single,kernel,RationalSignedTerminal.terminal_mean] at hh
  exact hh.trans (SparseSignedPartial.run_mean u p n i)

theorem round_pair (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (i j : Fin n) (hij : i ≠ j) :
    (round u p hp).moment (fun q => point q i*point q j) ≤ point p i*point p j := by
  have hh := ((SparseSignedPartial.run u p n).bindCompress_spec (kernel u p hp)
    features).2.2 (finSumFinEquiv (Sum.inr (finProdFinEquiv (i,j))))
  simp only [features_pair,kernel,RationalSignedTerminal.terminal_pair _ _ _ _ _ hij] at hh
  exact hh.trans_le (SparseSignedPartial.run_pair u p n i j hij)

theorem round_invariants (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (hu : ∀ i, 0 < u i → u i ≤ 1)
    (a : Fin (round u p hp).length) :
    let q := (round u p hp).states[a.val]
    (∀ i, 0 ≤ point q i ∧ point q i ≤ 1) ∧ (fractional q).card ≤ 1 ∧
    (∑ i, u i*point q i) ≤ (∑ i, u i*point p i)+1 := by
  obtain ⟨b,c,hbc⟩ := ((SparseSignedPartial.run u p n).bindCompress_spec
    (kernel u p hp) features).2.1 a
  dsimp only
  change (round u p hp).states[a.val]=_ at hbc
  rw [hbc]
  have hh := RationalSignedTerminal.terminal_spec u (SparseSignedPartial.run u p n).states[b.val]
    (SparseSignedPartial.run_invariants u p hp n b).1 hu
    (SparseSignedPartial.run_terminal u p hp b) c
  dsimp only at hh
  exact ⟨hh.1,hh.2.1,hh.2.2.trans_eq
    (congrArg (fun z : ℚ => z+1) (SparseSignedPartial.run_invariants u p hp n b).2.1)⟩

theorem round_spec (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (hu : ∀ i, 0 < u i → u i ≤ 1) :
    let μ := round u p hp
    μ.length ≤ n+n*n+1 ∧
    (∀ a : Fin μ.length, (∀ i, 0 ≤ point μ.states[a.val] i ∧ point μ.states[a.val] i ≤ 1) ∧
      (fractional μ.states[a.val]).card ≤ 1 ∧
      (∑ i, u i*point μ.states[a.val] i) ≤ (∑ i, u i*point p i)+1) ∧
    (∀ i, μ.moment (fun q => point q i)=point p i) ∧
    (∀ i j, i ≠ j → μ.moment (fun q => point q i*point q j) ≤ point p i*point p j) :=
  ⟨round_length u p hp,round_invariants u p hp hu,round_mean u p hp,round_pair u p hp⟩

end MetricKMedian.SparseSignedRounding
end
end

end OAI
