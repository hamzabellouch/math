import Mathlib
import OAI.Combinatorics.KMedian.Compression.ComputedCompressionStep

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

def compressSteps {n d : ℕ} (v : Fin n → Fin d → ℤ) (L : ℕ)
    (hv : ∀ i j, |v i j| ≤ (2:ℤ)^L) : ℕ → IntegerLaw (Fin n) → IntegerLaw (Fin n)
  | 0, μ => μ
  | t+1, μ =>
    if h : d+1 < μ.support.card then
      compressSteps v L hv t (compressionStep μ v L hv h)
    else μ

theorem compressSteps_spec {n d : ℕ} (v : Fin n → Fin d → ℤ) (L : ℕ)
    (hv : ∀ i j, |v i j| ≤ (2:ℤ)^L) (t : ℕ) (μ : IntegerLaw (Fin n))
    (hμ : μ.support.card ≤ t+(d+1)) :
    let ν := compressSteps v L hv t μ
    ν.denominator ≤ μ.denominator*(2:ℤ)^(((2*(d+1)*(d+1+L))*(n+1))*t) ∧
      ν.support ⊆ μ.support ∧ ν.support.card ≤ d+1 ∧
      ∀ j, (∑ i, ν.rational.weight i*(v i j:ℚ))=∑ i, μ.rational.weight i*(v i j:ℚ) := by
  induction t generalizing μ with
  | zero =>
    dsimp only [compressSteps]
    refine ⟨?_,Subset.rfl,by omega,fun _ => rfl⟩
    simp only [Nat.mul_zero,pow_zero,mul_one,le_refl]
  | succ t ih =>
    dsimp only
    by_cases h : d+1 < μ.support.card
    · rw [compressSteps,dite_eq_left h]
      let ν := compressionStep μ v L hv h
      have hs := compressionStep_spec μ v L hv h
      have hν : ν.support.card ≤ t+(d+1) := by
        dsimp only [ν]
        have hh := hs.2.2.1
        omega
      have hi := ih ν hν
      refine ⟨?_,hi.2.1.trans hs.2.1,hi.2.2.1,fun j => (hi.2.2.2 j).trans (hs.2.2.2 j)⟩
      let Z := ((2*(d+1)*(d+1+L))*(n+1))
      calc
        _ ≤ ν.denominator*(2:ℤ)^(Z*t) := hi.1
        _ ≤ (μ.denominator*(2:ℤ)^Z)*(2:ℤ)^(Z*t) :=
          mul_le_mul_of_nonneg_right hs.1 (by positivity)
        _ = μ.denominator*(2:ℤ)^(Z*(t+1)) := by
          rw [mul_assoc,← pow_add]
          congr 2
          ring
    · rw [compressSteps,dite_eq_right h]
      refine ⟨?_,Subset.rfl,by omega,fun _ => rfl⟩
      exact le_mul_of_one_le_right μ.denominator_pos.le (one_le_pow₀ (by norm_num))

def computedCompress {n d : ℕ} (μ : IntegerLaw (Fin n)) (v : Fin n → Fin d → ℤ)
    (L : ℕ) (hv : ∀ i j, |v i j| ≤ (2:ℤ)^L) : IntegerLaw (Fin n) :=
  compressSteps v L hv n μ

theorem computedCompress_spec {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℤ) (L : ℕ) (hv : ∀ i j, |v i j| ≤ (2:ℤ)^L) :
    let ν := computedCompress μ v L hv
    ν.denominator ≤ μ.denominator*(2:ℤ)^(((2*(d+1)*(d+1+L))*(n+1))*n) ∧
      ν.support ⊆ μ.support ∧ ν.support.card ≤ d+1 ∧
      ∀ j, (∑ i, ν.rational.weight i*(v i j:ℚ))=∑ i, μ.rational.weight i*(v i j:ℚ) := by
  apply compressSteps_spec
  exact (card_le_univ _).trans ((Fintype.card_fin n).trans_le (Nat.le_add_right _ _))

end MetricKMedian.IntegerLaw

end OAI
