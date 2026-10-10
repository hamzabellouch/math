import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseAlgorithm
import OAI.Combinatorics.KMedian.Sparse.SparseMarginalTools
import OAI.Combinatorics.KMedian.Rounding.RationalWeightedInvariants

namespace OAI

section
section
namespace MetricKMedian.SparseWeightedPartial
open Finset RationalWeightedStep
variable {n : ℕ}

def features (p : Vector ℚ n) (a : Fin (n+n*n)) : ℚ :=
  Sum.elim (point p) (fun ij : Fin (n*n) =>
    point p (finProdFinEquiv.symm ij).1*point p (finProdFinEquiv.symm ij).2)
    (finSumFinEquiv.symm a)

@[simp] theorem features_single (p : Vector ℚ n) (i : Fin n) :
    features p (finSumFinEquiv (Sum.inl i))=point p i := by
  simp only [features,Equiv.symm_apply_apply,Sum.elim_inl]

@[simp] theorem features_pair (p : Vector ℚ n) (i j : Fin n) :
    features p (finSumFinEquiv (Sum.inr (finProdFinEquiv (i,j))))=point p i*point p j := by
  simp only [features,Equiv.symm_apply_apply,Sum.elim_inr]

 def step (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (μ : SparseIntegerLaw (Vector ℚ n)) : SparseIntegerLaw (Vector ℚ n) :=
  μ.step features (probability β) (probability_unit β hβ) (endpoint β)

 theorem step_mean (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (μ : SparseIntegerLaw (Vector ℚ n)) (i : Fin n) :
    (step β hβ μ).moment (fun p => point p i)=μ.moment (fun p => point p i) := by
  have hh := μ.step_moment features (probability β) (probability_unit β hβ)
    (endpoint β) (finSumFinEquiv (Sum.inl i))
  simp only [features_single] at hh
  exact hh.trans (μ.moment_congr _ _ (fun a => endpoint_mean β hβ _ i))

 theorem step_pair (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (μ : SparseIntegerLaw (Vector ℚ n)) (i j : Fin n) (hij : i ≠ j) :
    (step β hβ μ).moment (fun p => point p i*point p j) ≤
      μ.moment (fun p => point p i*point p j) := by
  have hh := μ.step_moment features (probability β) (probability_unit β hβ)
    (endpoint β) (finSumFinEquiv (Sum.inr (finProdFinEquiv (i,j))))
  simp only [features_pair] at hh
  exact hh.trans_le (μ.moment_mono _ _ (fun k => endpoint_pair β hβ _ i j hij))

 def run (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i) (p : Vector ℚ n) :
    ℕ → SparseIntegerLaw (Vector ℚ n)
  | 0 => .dirac p
  | t+1 => step β hβ (run β hβ p t)

 theorem run_mean (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (t : ℕ) (i : Fin n) :
    (run β hβ p t).moment (fun q => point q i)=point p i := by
  induction t with
  | zero => exact SparseIntegerLaw.dirac_moment _ _
  | succ t ih => rw [run,step_mean,ih]

 theorem run_pair (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (t : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (run β hβ p t).moment (fun q => point q i*point q j) ≤ point p i*point p j := by
  induction t with
  | zero => exact (SparseIntegerLaw.dirac_moment _ _).le
  | succ t ih => exact (step_pair β hβ _ i j hij).trans ih

 theorem run_length (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (t : ℕ) : (run β hβ p t).length ≤ n+n*n+1 := by
  cases t with
  | zero => change 1 ≤ _; omega
  | succ t => exact ((run β hβ p t).branch (probability β)
      (probability_unit β hβ) (endpoint β)).compressAuto_correct features |>.1

 theorem run_invariants (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (t : ℕ) :
    ∀ a : Fin (run β hβ p t).length,
      let q := (run β hβ p t).states[a.val]
      (∀ i, 0 ≤ point q i ∧ point q i ≤ 1) ∧
      (∑ i, β i*point q i)=∑ i, β i*point p i ∧
      (fractional q).card ≤ max (n-t) 1 := by
  induction t with
  | zero =>
    intro a
    have he : (run β hβ p 0).states[a.val]=p := SparseIntegerLaw.dirac_states p a
    dsimp only
    rw [he]
    refine ⟨hp,rfl,?_⟩
    have hh := card_le_card (filter_subset (fun i : Fin n => 0 < point p i ∧ point p i < 1) univ)
    simp only [card_univ,Fintype.card_fin] at hh
    exact hh.trans (le_max_left _ _)
  | succ t ih =>
    apply (run β hβ p t).step_property features (probability β)
      (probability_unit β hβ) (endpoint β)
      (fun q => (∀ i, 0 ≤ point q i ∧ point q i ≤ 1) ∧
        (∑ i, β i*point q i)=∑ i, β i*point p i ∧
        (fractional q).card ≤ max (n-(t+1)) 1)
    intro a b
    obtain ⟨ha0,ha1,ha2⟩ := ih a
    refine ⟨endpoint_feasible β hβ _ ha0 b,(endpoint_weighted β hβ _ b).trans ha1,?_⟩
    by_cases h : 1 < (fractional (run β hβ p t).states[a.val]).card
    · have hh := endpoint_smaller β hβ _ h b
      omega
    · simp only [endpoint,dite_eq_right h]
      omega

end MetricKMedian.SparseWeightedPartial
end
end

end OAI
