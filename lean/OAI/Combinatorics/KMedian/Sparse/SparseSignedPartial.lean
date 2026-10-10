import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseWeightedPartial
import OAI.Combinatorics.KMedian.Rounding.RationalSignedStep

namespace OAI

section
section
namespace MetricKMedian.SparseSignedPartial
open Finset RationalSignedStep
open RationalWeightedStep (point fractional)
open SparseWeightedPartial (features features_single features_pair)
variable {n : ℕ}

 def step (β : Fin n → ℚ) 
    (μ : SparseIntegerLaw (Vector ℚ n)) : SparseIntegerLaw (Vector ℚ n) :=
  μ.step features (probability β) (probability_unit β) (endpoint β)

 theorem step_mean (β : Fin n → ℚ) 
    (μ : SparseIntegerLaw (Vector ℚ n)) (i : Fin n) :
    (step β μ).moment (fun p => point p i)=μ.moment (fun p => point p i) := by
  have hh := μ.step_moment features (probability β) (probability_unit β)
    (endpoint β) (finSumFinEquiv (Sum.inl i))
  simp only [features_single] at hh
  exact hh.trans (μ.moment_congr _ _ (fun a => endpoint_mean β _ i))

 theorem step_pair (β : Fin n → ℚ) 
    (μ : SparseIntegerLaw (Vector ℚ n)) (i j : Fin n) (hij : i ≠ j) :
    (step β μ).moment (fun p => point p i*point p j) ≤
      μ.moment (fun p => point p i*point p j) := by
  have hh := μ.step_moment features (probability β) (probability_unit β)
    (endpoint β) (finSumFinEquiv (Sum.inr (finProdFinEquiv (i,j))))
  simp only [features_pair] at hh
  exact hh.trans_le (μ.moment_mono _ _ (fun k => endpoint_pair β _ i j hij))

 def run (β : Fin n → ℚ) (p : Vector ℚ n) :
    ℕ → SparseIntegerLaw (Vector ℚ n)
  | 0 => .dirac p
  | t+1 => step β (run β p t)

 theorem run_mean (β : Fin n → ℚ) 
    (p : Vector ℚ n) (t : ℕ) (i : Fin n) :
    (run β p t).moment (fun q => point q i)=point p i := by
  induction t with
  | zero => exact SparseIntegerLaw.dirac_moment _ _
  | succ t ih => rw [run,step_mean,ih]

 theorem run_pair (β : Fin n → ℚ) 
    (p : Vector ℚ n) (t : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (run β p t).moment (fun q => point q i*point q j) ≤ point p i*point p j := by
  induction t with
  | zero => exact (SparseIntegerLaw.dirac_moment _ _).le
  | succ t ih => exact (step_pair β _ i j hij).trans ih

 theorem run_length (β : Fin n → ℚ) 
    (p : Vector ℚ n) (t : ℕ) : (run β p t).length ≤ n+n*n+1 := by
  cases t with
  | zero => change 1 ≤ _; omega
  | succ t => exact ((run β p t).branch (probability β)
      (probability_unit β) (endpoint β)).compressAuto_correct features |>.1

theorem run_invariants (β : Fin n → ℚ)
    (p : Vector ℚ n) (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (t : ℕ) :
    ∀ a : Fin (run β p t).length,
      let q := (run β p t).states[a.val]
      (∀ i, 0 ≤ point q i ∧ point q i ≤ 1) ∧
      (∑ i, β i*point q i)=∑ i, β i*point p i ∧
      ((fractional q).card ≤ n-t ∨ ¬Active β q) := by
  induction t with
  | zero =>
    intro a
    have he : (run β p 0).states[a.val]=p := SparseIntegerLaw.dirac_states p a
    dsimp only
    rw [he]
    refine ⟨hp,rfl,Or.inl ?_⟩
    have hh := card_le_card (filter_subset (fun i : Fin n => 0 < point p i ∧ point p i < 1) univ)
    simpa only [fractional,card_univ,Fintype.card_fin,Nat.sub_zero] using hh
  | succ t ih =>
    apply (run β p t).step_property features (probability β)
      (probability_unit β) (endpoint β)
      (fun q => (∀ i, 0 ≤ point q i ∧ point q i ≤ 1) ∧
        (∑ i, β i*point q i)=∑ i, β i*point p i ∧
        ((fractional q).card ≤ n-(t+1) ∨ ¬Active β q))
    intro a b
    obtain ⟨ha0,ha1,ha2⟩ := ih a
    refine ⟨endpoint_feasible β _ ha0 b,(endpoint_weighted β _ b).trans ha1,?_⟩
    by_cases h : Active β (run β p t).states[a.val]
    · have hh := endpoint_smaller β _ h b
      rcases ha2 with ha2 | ha2
      · exact Or.inl (by omega)
      · exact False.elim (ha2 h)
    · simp only [endpoint,dite_eq_right h]
      exact Or.inr h

theorem run_terminal (β : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (a : Fin (run β p n).length) :
    ¬Active β (run β p n).states[a.val] := by
  rcases (run_invariants β p hp n a).2.2 with h | h
  · intro ha
    have hi := (pair β (run β p n).states[a.val] ha).property.1
    have hc := card_pos.mpr ⟨_,hi⟩
    omega
  · exact h

end MetricKMedian.SparseSignedPartial
end
end

end OAI
