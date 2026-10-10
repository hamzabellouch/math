import Mathlib
import OAI.Combinatorics.TriangleRemoval.Queries.MarkedSuccess

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

@[simp] theorem markedGood_bind {α : Type*} [Fintype α] (π : PMF α)
    (p : α → PMF (Bool × Bool)) :
    markedGood (π.bind p) = pmfMean π (fun a => markedGood (p a)) :=
  pmfMean_bind π p _

noncomputable def prospectiveFailure (N : ℕ) [NeZero N] (t : ℕ) (q : Fin N → ℝ) : ℝ :=
  1 - (∑ u : Fin N, if u.val < t then q u else 0) / (N : ℝ)

theorem markedRow_cavity_bound {K : Type*} [Fintype K] [DecidableEq K]
    (N : ℕ) [NeZero N] (S : Finset K) (σ : K → Fin N)
    (p : K → Fin N → PMF (Bool × Bool)) (q : K → Fin N → ℝ)
    (deadline t : ℕ) (htd : t ≤ deadline) (hsel : ∀ k ∈ S, (σ k).val < deadline)
    (ht : ∃ k ∈ S, t ≤ (σ k).val) (hS : S.card ≤ 2)
    (hmarg : ∀ k ∉ S, ∀ u, markedSuccess (p k u) = q k u)
    (b : ℝ) (hfactor : ∀ k, (7 / 8 : ℝ) ≤ prospectiveFailure N t (q k))
    (hfull : ∏ k, prospectiveFailure N t (q k) ≤ (9 / 8 : ℝ) * b) :
    markedGood ((productPMF (selectedClockLaw N S σ)).bind
      (fun ω => markedCheck (markedRow S p deadline ω))) ≤
      (∏ k ∈ S, markedGood (p k (σ k))) * (2 * b) := by
  rw [markedGood_bind]
  have h := markedRow_integrated N S σ p deadline t htd hsel ht
  let f : K → ℝ := fun k => prospectiveFailure N t (q k)
  have he : (∏ k, if k ∈ S then markedGood (p k (σ k)) else
      1 - (∑ u : Fin N, if u.val < t then markedSuccess (p k u) else 0) / (N : ℝ)) =
      (∏ k ∈ S, markedGood (p k (σ k))) * (∏ k ∈ Finset.univ \ S, f k) := by
    have hp : (fun k => if k ∈ S then markedGood (p k (σ k)) else
        1 - (∑ u : Fin N, if u.val < t then markedSuccess (p k u) else 0) / (N : ℝ)) =
        (fun k => if k ∈ S then markedGood (p k (σ k)) else f k) := by
      funext k
      by_cases hk : k ∈ S
      · simp only [hk,↓reduceIte]
      · simp only [hk,↓reduceIte,f,prospectiveFailure,hmarg k hk]
    rw [hp,Finset.prod_ite]
    congr 1
    · congr 1
      ext k
      simp
    · congr 1
      ext k
      simp
  rw [he] at h
  have hf := offpattern_product_bound Finset.univ S (Finset.subset_univ S) hS f b
    (fun k _ => hfactor k) hfull
  exact h.trans (mul_le_mul_of_nonneg_left hf (Finset.prod_nonneg
    (fun k _ => markedGood_nonneg (p k (σ k)))))

@[simp] theorem markedGood_no_marks (p : PMF Bool) :
    markedGood (p.map (fun b => (b,true))) = 1 := by
  rw [markedGood,pmfMean_map]
  simp only [↓reduceIte,pmfMean_const]

@[simp] theorem markedSuccess_no_marks (p : PMF Bool) :
    markedSuccess (p.map (fun b => (b,true))) = (p true).toReal := by
  rw [markedSuccess,pmfMean_map]
  simp [pmfMean]

end SharpTerminalLeave

end

end OAI
