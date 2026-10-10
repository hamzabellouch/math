import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseWeightedPartial
import OAI.Combinatorics.KMedian.Rounding.RationalLastFraction

namespace OAI

section
section
namespace MetricKMedian.SparseWeightedRounding
open Finset RationalWeightedStep SparseWeightedPartial
variable {n : ℕ}

def round (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i) (p : Vector ℚ n) :
    SparseIntegerLaw (Vector ℚ n) :=
  (run β hβ p n).step features RationalLastFraction.probability
    RationalLastFraction.probability_unit RationalLastFraction.endpoint

theorem round_mean (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (i : Fin n) :
    (round β hβ p).moment (fun q => point q i)=point p i := by
  have hh := (run β hβ p n).step_moment features RationalLastFraction.probability
    RationalLastFraction.probability_unit RationalLastFraction.endpoint
    (finSumFinEquiv (Sum.inl i))
  simp only [features_single] at hh
  exact hh.trans (((run β hβ p n).moment_congr _ _
    (fun a => RationalLastFraction.endpoint_mean _ i)).trans (run_mean β hβ p n i))

theorem round_pair (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (i j : Fin n) (hij : i ≠ j) :
    (round β hβ p).moment (fun q => point q i*point q j) ≤ point p i*point p j := by
  have hh := (run β hβ p n).step_moment features RationalLastFraction.probability
    RationalLastFraction.probability_unit RationalLastFraction.endpoint
    (finSumFinEquiv (Sum.inr (finProdFinEquiv (i,j))))
  simp only [features_pair] at hh
  exact hh.trans_le (((run β hβ p n).moment_congr _ _
    (fun a => RationalLastFraction.endpoint_pair _ i j hij)).trans_le (run_pair β hβ p n i j hij))

theorem round_length (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) : (round β hβ p).length ≤ n+n*n+1 :=
  ((run β hβ p n).branch RationalLastFraction.probability
    RationalLastFraction.probability_unit RationalLastFraction.endpoint).compressAuto_correct features |>.1

theorem round_invariants (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1)
    {M : ℚ} (hM : 0 ≤ M) (hβM : ∀ i, β i ≤ M) :
    ∀ a : Fin (round β hβ p).length,
      let q := (round β hβ p).states[a.val]
      (∀ i, point q i=0 ∨ point q i=1) ∧
      |(∑ i, β i*point q i)-(∑ i, β i*point p i)| ≤ M := by
  apply (run β hβ p n).step_property features RationalLastFraction.probability
    RationalLastFraction.probability_unit RationalLastFraction.endpoint
    (fun q => (∀ i, point q i=0 ∨ point q i=1) ∧
      |(∑ i, β i*point q i)-(∑ i, β i*point p i)| ≤ M)
  intro a b
  obtain ⟨ha,hb,hc⟩ := run_invariants β hβ p hp n a
  have hc' : (fractional (run β hβ p n).states[a.val]).card ≤ 1 := by simpa using hc
  refine ⟨RationalLastFraction.endpoint_integral _ ha hc' b,?_⟩
  have hh := RationalLastFraction.endpoint_noise (run β hβ p n).states[a.val] β
    (fun k => (hβ k).le) hβM hM b
  rwa [hb] at hh

theorem round_spec (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1)
    {M : ℚ} (hM : 0 ≤ M) (hβM : ∀ i, β i ≤ M) :
    let μ := round β hβ p
    μ.length ≤ n+n*n+1 ∧
    (∀ a : Fin μ.length, (∀ i, point μ.states[a.val] i=0 ∨ point μ.states[a.val] i=1) ∧
      |(∑ i, β i*point μ.states[a.val] i)-(∑ i, β i*point p i)| ≤ M) ∧
    (∀ i, μ.moment (fun q => point q i)=point p i) ∧
    (∀ i j, i ≠ j → μ.moment (fun q => point q i*point q j) ≤ point p i*point p j) :=
  ⟨round_length β hβ p,round_invariants β hβ p hp hM hβM,
    round_mean β hβ p,round_pair β hβ p⟩

end MetricKMedian.SparseWeightedRounding
end
end

end OAI
