import OAI.NumberTheory.TwoPoint.Circuits.CircuitComparison
import OAI.NumberTheory.TwoPoint.Bounds.CRTComparison
import Mathlib.Data.Nat.Choose.Bounds

namespace OAI

/-!
# Counting low-order Fourier coefficients

The number of nonempty coordinate sets of order at most `t` is at most
`(t+1)n^t`. Combining individual coefficient bounds with this count gives
the explicit error budget used by finite residue comparison.
-/

namespace TwoPointCorrelations

open Finset

lemma card_lowWalshSets_le {n : ℕ} (hn : 0 < n) (t : ℕ) :
    (lowWalshSets n t).card ≤ (t + 1) * n ^ t := by
  have hsub : lowWalshSets n t ⊆ (Finset.range (t + 1)).biUnion
      (fun k => (Finset.univ : Finset (Fin n)).powersetCard k) := by
    intro S hS
    have ht := (Finset.mem_filter.mp hS).2.2
    apply Finset.mem_biUnion.mpr
    refine ⟨S.card, Finset.mem_range.mpr (by omega), ?_⟩
    simp
  calc
    (lowWalshSets n t).card ≤ ((Finset.range (t + 1)).biUnion
        (fun k => (Finset.univ : Finset (Fin n)).powersetCard k)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.range (t + 1), ((Finset.univ : Finset (Fin n)).powersetCard k).card :=
      Finset.card_biUnion_le
    _ = ∑ k ∈ Finset.range (t + 1), n.choose k := by simp
    _ ≤ ∑ _k ∈ Finset.range (t + 1), n ^ t := by
      apply Finset.sum_le_sum
      intro k hk
      exact (Nat.choose_le_pow n k).trans (Nat.pow_le_pow_right hn (by
        have := Finset.mem_range.mp hk
        omega))
    _ = (t + 1) * n ^ t := by simp

lemma lowWalshMass_le_of_coefficients {n : ℕ} (hn : 0 < n)
    (f : BooleanCube n → ℝ) (t : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hf : ∀ S ∈ lowWalshSets n t, |walshCoefficient f S| ≤ δ) :
    lowWalshMass f t ≤ δ * ((t + 1 : ℕ) : ℝ) * (n : ℝ) ^ t := by
  unfold lowWalshMass
  calc
    (∑ S ∈ lowWalshSets n t, |walshCoefficient f S|) ≤ ∑ _S ∈ lowWalshSets n t, δ :=
      Finset.sum_le_sum hf
    _ = δ * ((lowWalshSets n t).card : ℝ) := by simp [mul_comm]
    _ ≤ δ * (((t + 1) * n ^ t : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast card_lowWalshSets_le hn t) hδ
    _ = _ := by push_cast; ring

/-- The fixed-parameter finite-law consequence of Braverman's theorem:
only the individual low-order Fourier errors and the actual circuit size
and depth occur as hypotheses. -/
theorem BravermanDepth22Input.coefficient_comparison (hBraverman : BravermanDepth22Input) :
    ∃ K C : ℕ, 0 < K ∧ 0 < C ∧ ∀ (n : ℕ), 0 < n →
      ∀ (c : AC0Circuit n), c.depth ≤ 22 →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ t : ℕ,
        (K : ℝ) * (Real.log ((c.size : ℝ) / ε)) ^ C ≤ (t : ℝ) →
        ∀ (f : BooleanCube n → ℝ) (δ a : ℝ),
          (∀ x, 0 ≤ f x) → cubeAverage f = 1 → 0 ≤ δ →
          (∀ S ∈ lowWalshSets n t, |walshCoefficient f S| ≤ δ) →
          δ * ((t + 1 : ℕ) : ℝ) * (n : ℝ) ^ t ≤ a →
          |cubeAverage (fun x => f x * c.indicator x) - cubeAverage c.indicator| ≤
            3 * a / 2 + ε := by
  obtain ⟨K, C, hK, hC, hbound⟩ := hBraverman.fourier_comparison
  refine ⟨K, C, hK, hC, ?_⟩
  intro n hn c hc ε hε hεmax t ht f δ a hf hmean hδ hcoeff ha
  have hmass := lowWalshMass_le_of_coefficients hn f t δ hδ hcoeff
  have ha0 : 0 ≤ a := le_trans (by positivity) ha
  exact hbound n c hc ε hε hεmax t ht f a hf hmean ha0 (hmass.trans ha)

end TwoPointCorrelations

end OAI
