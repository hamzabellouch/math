import OAI.Analysis.CircleDomains.LengthArea
import Mathlib.Analysis.Normed.Group.Tannery

namespace OAI

/-!
# Vanishing terminal-count bounds for finite transfer

In the Koebe manuscript's finite-transfer estimate `eq:transfer-terminal-mean`,
the scaled expected terminal count is bounded by a finite-cardinality
term and finitely many series of clipped oscillation products.
Square-summability of the oscillations makes these products summable,
and dominated convergence makes the bound tend to zero as the grid
spacing tends to zero through positive values.
-/

open Filter
open scoped Topology

namespace CircleDomainRigidity.FiniteTransfer

/-- Clipping two nonnegative oscillations at a nonnegative grid spacing
preserves the summable mixed-product majorant. -/
theorem min_mul_min_norm_le {ι : Type*} {a b : ι → ℝ} {h : ℝ}
    (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s) (hh : 0 ≤ h) (s : ι) :
    ‖min h (a s) * min h (b s)‖ ≤ a s * b s := by
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (le_min hh (ha s)) (le_min hh (hb s)))]
  exact mul_le_mul (min_le_right _ _) (min_le_right _ _)
    (le_min hh (hb s)) (ha s)

/-- Each clipped-product series is summable at every nonnegative spacing. -/
theorem summable_min_mul_min {ι : Type*} {a b : ι → ℝ} {h : ℝ}
    (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s)
    (ha2 : Summable (fun s => a s ^ 2)) (hb2 : Summable (fun s => b s ^ 2))
    (hh : 0 ≤ h) : Summable (fun s => min h (a s) * min h (b s)) :=
  (LengthArea.summable_mul_of_squares ha2 hb2).of_norm_bounded
    (min_mul_min_norm_le ha hb hh)

/-- Dominated convergence for the clipped oscillation products in the
terminal-count estimate. -/
theorem tendsto_tsum_min_mul_min_zero {ι : Type*} {a b : ι → ℝ}
    (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s)
    (ha2 : Summable (fun s => a s ^ 2)) (hb2 : Summable (fun s => b s ^ 2)) :
    Tendsto (fun h : ℝ => ∑' s, min h (a s) * min h (b s))
      (𝓝[>] 0) (𝓝 0) := by
  have hid : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hpoint : ∀ s, Tendsto (fun h : ℝ => min h (a s) * min h (b s))
      (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    intro s
    have hmina : Tendsto (fun h : ℝ => min h (a s)) (𝓝[>] 0) (𝓝 (min 0 (a s))) :=
      hid.min tendsto_const_nhds
    have hminb : Tendsto (fun h : ℝ => min h (b s)) (𝓝[>] 0) (𝓝 (min 0 (b s))) :=
      hid.min tendsto_const_nhds
    simpa only [min_eq_left (ha s), min_eq_left (hb s), zero_mul] using
      hmina.mul hminb
  have hpos : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
  have hbound : ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ s,
      ‖min h (a s) * min h (b s)‖ ≤ a s * b s := by
    filter_upwards [hpos] with h hh
    exact min_mul_min_norm_le ha hb hh.le
  simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence
    (LengthArea.summable_mul_of_squares ha2 hb2) hpoint hbound

/-- The complete finite-family bound in `eq:transfer-terminal-mean`
vanishes with the positive grid spacing. `P` can be the finite family of
coordinate pairs `i < j`, and `F` the prescribed finite terminal set. -/
theorem terminal_mean_bound_tendsto_zero {κ τ ι : Type*}
    (F : Finset κ) (P : Finset τ) (a b : τ → ι → ℝ)
    (ha : ∀ p ∈ P, ∀ s, 0 ≤ a p s) (hb : ∀ p ∈ P, ∀ s, 0 ≤ b p s)
    (ha2 : ∀ p ∈ P, Summable (fun s => a p s ^ 2))
    (hb2 : ∀ p ∈ P, Summable (fun s => b p s ^ 2)) :
    Tendsto (fun h : ℝ => h ^ 2 * (F.card : ℝ) +
      ∑ p ∈ P, ∑' s, min h (a p s) * min h (b p s)) (𝓝[>] 0) (𝓝 0) := by
  have hid : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hfinite := tendsto_finsetSum P (fun p hp =>
    tendsto_tsum_min_mul_min_zero (ha p hp) (hb p hp) (ha2 p hp) (hb2 p hp))
  have hcard := (hid.pow 2).mul (tendsto_const_nhds (x := (F.card : ℝ)))
  simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, Finset.sum_const_zero,
    zero_add] using hcard.add hfinite

end CircleDomainRigidity.FiniteTransfer

end OAI
