import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.BilateralBetaWitnesses
import OAI.Analysis.RieszRectifiability.Foundations.CappedLowerSupportTubes
import OAI.Analysis.RieszRectifiability.Flatness.LocalFlatBallTransfer
import OAI.Analysis.RieszRectifiability.Limits.CompactSupportApproximants

namespace OAI

/-!
# Flat balls under compact-test convergence

Capped lower growth supplies local support control along a converging sequence of measures.
Bilateral approximation by an affine plane then transfers flat balls to nearby centers of
the approximating measures, and persistent bad balls impose a lower beta bound on the limit.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem compactTestConvergence_capped_flat_ball {d : ℕ} (n : ℕ) (C H : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (hC : 0 < C) (hH : 0 < H)
    (hlower : ∀ j, CappedLowerGrowth n C H (μ j))
    (a : Ambient d) (ha : a ∈ ν.support) (b : ℕ → Ambient d) (hb : Tendsto b atTop (𝓝 a))
    (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S)
    (hforward : ∀ x ∈ ball a (2 * r), x ∈ ν.support → infDist x (S : Set (Ambient d)) < ε * r / 16)
    (hreverse : ∀ x ∈ ball a (2 * r), x ∈ S → infDist x ν.support < ε * r / 16) :
    ∀ᶠ j in atTop, bilateralBeta n (μ j) (b j) r < ε := by
  have hmargin : ε * r / 16 ≤ r / 4 := by nlinarith [mul_le_mul_of_nonneg_right hε1 hr.le]
  filter_upwards [compactTestConvergence_capped_bilateral_tubes n C H μ ν hlocal hC hH hlower
    a (2 * r) (ε * r / 16) (by positivity),
    Metric.tendsto_nhds.mp hb (r / 4) (by positivity)] with j hj hjb
  have ht := local_bilateral_tube_transfer ν.support (μ j).support (S : Set (Ambient d))
    ⟨a, ha⟩ a (b j) r (ε * r / 16) (ε * r / 16) hr hmargin hmargin hjb.le
    hj.1 hj.2 hforward hreverse
  apply bilateralBeta_lt_of_support_tubes n (μ j) (b j) r ε hr hε S hS
  · intro x hx hxs
    have hp := ht.1 x hx hxs
    nlinarith [mul_pos hε hr]
  · intro x hx hxs
    have hp := ht.2 x hx hxs
    nlinarith [mul_pos hε hr]

theorem compactTestConvergence_capped_beta_lower {n d : ℕ} (hnd : n ≤ d) (C H : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (hC : 0 < C) (hH : 0 < H)
    (hlower : ∀ j, CappedLowerGrowth n C H (μ j))
    (U : Set (Ambient d)) (hU : IsOpen U) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (r : ℝ) (hr : 0 < r)
    (hbad : ∀ᶠ j in atTop, ∀ b ∈ (μ j).support, b ∈ U → ε ≤ bilateralBeta n (μ j) b r)
    (a : Ambient d) (ha : a ∈ ν.support) (haU : a ∈ U) :
    ε / 64 ≤ bilateralBeta n ν a (2 * r) := by
  by_contra hnot
  obtain ⟨S, hS, he⟩ := exists_bilateral_plane_error_lt hnd ν a (2 * r) (ε / 64) (lt_of_not_ge hnot)
  have hp := bilateralPlaneError_lt_pointwise ν ⟨a, ha⟩ a (2 * r) (ε / 64) (by positivity) S hS he
  have hforward : ∀ x ∈ ball a (2 * r), x ∈ ν.support →
      infDist x (S : Set (Ambient d)) < ε * r / 16 := by
    intro x hx hxs
    have ht := hp.1 x hx hxs
    nlinarith [mul_pos hε hr]
  have hreverse : ∀ x ∈ ball a (2 * r), x ∈ S → infDist x ν.support < ε * r / 16 := by
    intro x hx hxs
    have ht := hp.2 x hx hxs
    nlinarith [mul_pos hε hr]
  obtain ⟨φ, b, _, hφ, hbs, hb⟩ := compactTestConvergence_support_approximants μ ν hlocal a ha
  let : ∀ j, IsFiniteMeasureOnCompacts ((μ ∘ φ) j) :=
    fun j => inferInstanceAs (IsFiniteMeasureOnCompacts (μ (φ j)))
  have hc : CompactTestConvergence (μ ∘ φ) ν := fun f => (hlocal f).comp hφ
  have ht := compactTestConvergence_capped_flat_ball n C H (μ ∘ φ) ν hc hC hH
    (fun j => hlower (φ j)) a ha b hb r ε hr hε hε1 S hS hforward hreverse
  obtain ⟨j, hjflat, hjbad, hjU⟩ :=
    (ht.and ((hφ.eventually hbad).and (hb.eventually (hU.mem_nhds haU)))).exists
  exact (not_lt_of_ge (hjbad (b j) (hbs j) hjU)) hjflat

end

end RieszRectifiability

end OAI
