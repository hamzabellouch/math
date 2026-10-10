import OAI.Analysis.CircleDomains.Topology.NestedJordanLimits
import OAI.Analysis.CircleDomains.Topology.HorizontalFrontierCrossings

namespace OAI

/-!
# Crossing segments persist in converging finite models

Anchored convergence of the inner and outer Jordan contours retains a
fixed compact subset of the inner fill and the strict nesting. Their
prescribed zero/one boundary values then yield crossings over the same
fixed projection set for all sufficiently late models.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem eventually_crossings_of_anchored_jordan_limits
    (H K : ℂ ≃ₜ ℂ) (Hn Kn : ℕ → ℂ ≃ₜ ℂ)
    (γ δ : Circle → ℂ) (γn δn : ℕ → Circle → ℂ)
    (hγ : Continuous γ) (hδ : Continuous δ)
    (hγfront : range γ = frontier (jordanInterior H))
    (hδfront : range δ = frontier (jordanInterior K))
    (hγn : ∀ᶠ n in atTop, range (γn n) = frontier (jordanInterior (Hn n)))
    (hδn : ∀ᶠ n in atTop, range (δn n) = frontier (jordanInterior (Kn n)))
    (hγlim : TendstoUniformly γn γ atTop) (hδlim : TendstoUniformly δn δ atTop)
    (hHK : closure (jordanInterior H) ⊆ jordanInterior K)
    {z w : ℂ} {zn wn : ℕ → ℂ}
    (hz : z ∈ jordanInterior H) (hw : w ∈ jordanInterior K)
    (hzn : Tendsto zn atTop (𝓝 z)) (hwn : Tendsto wn atTop (𝓝 w))
    (hzanchor : ∀ᶠ n in atTop, zn n ∈ jordanInterior (Hn n))
    (hwanchor : ∀ᶠ n in atTop, wn n ∈ jordanInterior (Kn n))
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ jordanInterior H)
    (D : ℕ → Set ℂ) (v : ℕ → ℂ → ℝ) {L : ℝ}
    (hbound : ∀ᶠ n in atTop, closure (jordanInterior (Kn n)) ⊆ closedBall 0 L)
    (hboundary : ∀ᶠ n in atTop, frontier (jordanInterior (Hn n)) ⊆ D n ∧
      frontier (jordanInterior (Kn n)) ⊆ D n)
    (hvalues : ∀ᶠ n in atTop,
      (∀ p ∈ frontier (jordanInterior (Kn n)), v n p = 0) ∧
      (∀ p ∈ frontier (jordanInterior (Hn n)), v n p = 1))
    {J : Set ℝ} (hJ : J ⊆ Complex.im '' C) :
    ∀ᶠ n in atTop, ∀ y ∈ J, ∃ a b : ℝ, a < b ∧ horizontalLine y a ∈ D n ∧
      horizontalLine y b ∈ D n ∧ horizontalLine y a ∈ closedBall 0 L ∧
      horizontalLine y b ∈ closedBall 0 L ∧ v n (horizontalLine y a) = 0 ∧
      v n (horizontalLine y b) = 1 := by
  have hretain := eventually_compact_subset_jordanInterior_of_anchor H Hn γ γn
    hγ hγfront hγn hγlim hz hzn hzanchor hC hCH
  have hnested := eventually_nested_jordanInteriors_of_anchor H K Hn Kn γ δ γn δn
    hγ hδ hγfront hδfront hγn hδn hγlim hδlim hHK hw hwn hwanchor
  filter_upwards [hretain, hnested, hbound, hboundary, hvalues] with n hnC hnested hnB hnD hnv
  apply horizontal_frontier_crossings_give_values
    (jordanInterior_isOpen (Hn n)) (jordanInterior_isOpen (Kn n))
    (isCompact_closure_jordanInterior (Hn n)) (isCompact_closure_jordanInterior (Kn n))
    hnested hnB hnD.2 hnD.1 hnv.1 hnv.2
  exact hJ.trans (image_mono (hnC.trans subset_closure))

end CircleDomainRigidity

end

end OAI
