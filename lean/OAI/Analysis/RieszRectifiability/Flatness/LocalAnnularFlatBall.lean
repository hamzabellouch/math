import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.CappedNonflatTangents
import OAI.Analysis.RieszRectifiability.Foundations.AnnularDimensionTermination

namespace OAI

/-!
# Local flat balls from annular bounds

Local smooth annular control and capped lower growth force arbitrarily small balls
with small bilateral beta number. Otherwise a tangent inherits global nonflatness and
annular control, contradicting termination of the supporting-plane dimension drop.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem exists_local_flat_ball_of_annular_bound {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d)
    (C G H B annCap : ℝ) (μ : Measure (Ambient d)) (hC : 0 < C) (hH : 0 < H)
    (hg : GlobalUpperGrowth n G μ) (hlower : CappedLowerGrowth n C H μ)
    (U : Set (Ambient d)) (hU : IsOpen U) (a : Ambient d) (ha : a ∈ μ.support) (haU : a ∈ U)
    (hAnnCap : 0 < annCap)
    (hbound : ∀ x ∈ μ.support, x ∈ U → ∀ r R : ℝ, ∀ hr : 0 < r, ∀ hrR : r ≤ R,
      R < annCap → ‖smoothAnnularTransform n μ x r R hr (hr.trans_le hrR)‖ ≤ B)
    (flatCap ε : ℝ) (hflatCap : 0 < flatCap) (hε : 0 < ε) :
    ∃ b ∈ μ.support, b ∈ U ∧ ∃ r : ℝ, 0 < r ∧ r < flatCap ∧ bilateralBeta n μ b r < ε := by
  by_contra hnone
  let s := fun j : ℕ => H * (1 / 2 : ℝ) ^ j
  have hs (j : ℕ) : 0 < s j := by dsimp only [s]; positivity
  have hsH (j : ℕ) : s j ≤ H := by
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num)) hH.le).trans_eq (mul_one H)
  have hs0 : Tendsto s atTop (𝓝 0) := by
    simpa only [mul_zero] using!
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul H
  obtain ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, _, hlowerν⟩ :=
    exists_capped_lower_tangent n C G H μ hC hH hg hlower a ha s hs hsH hs0
  let := hfinite
  have hBν : GlobalSmoothAnnularBound n ν B :=
    GlobalSmoothAnnularBound.of_local_tangent n G B annCap μ ν hg U hU a haU hAnnCap
      (fun j => s (ρ j)) (fun j => hs (ρ j)) (hs0.comp hρ.tendsto_atTop) hlocal hbound
  have hbad : ∀ x ∈ μ.support, x ∈ U → ∀ r : ℝ, 0 < r → r < flatCap →
      min ε 1 ≤ bilateralBeta n μ x r := by
    intro x hx hxU r hr hrcap
    apply (min_le_left ε 1).trans
    exact le_of_not_gt (fun hb => hnone ⟨x, hx, hxU, r, hr, hrcap, hb⟩)
  have hbadν := global_bilateral_lower_of_capped_tangent hnd C G H flatCap (min ε 1) μ ν
    hC hg hlower U hU a haU (fun j => s (ρ j)) (fun j => hs (ρ j)) (fun j => hsH (ρ j))
    (hs0.comp hρ.tendsto_atTop) hlocal hflatCap (lt_min hε zero_lt_one) (min_le_right _ _) hbad
  exact not_global_nonflat_annular_measure hn hnd ν hne (C * 4 ^ n) (G * 2 ^ n) B
    (min ε 1 / 64) (by positivity) hgν hlowerν hBν
    (by positivity) (by linarith [min_le_right ε 1]) hbadν

end

end RieszRectifiability

end OAI
