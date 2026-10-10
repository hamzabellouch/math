import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.CellBadCountRebase
import OAI.Analysis.RieszRectifiability.Restart.BadDepthAndRestartLossBudget

namespace OAI

/-!
# Bad-cell count budgets inside a support cell

Removing a multiplicity tail leaves a measurable set with uniformly bounded bad-cell counts
relative to every descendant. A zero count forbids all bad descendants containing the point,
and hence places that point in the corresponding good-region limit.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem original_AD_Riesz_cell_bad_count_budget {p d : ℕ} (hnd : p + 1 ≤ d)
    (μ : Measure (Ambient d)) [μ.Regular] (hAD : ADRegular (p + 1) μ)
    (hRiesz : RieszL2Bounded (p + 1) μ) (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ N : ℕ, 0 < N ∧ ∀ (R : ℝ) (hR : 0 < R) (k : ℕ)
      (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      ∃ A : Set (Ambient d), MeasurableSet A ∧ A ⊆ cleanSupportCell μ R hR k z ∧
        μ (cleanSupportCell μ R hR k z \ A) ≤ ENNReal.ofReal ζ * μ (cleanSupportCell μ R hR k z) ∧
        ∀ x ∈ A, ∀ q : SupportCellDescendant μ R hR k z,
          cellBadCountBound (fun i => ε ≤ bilateralBeta (p + 1) μ i.center (H * i.radius)) q N x := by
  classical
  obtain ⟨N, hN, htail⟩ := original_AD_Riesz_bad_depth_loss_budget hnd μ hAD hRiesz H ε hH hε ζ hζ
  refine ⟨N, hN, ?_⟩
  intro R hR k z hcore
  let A := {x ∈ cleanSupportCell μ R hR k z |
    badBetaMultiplicity (p + 1) μ R hR k z H ε x < (N : ℝ≥0∞)}
  have hAmeas : MeasurableSet A := (cleanSupportCell_measurable μ R hR k z).inter
    (measurableSet_lt (badBetaMultiplicity_measurable (p + 1) μ R hR k z H ε) measurable_const)
  have hsub : cleanSupportCell μ R hR k z \ A ⊆
      {x | (N : ℝ≥0∞) ≤ badBetaMultiplicity (p + 1) μ R hR k z H ε x} := by
    intro x hx
    by_contra hn
    exact hx.2 ⟨hx.1, lt_of_not_ge hn⟩
  refine ⟨A, hAmeas, fun _ hx => hx.1, (measure_mono hsub).trans (htail R hR k z hcore), ?_⟩
  intro x hx q
  apply cellBadCountBound_of_subtype_incidence_bound _ q N x
  intro F hF
  have hcount : (F.card : ℝ≥0∞) ≤ badBetaMultiplicity (p + 1) μ R hR k z H ε x := by
    calc
      _ = ∑ i ∈ F, i.val.cell.indicator (fun _ => (1 : ℝ≥0∞)) x := by
        symm
        calc
          _ = ∑ _i ∈ F, (1 : ℝ≥0∞) :=
            Finset.sum_congr rfl (fun i hi => Set.indicator_of_mem (hF i hi) _)
          _ = _ := by simp
      _ ≤ _ := ENNReal.sum_le_tsum F
  exact_mod_cast hcount.trans hx.2.le

theorem zero_bad_count_mem_relative_region_limit {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points) (H ε : ℝ)
    (q : SupportCellDescendant μ R hR k z) (x : Ambient d) (hx : x ∈ q.cell)
    (hcount : cellBadCountBound (fun i => ε ≤ bilateralBeta n μ i.center (H * i.radius)) q 0 x) :
    x ∈ cellRegionLimit μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩
      (fun i => bilateralBeta n μ i.center (H * i.radius) < ε) := by
  refine ⟨hx, ?_⟩
  intro j hxj
  have hdepth : q.depth ≤ (q.compose j).depth := by
    rw [SupportCellDescendant.compose_depth]
    omega
  have hsub : (q.compose j).cell ⊆ q.cell := by
    rw [SupportCellDescendant.compose_cell]
    exact j.cell_subset_top
  have hxj' : x ∈ (q.compose j).cell := by
    rw [SupportCellDescendant.compose_cell]
    exact hxj
  have hgood := not_le.mp (cellBadCountBound_zero_forbids_bad_descendant
    (fun i => ε ≤ bilateralBeta n μ i.center (H * i.radius)) q (q.compose j) hdepth hsub x hxj' hcount)
  change bilateralBeta n μ j.center (H * (q.compose j).radius) < ε at hgood
  rwa [SupportCellDescendant.compose_radius] at hgood

end

end RieszRectifiability

end OAI
