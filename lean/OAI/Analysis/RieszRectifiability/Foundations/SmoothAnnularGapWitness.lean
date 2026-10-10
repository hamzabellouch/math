import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.SmoothAnnularIntegrability

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem exists_uniform_smooth_annular_gap_direction {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (G L : ℝ) (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (a : Ambient d) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (S : Set (Ambient d)) (hS : MeasurableSet S) (hSfin : μ S < ∞)
    (hcontains : ball a (2 * R) ⊆ S)
    (A Q : Set (Ambient d)) (hA : MeasurableSet A) (hQ : MeasurableSet Q)
    (hAfin : μ A < ∞) (hQfin : μ Q < ∞) (hApos : 0 < μ.real A) (hQpos : 0 < μ.real Q)
    (hAnear : ∀ x ∈ A, 2 * dist x a ≤ r) (hQnear : ∀ x ∈ Q, 2 * dist x a ≤ R)
    (hAmass : r ^ n ≤ L * μ.real A) (hQmass : R ^ n ≤ L * μ.real Q)
    (D : ℝ≥0)
    (hRiesz : ∀ ε : ℝ, 0 < ε → ∀ u : Ambient d → ℝ, MemLp u 2 μ →
      MemLp (truncated n μ ε u) 2 μ ∧
        eLpNorm (truncated n μ ε u) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm u 2 μ) :
    ∃ e : Ambient d, ‖e‖ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε < r / 2 →
      ‖smoothAnnularTransform n μ a r R hr (hr.trans_le hrR)‖ -
        (3 * ((D : ℝ) ^ 2 * (G * 2 ^ n * L) + 1) + 3 * exteriorCellMeanConstant n G 1) ≤
      |cellMean (μ.restrict A) (fun x => inner ℝ e
          (truncated n μ ε (S.indicator (fun _ => 1)) x)) -
        cellMean (μ.restrict Q) (fun x => inner ℝ e
          (truncated n μ ε (S.indicator (fun _ => 1)) x))| := by
  obtain ⟨e, he, hev⟩ := exists_unit_bounded_norm_direction
    (smoothAnnularTransform n μ a r R hr (hr.trans_le hrR))
  refine ⟨e, he, ?_⟩
  intro ε hε hεr
  have hb := smooth_annular_indicator_cell_comparison n hn G L μ hg a e he r R ε hr hrR hε hεr
    S hS hSfin hcontains A Q hA hQ hAfin hQfin hApos hQpos hAnear hQnear
    hAmass hQmass D (hRiesz ε hε)
  rw [hev, abs_of_nonneg (norm_nonneg _)] at hb
  linarith

end

end RieszRectifiability

end OAI
