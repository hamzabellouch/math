import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.LocalWeakCappedTransform
import OAI.Analysis.RieszRectifiability.Limits.WeakTransformInterior

namespace OAI

/-!
# Local L² representatives of interior pairings

Weak limits of capped transforms on ball restrictions represent the interior Riesz
pairing. The resulting representative retains the quantitative L² bound inherited
from the approximating measures.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem exists_local_L2_interior_representative {d : ℕ} (p : ℕ) (C G : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hgrowth : ∀ j, GlobalUpperGrowth (p + 1) C (μ j))
    (hgν : GlobalUpperGrowth (p + 1) G ν) (hweak : CompactTestConvergence μ ν)
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 (μ j) →
      MemLp (truncated (p + 1) (μ j) ε f) 2 (μ j) ∧
        eLpNorm (truncated (p + 1) (μ j) ε f) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm f 2 (μ j))
    (a : Ambient d) (R : ℝ)
    (hboundary : ν (frontier (ball a R)) = 0) (hmass : ν (ball a R) ≠ 0) (e : Ambient d) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      Tendsto (fun j => (1 / 2 : ℝ) ^ (ρ j)) atTop (𝓝 0) ∧
      ∃ v : Lp ℝ 2 (ν.restrict (ball a R)),
        ‖v‖ ≤ (Real.toNNReal (‖e‖ * ((D : ℝ) + C * 2 ^ (p + 1))) : ℝ) *
          Real.sqrt (ν.real (ball a R)) ∧
        (∀ g : Ambient d → ℝ, MemLp g 2 (ν.restrict (ball a R)) →
          Tendsto (fun j => ∫ x in ball a R,
            scalarCappedTransform (p + 1) (ν.restrict (ball a R)) e ((1 / 2 : ℝ) ^ (ρ j))
              (fun _ => 1) x * g x ∂ν) atTop (𝓝 (∫ x in ball a R, v x * g x ∂ν))) ∧
        ∀ (φ : Ambient d → ℝ) (L B : ℝ≥0), LipschitzWith L φ →
          (∀ x, |φ x| ≤ (B : ℝ)) →
          (∫ x in ball a R, v x * φ x ∂ν) = (1 / 2 : ℝ) *
            (∫ q, rieszInteriorIntegrand (p + 1) e φ q
              ∂(ν.restrict (ball a R)).prod (ν.restrict (ball a R))) := by
  have hcompact : IsCompact (closure (ball a R)) :=
    (isCompact_closedBall a R).of_isClosed_subset isClosed_closure
      (closure_minimal ball_subset_closedBall isClosed_closedBall)
  let := relativelyCompact_restrict_finite ν (ball a R) hcompact
  obtain ⟨ρ, hρ, hεlim, v, hv, hlim⟩ := exists_local_weak_transform_of_source_L2
    (p + 1) (by omega) C μ ν hgrowth hweak D hB a R hboundary hmass e
  refine ⟨ρ, hρ, hεlim, v, hv, hlim, ?_⟩
  intro φ L B hφ hBφ
  exact weak_transform_represents_interior p G (ν.restrict (ball a R))
    (globalGrowth_restrict (p + 1) G ν hgν (ball a R)) e
    (fun j => (1 / 2 : ℝ) ^ (ρ j)) (fun _ => by positivity) hεlim v hlim φ L B hφ hBφ

end

end RieszRectifiability

end OAI
