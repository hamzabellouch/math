import Mathlib
import OAI.Analysis.RieszRectifiability.Projections.ProjectionRegionChildAssembly

namespace OAI

/-!
# Finite-depth projection-region charts

Iterating child assembly yields a bounded chart with recursively controlled Lipschitz
constant. A fixed fractional stop-mass bound gives a geometric uncovered-mass bound
at each finite depth.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def projectionRegionDepthConstant (d : ℕ) (L : ℝ≥0) : ℕ → ℝ≥0
  | 0 => 1
  | J + 1 => projectionRegionAssemblyConstant d L (projectionRegionDepthConstant d L J)

theorem exists_projection_region_depth_chart {n d : ℕ}
    (ν : Measure (Ambient d)) (L : ℝ≥0) (hL : 1 ≤ L) (θ : ℝ)
    (hregions : ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets ν R hR k).points),
      ∃ Good : SupportCellDescendant ν R hR k z → Prop,
        ∃ P : Submodule ℝ (Ambient d), Module.finrank ℝ P = n ∧
          (∀ x ∈ cellRegionRepresentatives ν R hR k z Good,
            ∀ y ∈ cellRegionRepresentatives ν R hR k z Good,
              dist x y ≤ (L : ℝ) * dist (P.starProjection x) (P.starProjection y)) ∧
          (∑' i : cellRegionStops ν R hR k z Good, ν i.val.cell) ≤
            ENNReal.ofReal (1 - θ) * ν (cleanSupportCell ν R hR k z))
    (J : ℕ) :
    ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets ν R hR k).points),
      ∃ g : ball (0 : Ambient n) (latticeRadius R k) → Ambient d,
        LipschitzWith (projectionRegionDepthConstant d L J) g ∧
        Set.range g ⊆ closedBall (z : Ambient d) (2 * latticeRadius R k) ∧
        ν (cleanSupportCell ν R hR k z \ Set.range g) ≤
          (ENNReal.ofReal (1 - θ)) ^ J * ν (cleanSupportCell ν R hR k z) := by
  induction J with
  | zero =>
    intro R hR k z
    refine ⟨fun _ => (z : Ambient d), ?_, ?_, ?_⟩
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [dist_self]
      positivity
    · rintro y ⟨u, rfl⟩
      exact mem_closedBall_self (by have hr := latticeRadius_pos R hR k; positivity)
    · simpa only [pow_zero, one_mul] using!
        (measure_mono sdiff_subset (μ := ν)
          (s := cleanSupportCell ν R hR k z \ Set.range (fun _ : ball (0 : Ambient n) (latticeRadius R k) => (z : Ambient d))))
  | succ J ih =>
    intro R hR k z
    obtain ⟨Good, P, hdim, hsep, hstop⟩ := hregions R hR k z
    let F := cellRegionStops ν R hR k z Good
    have hchildren (i : F) := ih R hR (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩
    choose child hLip himage hloss using hchildren
    obtain ⟨g, hg, hgrange, _, _, hdeficit⟩ := exists_projection_region_child_assembly
      ν R hR k z Good P hdim L hL hsep child (projectionRegionDepthConstant d L J) hLip himage
    refine ⟨g, hg, hgrange, hdeficit.trans ?_⟩
    calc
      _ ≤ ∑' i : F, (ENNReal.ofReal (1 - θ)) ^ J * ν i.val.cell :=
        ENNReal.tsum_le_tsum hloss
      _ = (ENNReal.ofReal (1 - θ)) ^ J * ∑' i : F, ν i.val.cell := ENNReal.tsum_mul_left
      _ ≤ (ENNReal.ofReal (1 - θ)) ^ J *
          (ENNReal.ofReal (1 - θ) * ν (cleanSupportCell ν R hR k z)) := mul_le_mul' le_rfl hstop
      _ = _ := by rw [pow_succ, mul_assoc]

end

end RieszRectifiability

end OAI
