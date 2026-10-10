import OAI.Analysis.Brenier.CanonicalPaths
import OAI.Analysis.Brenier.ClosedPaths
import OAI.Analysis.Brenier.Coordinates
import OAI.Analysis.Brenier.MapTransport
import OAI.Analysis.Brenier.MovingBoundary
import OAI.Analysis.Brenier.PlaneEnvelopes
import OAI.Analysis.Brenier.SharpSlices
import OAI.Analysis.Brenier.Sharpness
import OAI.Analysis.Brenier.SliceInterpolation

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Problem358

theorem one_third_stability :
    ∀ (d : ℕ) (K Y : Set (E d)),
      2 ≤ d → IsCompact K → Convex ℝ K → (interior K).Nonempty →
      IsCompact Y → Y.Nonempty →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (μ ν : Measure (E d)),
          IsProbabilityMeasure μ → IsProbabilityMeasure ν →
          IsSupported μ Y → IsSupported ν Y →
          ∃ Tμ Tν : E d → E d,
            IsUniqueQuadraticOptimalMap (uniformMeasure K) μ Tμ ∧
            IsUniqueQuadraticOptimalMap (uniformMeasure K) ν Tν ∧
            mapL2Dist (uniformMeasure K) Tμ Tν ≤
              C * Real.rpow (wasserstein2 μ ν) (1 / 3 : ℝ) := by
  intro d K Y _hd hK hKconv hKint hY hYne
  obtain ⟨R, hRpos, hKR⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨L, hLpos, hYL⟩ := hY.isBounded.exists_pos_norm_le
  let Rn : ℝ≥0 := ⟨R, hRpos.le⟩
  let Ln : ℝ≥0 := ⟨L, hLpos.le⟩
  have hxR : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ Rn := by
    filter_upwards [UniformSource.ae_mem hK.measurableSet] with x hx
    exact hKR x hx
  apply one_third_stability_of_closedCell_intercept_paths hK hKconv hKint hY hYne
    Rn Ln hxR hYL (κ := 162) (by norm_num)
  intro n hn m y z hm hsum _hyL _hzL hinj
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact FixedMassIntercepts.exists_actual_atomic_intercept_path hK hKconv hKint
    m hm hsum y z Rn hxR (fun t ht => hinj t ht.1 ht.2)

theorem one_third_exponent_is_sharp :
    ∀ (d : ℕ), 2 ≤ d → ∀ α : ℝ, (1 / 3 : ℝ) < α →
      ∀ C : ℝ, 0 < C →
        ∃ (μ ν : Measure (E d)) (Tμ Tν : E d → E d),
          IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
          IsSupported μ (cube d) ∧ IsSupported ν (cube d) ∧
          HasExactlyThreeAtoms μ (cube d) ∧ HasExactlyThreeAtoms ν (cube d) ∧
          μ ≠ ν ∧
          IsUniqueQuadraticOptimalMap (uniformMeasure (cube d)) μ Tμ ∧
          IsUniqueQuadraticOptimalMap (uniformMeasure (cube d)) ν Tν ∧
          0 < wasserstein2 μ ν ∧
          C * Real.rpow (wasserstein2 μ ν) α <
            mapL2Dist (uniformMeasure (cube d)) Tμ Tν := by
  exact one_third_exponent_is_sharp_via_rectangle

end Problem358

end

end OAI
