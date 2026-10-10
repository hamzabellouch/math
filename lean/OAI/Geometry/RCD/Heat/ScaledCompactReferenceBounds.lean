import OAI.Geometry.RCD.Metric.CompactFactorBackwardRatio
import OAI.Geometry.RCD.Heat.ScaledReferenceError
import OAI.Geometry.RCD.Heat.ScaledCompactFactorTimeLower

namespace OAI

/-! # Fixed-reference amplitude bounds for the actual scaled heat potentials

The additive gauge is fixed once at time ε. All interior times use that
same gauge, uniformly over the positive endpoint factor.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem scaled_compact_heat_reference_bounds (hK : K≤0) :
    ∃ C D : ℝ, 0≤C ∧ 0<D ∧
      ∀ {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
        (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0≤ρ x) {B : ℝ≥0},
        (∀ᵐ x ∂hausdorff n X, |ρ x|≤B) →
        ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)) →
        ∀ (F : C(S, ℝ)), (∀ a, 0<F a) →
        ∀ {ε δ s : ℝ} (hε : 0<ε), ε≤1 → (hδ : 0<δ) → (hδs : δ≤ s) → s≤1 →
        ∀ (z : X) (R : ℝ), 0≤R → (∀ a : S, dist z a≤R) →
        let v := hX.scaledCompactHeatPotential hn p ν F ε s
          (div_pos (mul_pos hε (hδ.trans_le hδs)) (by norm_num)) z-
          ε*Real.log (hX.compactHeatFactor hn p ν F ε hε z);
        -(C+2*D*R^2/δ)≤v ∧ v≤(n:ℝ)*(2/δ+|K|) := by
  obtain ⟨C,D,hC,hD,hback⟩ := hX.compact_heat_factor_log_backward_time_ratio hn p
  refine ⟨C,D,hC,hD,?_⟩
  intro S _ ν _ ρ hρ hρ0 B hB hν F hF ε δ s hε hε1 hδ hδs hs1 z R hR hdist
  have hs : 0<s := hδ.trans_le hδs
  have ha : 0<ε*s/2 := by positivity
  have hae : ε*s/2≤ε := by nlinarith only [mul_le_mul_of_nonneg_left hs1 hε.le,hε]
  have hb := hback ν F hF (ε*s/2) ε ha hae hε1 z R hR hdist
  have hl := hX.compact_heat_factor_log_time_lower hn p hK ν ρ hρ hρ0 hB hν F hF ha hae z
  have hb' := mul_le_mul_of_nonneg_left hb hε.le
  have hl' := mul_le_mul_of_nonneg_left hl hε.le
  have hlow := scaled_reference_lower_error hC hD.le hε hε1 hδ hδs (R:=R)
  have hupp := scaled_reference_upper_error (Nat.cast_nonneg n) (abs_nonneg K) hε hε1 hδ hδs
  change -(C+2*D*R^2/δ)≤ε*Real.log _-ε*Real.log _ ∧
    ε*Real.log _-ε*Real.log _≤(n:ℝ)*(2/δ+|K|)
  constructor
  · nlinarith only [hb',hlow]
  · nlinarith only [hl',hupp]

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
