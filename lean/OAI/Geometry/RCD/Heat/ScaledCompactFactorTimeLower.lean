import OAI.Geometry.RCD.Metric.CompactFactorTimeMonotone
import OAI.Geometry.RCD.Metric.CompactFactorCenteredCompactness
import OAI.Geometry.RCD.Heat.ScaledTimeError

namespace OAI

/-! # Vanishing one-sided time error for the actual scaled heat potentials

The estimate is independent of the positive endpoint scaling factor. It
controls decreases in forward time, with an explicit error of order ε.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem scaled_compact_heat_potential_time_lower (hK : K≤0)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0≤ρ x) {C : ℝ≥0}
    (hC : ∀ᵐ x ∂hausdorff n X, |ρ x|≤C)
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : C(S, ℝ)) (hF : ∀ a, 0<F a) {ε s t : ℝ}
    (hε : 0<ε) (hs : 0<s) (hst : s≤t) (x : X) :
    hX.scaledCompactHeatPotential hn p ν F ε s (by positivity) x-
      hX.scaledCompactHeatPotential hn p ν F ε t
        (div_pos (mul_pos hε (hs.trans_le hst)) (by norm_num)) x ≤
      (n:ℝ)*ε*Real.log (t/s)+(n:ℝ)*|K| *ε^2*(t-s)/2 := by
  have ha : 0<ε*s/2 := by positivity
  have hb : 0<ε*t/2 := div_pos (mul_pos hε (hs.trans_le hst)) (by norm_num)
  have hab : ε*s/2≤ε*t/2 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hst hε.le) (by norm_num)
  have hh := mul_le_mul_of_nonneg_left
    (hX.compact_heat_factor_log_time_lower hn p hK ν ρ hρ hρ0 hC hν F hF ha hab x) hε.le
  have hratio : Real.log (ε*t/2)-Real.log (ε*s/2)=Real.log (t/s) := by
    rw [←Real.log_div hb.ne' ha.ne']
    congr 1
    field_simp
  change ε*Real.log _-ε*Real.log _≤_
  calc
    _ = ε*(Real.log (hX.compactHeatFactor hn p ν F (ε*s/2) ha x)-
        Real.log (hX.compactHeatFactor hn p ν F (ε*t/2) hb x)) := by ring
    _ ≤ ε*((n:ℝ)*(Real.log (ε*t/2)-Real.log (ε*s/2)+|K| *(ε*t/2-ε*s/2))) := hh
    _ = _ := by rw [hratio]; ring

theorem scaled_compact_heat_potential_interior_time_lower (hK : K≤0)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0≤ρ x) {C : ℝ≥0}
    (hC : ∀ᵐ x ∂hausdorff n X, |ρ x|≤C)
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : C(S, ℝ)) (hF : ∀ a, 0<F a) {ε δ s t : ℝ}
    (hε : 0<ε) (hε1 : ε≤1) (hδ : 0<δ) (hδs : δ≤ s) (hst : s≤t) (x : X) :
    hX.scaledCompactHeatPotential hn p ν F ε s
        (div_pos (mul_pos hε (hδ.trans_le hδs)) (by norm_num)) x-
      hX.scaledCompactHeatPotential hn p ν F ε t
        (div_pos (mul_pos hε (hδ.trans_le (hδs.trans hst))) (by norm_num)) x ≤
      ε*((n:ℝ)/δ+(n:ℝ)*|K|/2)*(t-s) := by
  exact (hX.scaled_compact_heat_potential_time_lower hn p hK ν ρ hρ hρ0 hC hν F hF
    hε (hδ.trans_le hδs) hst x).trans
    (scaled_log_time_error (Nat.cast_nonneg n) (abs_nonneg K) hε.le hε1 hδ hδs hst)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
