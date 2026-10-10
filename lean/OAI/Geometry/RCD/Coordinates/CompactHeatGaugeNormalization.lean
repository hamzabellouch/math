import OAI.Geometry.RCD.Metric.FixedGaugeScaledPotential

namespace OAI

/-! # Positive endpoint scaling realizes the fixed additive heat gauge -/

open Set Filter MeasureTheory TopologicalSpace
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compactHeatFactor_smul {S : Set X} [CompactSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (F : C(S,ℝ))
    (a t : ℝ) (ht : 0 < t) (x : X) :
    hX.compactHeatFactor hn p ν (a • F) t ht x =
      a*hX.compactHeatFactor hn p ν F t ht x := by
  change (∫ y, hX.compactHeatFactorKernel hn p S t ht (x,y)*(a*F y) ∂ν) =
    a*(∫ y, hX.compactHeatFactorKernel hn p S t ht (x,y)*F y ∂ν)
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun _ => by ring

theorem fixedGaugeScaledPotential_normalized {S : Set X} [CompactSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (F : C(S,ℝ)) (hF : ∀ y, 0 < F y)
    {ε δ t : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (ht : δ ≤ t) (z : X) :
    ∃ G : C(S,ℝ), (∀ y, 0 < G y) ∧ ∀ x,
      hX.fixedGaugeScaledPotential hn p ν F ε hε δ hδ z t x =
        ε*Real.log (hX.compactHeatFactor hn p ν G (ε*t/2)
          (div_pos (mul_pos hε (hδ.trans_le ht)) (by norm_num)) x) := by
  let c := hX.compactHeatFactor hn p ν F ε hε z
  have hc : 0 < c := hX.compactHeatFactor_positive hn p ν F hF ε hε z
  refine ⟨c⁻¹ • F,fun y => mul_pos (inv_pos.mpr hc) (hF y),?_⟩
  intro x
  rw [hX.fixedGaugeScaledPotential_eq hn p ν F ε hε δ hδ z ht x]
  dsimp only [scaledCompactHeatPotential]
  rw [hX.compactHeatFactor_smul,Real.log_mul (inv_ne_zero hc.ne')
    (hX.compactHeatFactor_positive hn p ν F hF _ _ x).ne',Real.log_inv]
  dsimp only [c]
  ring

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
