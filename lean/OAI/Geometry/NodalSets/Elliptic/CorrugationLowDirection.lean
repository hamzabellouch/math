import OAI.Geometry.NodalSets.Charts.MetricNormalizationStabilityLemmas
import OAI.Geometry.NodalSets.Elliptic.CorrugationLeadingLength

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

theorem corrugation_low_leading_direction {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ (g : Coord →L[ℝ] Coord →L[ℝ] ℝ), ‖g‖ ≤ M →
      (∀ v, c*‖v‖^2 ≤ g v v) →
      ∀ (e : Coord ≃L[ℝ] Coord),
      (∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      ∀ (amp t : ℝ) (z : ℝ × ℝ), 0 ≤ amp → 0 ≤ t →
      t*corrugationSlope amp (1/4) (corrugationCellRadius z) ≤ δ →
      ‖metricNormalize g (corrugationLeadingVector amp t e z)-e (Pi.single 0 1)‖ ≤
        C*(t*corrugationSlope amp (1/4) (corrugationCellRadius z)) := by
  let K : ℝ := 1+c⁻¹
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨ε₀,B,hε₀,hB,hstab⟩ := metric_normalization_uniform_stability hM hK.le
  let Q : ℝ := 4*K
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨ε₀/Q,B*Q,div_pos hε₀ hQ,mul_pos hB hQ,?_⟩
  intro g hg hco e he amp t z ha ht hsmall
  have hunit : g (e (Pi.single 0 1)) (e (Pi.single 0 1)) = 1 := by simpa using he 0 0
  have haxis := metric_unit_coordinate_bound g hc hco _ hunit
  have hl := corrugationSlope_nonneg (R := (1/4:ℝ)) ha (corrugationCellRadius_properties z).1
  have hε : 0 ≤ Q*(t*corrugationSlope amp (1/4) (corrugationCellRadius z)) := by positivity
  have hd : ‖corrugationLeadingVector amp t e z-e (Pi.single 0 1)‖ ≤
      Q*(t*corrugationSlope amp (1/4) (corrugationCellRadius z)) := by
    rw [corrugationLeadingVector,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]
    apply (mul_le_mul_of_nonneg_left (corrugationFastVector_bound g hc hco ha e he z) ht).trans_eq
    dsimp [Q,K]
    ring
  have heps : Q*(t*corrugationSlope amp (1/4) (corrugationCellRadius z)) ≤ ε₀ := by
    have hh := (le_div_iff₀ hQ).mp hsmall
    nlinarith only [hh]
  have hh := (hstab g g (corrugationLeadingVector amp t e z) (e (Pi.single 0 1))
    (Q*(t*corrugationSlope amp (1/4) (corrugationCellRadius z))) hg haxis hunit.ge hd
    (by
      apply ContinuousLinearMap.opNorm_le_bound _ hε
      intro v
      have hz : (g-g) v = 0 := by ext u; simp
      rw [hz, norm_zero]
      positivity) heps).2.2
  rw [metricNormalize_fixed g _ hunit] at hh
  convert hh using 1
  ring

end
end Yau.Geometry

end OAI
