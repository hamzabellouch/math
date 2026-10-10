import OAI.Geometry.CylinderCovering.Rational.CostActual
import OAI.Geometry.CylinderCovering.Rational.Padding

namespace OAI

noncomputable section
open Asymptotics Filter
open scoped Topology

namespace SlopeRational

theorem weightedCost_vanishing_padding_expansion {d : ℝ} (hd : 0 < d) :
    (fun ε : ℝ => weightedCost d ε (ε ^ (5 / 2 : ℝ)) / physicalScale -
      (1 / 8 - (energyIntegral d - ceilingIntegral d) * ε ^ 2))
      =o[𝓝[>] 0] (fun ε => ε ^ (2 : ℕ)) := by
  have hq0 : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 ≤ ε ^ (5 / 2 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (Real.rpow_pos_of_pos hε _).le
  have hq := CylinderCovering.RationalPadding.vanishing_padding_rates.1
  have hr := (weightedCost_expansion hd hq0 hq.isBigO).trans_isLittleO
    ((isLittleO_pow_pow (𝕜 := ℝ) (show 2 < 4 by norm_num)).mono nhdsWithin_le_nhds)
  exact (hr.add (hq.const_mul_left (1 / 2 : ℝ))).congr_left (fun ε => by ring)

theorem weightedCost_quadratic_padding_expansion {d η : ℝ}
    (hd : 0 < d) (hη : 0 ≤ η) :
    (fun ε : ℝ => weightedCost d ε (η * ε ^ 2) / physicalScale -
      (1 / 8 - (energyIntegral d - ceilingIntegral d - η / 2) * ε ^ 2))
      =O[𝓝[>] 0] (fun ε => ε ^ (4 : ℕ)) := by
  have hq0 : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 ≤ η * ε ^ 2 :=
    Filter.Eventually.of_forall (fun ε => mul_nonneg hη (sq_nonneg ε))
  have hq := (isBigO_refl (fun ε : ℝ => ε ^ (2 : ℕ)) (𝓝[>] (0 : ℝ))).const_mul_left η
  exact (weightedCost_expansion hd hq0 hq).congr_left (fun ε => by ring)

theorem quadratic_coefficient_limit_of_littleO {C : ℝ → ℝ} {A B : ℝ}
    (hrem : (fun ε => C ε - (A + B * ε ^ 2))
      =o[𝓝[>] 0] (fun ε : ℝ => ε ^ (2 : ℕ))) :
    Tendsto (fun ε => (C ε - A) / ε ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 B) := by
  have ht := hrem.tendsto_div_nhds_zero.add_const B
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : 0 < ε := hε
  field_simp [hεpos.ne']
  ring

theorem weightedCost_vanishing_padding_coefficient {d : ℝ} (hd : 0 < d) :
    Tendsto (fun ε : ℝ =>
      (weightedCost d ε (ε ^ (5 / 2 : ℝ)) / physicalScale - 1 / 8) / ε ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (ceilingIntegral d - energyIntegral d)) := by
  apply quadratic_coefficient_limit_of_littleO
  exact (weightedCost_vanishing_padding_expansion hd).congr_left (fun ε => by ring)

theorem weightedCost_quadratic_padding_coefficient {d η : ℝ}
    (hd : 0 < d) (hη : 0 ≤ η) :
    Tendsto (fun ε : ℝ =>
      (weightedCost d ε (η * ε ^ 2) / physicalScale - 1 / 8) / ε ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (ceilingIntegral d - energyIntegral d + η / 2)) := by
  apply quadratic_coefficient_limit_of_littleO
  have hr := (weightedCost_quadratic_padding_expansion hd hη).trans_isLittleO
    ((isLittleO_pow_pow (𝕜 := ℝ) (show 2 < 4 by norm_num)).mono nhdsWithin_le_nhds)
  exact hr.congr_left (fun ε => by ring)

end SlopeRational

end

end OAI
