import OAI.MeasureTheory.Falconer.Radial.RadialMeanPowerBound
import OAI.MeasureTheory.Falconer.Radial.RadialCollisionDeletion

namespace OAI

/-! # Power-small original-pair deletion on an outer profile interval -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem outer_radial_interval_pruning {D η q : ℝ}
    (hD : 1 ≤ D) (hη : 0 < η) (hq : 0 ≤ q) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ g k : ℕ, k ≤ N →
      ∀ (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (G : Set (Space d × Space d)), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → x ≠ z) →
      (∀ᵐ z ∂μ,
        (∀ᵐ y ∂μ, ‖y-z‖ < 1/(2:ℝ)^g ∧ ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D) ∧
        (∀ j : ℕ, j ≤ g+k → μ {y | ‖y-z‖ < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((((2:ℝ)^N)^η*((2:ℝ)^g)^q)*(1/(2:ℝ)^j)^q)) ∧
        (∀ r : ℝ, 1/(2:ℝ)^(g+k) ≤ r → r ≤ 1 → ∀ u : Space d, ‖u‖ = 1 →
          ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
            ENNReal.ofReal (((2:ℝ)^N)^η*r^q))) →
      ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
        (μ.prod ν) (G \ H) ≤ ENNReal.ofReal (((2:ℝ)^N)^(-η)) ∧
        ∀ p ∈ H, radialCollisionMass μ (1/(2:ℝ)^(g+k)) p ≤
          ENNReal.ofReal (((2:ℝ)^N)^(4*η)*((2:ℝ)^k)^(-q)) := by
  obtain ⟨N₀,hN₀⟩ := eventually_radial_collision_mean (d := d) hD hη hq
  refine ⟨N₀,?_⟩
  intro N hN g k hk μ ν _ _ G hG hdiag hdata
  let R : ℝ := (2:ℝ)^N
  let S : ℝ := ((2:ℝ)^k)^(-q)
  have hR : 0 < R := by dsimp [R]; positivity
  have hS : 0 < S := by dsimp [S]; positivity
  have hF : 0 < R^(4*η)*S := by positivity
  have hmean : ∀ᵐ z ∂μ,
      (∫⁻ x in {x | (z,x) ∈ G}, radialCollisionMass μ (1/(2:ℝ)^(g+k)) (z,x) ∂ν) ≤
        ENNReal.ofReal (R^(3*η)*S) := by
    filter_upwards [hdata] with z hz
    exact hN₀ N hN g k hk μ ν G hG z (by simp) (hdiag z) hz.1 hz.2.1 hz.2.2
  obtain ⟨H,hH,hHG,hcost,hcap⟩ := radial_collision_pruning μ ν G hG
    (1/(2:ℝ)^(g+k)) (ENNReal.ofReal_pos.mpr hF).ne' ENNReal.ofReal_ne_top hmean
  refine ⟨H,hH,hHG,hcost.trans_eq ?_,hcap⟩
  rw [measure_univ,mul_one,← ENNReal.ofReal_div_of_pos hF]
  congr 1
  calc
    (R^(3*η)*S)/(R^(4*η)*S) = R^(3*η)/R^(4*η) := by
      exact mul_div_mul_right _ _ (ne_of_gt hS)
    _ = R^(3*η-4*η) := (Real.rpow_sub hR _ _).symm
    _ = R^(-η) := by congr 1; ring

end Falconer

end OAI
