import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedCollisionBlocks
import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedGeometricBlock

namespace OAI

section

/-! # Terminal survival and physical positions of density-scaled histories -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem finishFlight_scaled (ρ : ℝ) (hρ : ρ ≠ 0) (x₀ : V) (p : PhysicalFlightState) :
    finishMediumFlight (flightScaleEquiv ρ hρ x₀ p) =
      (ρ • ((finishMediumFlight p).1-x₀),(finishMediumFlight p).2) := by
  apply Prod.ext
  · dsimp [finishMediumFlight,flightScaleEquiv]
    module
  · rfl

theorem finishFlight_scale_inverse (ρ : ℝ) (hρ : ρ ≠ 0) (x₀ : V)
    (p : PhysicalFlightState) :
    (x₀+ρ⁻¹ • (finishMediumFlight (flightScaleEquiv ρ hρ x₀ p)).1,
      (finishMediumFlight (flightScaleEquiv ρ hρ x₀ p)).2) = finishMediumFlight p := by
  rw [finishFlight_scaled,smul_smul,inv_mul_cancel₀ hρ,one_smul]
  simp

theorem clockSurvival_scaled (C : ℝ≥0) {ρ : ℝ} (hρ : 0 < ρ) (s : ℝ) :
    clockSurvival C (ρ*s) = clockSurvival (Real.toNNReal ρ*C) s := by
  unfold clockSurvival
  congr 2
  rw [NNReal.coe_mul,Real.coe_toNNReal _ hρ.le]
  ring

theorem densityScaled_endpoint_integral (b : BeamCoefficients) {ρ : ℝ} (hρ : 0 < ρ)
    (t₀ endTime : ℝ) (x₀ : V) (n : ℕ) (p : PhysicalFlightState) {T : ℝ} (hT : ρ*p.1 ≤ T)
    {F : V × V → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, clockSurvival (Real.toNNReal ρ*referenceClock) q.1 * F (finishMediumFlight q)
      ∂((boundedDensityScaledEvent b endTime (Real.toNNReal ρ))^n) p) =
    ∫⁻ q, clockSurvival referenceClock q.1 *
      F (x₀+ρ⁻¹ • (finishMediumFlight q).1,(finishMediumFlight q).2)
      ∂((boundedMediumEventKernel (b.normalized ρ t₀ x₀) (ρ*(endTime-t₀)) T)^n)
        (flightScaleEquiv ρ hρ.ne' x₀ p) := by
  let g : PhysicalFlightState → ℝ≥0∞ := fun q => clockSurvival referenceClock q.1 *
    F (x₀+ρ⁻¹ • (finishMediumFlight q).1,(finishMediumFlight q).2)
  have hg : Measurable g := by
    apply (show Measurable (fun q : PhysicalFlightState => clockSurvival referenceClock q.1) by
      unfold clockSurvival; fun_prop).mul
    exact hF.comp (by unfold finishMediumFlight; fun_prop)
  have H := congrArg (fun μ : Measure PhysicalFlightState => ∫⁻ q, g q ∂μ)
    (densityScaled_bounded_history_map b hρ t₀ endTime x₀ n p hT)
  rw [lintegral_map hg (flightScaleEquiv ρ hρ.ne' x₀).measurable] at H
  calc
    _ = ∫⁻ q, g (flightScaleEquiv ρ hρ.ne' x₀ q)
        ∂((boundedDensityScaledEvent b endTime (Real.toNNReal ρ))^n) p := by
      apply lintegral_congr
      intro q
      dsimp only [g]
      rw [finishFlight_scale_inverse]
      change _ = clockSurvival referenceClock (ρ*q.1)*F (finishMediumFlight q)
      rw [clockSurvival_scaled referenceClock hρ]
    _ = _ := H

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The displacement target under the local density scale -/

noncomputable section

open Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem scaled_block_target {ρ : ℝ} (hρ : 0 < ρ) (x : V) (Δ κ d : ℝ) (q : V × V) :
    (x+ρ⁻¹ • q.1,q.2) ∈ physicalBlockTarget x Δ κ d ↔
      q ∈ physicalBlockTarget 0 (ρ*Δ) κ d := by
  have he : (x+ρ⁻¹ • q.1)-(x+(κ*Δ) • firstAxis) =
      ρ⁻¹ • (q.1-(κ*(ρ*Δ)) • firstAxis) := by
    rw [smul_sub,smul_smul,show ρ⁻¹*(κ*(ρ*Δ)) = κ*Δ by field_simp [hρ.ne']]
    abel
  change (‖(x+ρ⁻¹ • q.1)-(x+(κ*Δ) • firstAxis)‖ < d*κ*Δ ∧ ‖q.2‖ < 5) ↔
    (‖q.1-(0+(κ*(ρ*Δ)) • firstAxis)‖ < d*κ*(ρ*Δ) ∧ ‖q.2‖ < 5)
  rw [he,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hρ,zero_add]
  have hnorm : ρ⁻¹*‖q.1-(κ*(ρ*Δ)) • firstAxis‖ =
      ‖q.1-(κ*(ρ*Δ)) • firstAxis‖/ρ := by ring
  rw [hnorm,div_lt_iff₀ hρ]
  have hprod : d*κ*Δ*ρ = d*κ*(ρ*Δ) := by ring
  rw [hprod]

theorem scaled_block_indicator {ρ : ℝ} (hρ : 0 < ρ) (x : V) (Δ κ d : ℝ) (q : V × V) :
    (physicalBlockTarget x Δ κ d).indicator (1 : V × V → ℝ≥0∞) (x+ρ⁻¹ • q.1,q.2) =
      (physicalBlockTarget 0 (ρ*Δ) κ d).indicator 1 q := by
  by_cases hq : q ∈ physicalBlockTarget 0 (ρ*Δ) κ d
  · simp [hq,(scaled_block_target hρ x Δ κ d q).mpr hq]
  · simp [hq,show (x+ρ⁻¹ • q.1,q.2) ∉ physicalBlockTarget x Δ κ d from
      fun h => hq ((scaled_block_target hρ x Δ κ d q).mp h)]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Exact physical-time mass of each finite normalized branching block -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def densityScaledBlockMass (b : BeamCoefficients) (endTime ρ : ℝ)
    (x : V) (Δ : ℝ) (v : RetainedState) (κ d : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range N, ∫⁻ q,
    clockSurvival (Real.toNNReal ρ*referenceClock) q.1 *
      (physicalBlockTarget x Δ κ d).indicator 1 (finishMediumFlight q)
    ∂((boundedDensityScaledEvent b endTime (Real.toNNReal ρ))^n) (Δ,(x,(v : V)))

theorem densityScaledBlockMass_eq (b : BeamCoefficients) {ρ : ℝ} (hρ : 0 < ρ)
    (t₀ : ℝ) (x : V) (Δ : ℝ) (v : RetainedState) (κ d : ℝ) (N : ℕ) {T : ℝ}
    (hT : ρ*Δ ≤ T) :
    densityScaledBlockMass b (t₀+Δ) ρ x Δ v κ d N =
      boundedMediumBlockMass (b.normalized ρ t₀ x) (ρ*Δ) T (ρ*Δ,(0,v)) κ d N := by
  unfold densityScaledBlockMass boundedMediumBlockMass
  apply Finset.sum_congr rfl
  intro n _hn
  have H := densityScaled_endpoint_integral b hρ t₀ (t₀+Δ) x n
    (Δ,(x,(v : V))) hT
    (F := (physicalBlockTarget x Δ κ d).indicator (1 : V × V → ℝ≥0∞))
    (measurable_const.indicator (physicalBlockTarget_measurable _ _ _ _))
  rw [H]
  have ht : ρ*(t₀+Δ-t₀) = ρ*Δ := by ring
  have hp : flightScaleEquiv ρ hρ.ne' x (Δ,(x,(v : V))) = (ρ*Δ,(0,(v : V))) := by
    simp [flightScaleEquiv]
  rw [ht,hp]
  simp_rw [scaled_block_indicator hρ x Δ κ d]
  exact (boundedMediumWord_integral (b.normalized ρ t₀ x) (ρ*Δ) T
    (mediumFlightSeed_measurable (measurable_const.indicator
      (physicalBlockTarget_measurable 0 (ρ*Δ) κ d))) n
        (embedFlightState (ρ*Δ,(0,v)))).symm

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
