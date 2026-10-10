import OAI.Geometry.IsometricImmersion.Darboux.QEnergyApplication
import OAI.Geometry.IsometricImmersion.Energy.MovingEnergyGradient

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

def spatialEnergyNormBudget (s0 : ℝ) (A : ℝ≥0) : ℝ≥0 :=
  ⟨Real.sqrt (2 * (1 + 1 / s0)) * (A : ℝ), mul_nonneg (Real.sqrt_nonneg _) A.2⟩

theorem real_slice_eLpNorm_two_le_of_square_integral
    {f : ℝ → ℝ} {left right : ℝ} {B : ℝ≥0}
    (hlr : left ≤ right) (hf : MemLp f 2 (volume.restrict (Icc left right)))
    (hB : (∫ x in left..right, f x ^ 2) ≤ (B : ℝ)^2) :
    eLpNorm f 2 (volume.restrict (Icc left right)) ≤ (B : ℝ≥0∞) := by
  rw [intervalIntegral.integral_of_le hlr, restrict_Ioc_eq_restrict_Icc,
    integral_square_eq_L2_norm_square hf, Lp.norm_def, eLpNorm_congr_ae hf.coeFn_toLp] at hB
  apply (ENNReal.toReal_le_toReal hf.eLpNorm_ne_top (by simp)).mp
  change (eLpNorm f 2 (volume.restrict (Icc left right))).toReal ≤ (B : ℝ)
  exact (sq_le_sq₀ ENNReal.toReal_nonneg B.2).mp hB

theorem spatialFirstJet_slice_eLpNorm_two_of_energy
    {z S : Coord → ℝ} {U : Set Coord} {left right theta s0 : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hS : ContDiffOn ℝ ∞ S U)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlr : left ≤ right) (hs0 : 0 < s0)
    (hfloor : ∀ x ∈ Icc left right, s0 ≤ S (coordinatePoint x theta))
    (ell : ℕ) (A : ℝ≥0)
    (henergy : Real.sqrt (∫ x in left..right,
      energyDensity S (horizontalJet z ell) (coordinatePoint x theta)) ≤ (A : ℝ))
    (i : Fin 2) :
    eLpNorm (fun x => spatialJet (spatialFirstJet z i) ell (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤ (spatialEnergyNormBudget s0 A : ℝ≥0∞) := by
  let u := horizontalJet z ell
  let E := ∫ x in left..right, energyDensity S u (coordinatePoint x theta)
  let C := 2 * (1 + 1 / s0)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hu := horizontalJet_contDiffOn hU hz ell
  have hd (j : Fin 2) := partial_contDiffOn hu hU j
  have he : ContDiffOn ℝ ∞ (energyDensity S u) U :=
    (((hd 1).pow 2).add (hS.mul ((hd 0).pow 2))).div_const 2
  have hEA : E ≤ (A : ℝ)^2 := (Real.sqrt_le_iff.mp henergy).2
  have hfiCont : ContinuousOn (fun x => coordPartial i u (coordinatePoint x theta)^2) (Icc left right) :=
    ((hd i).pow 2).continuousOn.comp (horizontalPoint_contDiff theta).continuous.continuousOn hseg
  have heCont : ContinuousOn (fun x => C * energyDensity S u (coordinatePoint x theta)) (Icc left right) :=
    (continuousOn_const.mul he.continuousOn).comp (horizontalPoint_contDiff theta).continuous.continuousOn hseg
  have hiInt : (∫ x in left..right, coordPartial i u (coordinatePoint x theta)^2) ≤ C * E := by
    have hh : (∫ x in left..right, coordPartial i u (coordinatePoint x theta)^2) ≤
        ∫ x in left..right, C * energyDensity S u (coordinatePoint x theta) :=
      intervalIntegral.integral_mono_on hlr
      (hfiCont.intervalIntegrable_of_Icc hlr) (heCont.intervalIntegrable_of_Icc hlr)
      (fun x hx => show coordPartial i u (coordinatePoint x theta)^2 ≤
          C * energyDensity S u (coordinatePoint x theta) from by
        have hscalar := scalar_gradient_le_energy hs0 (hfloor x hx)
          (a := coordPartial 1 u (coordinatePoint x theta)) (b := coordPartial 0 u (coordinatePoint x theta))
        have hind : coordPartial i u (coordinatePoint x theta)^2 ≤
            coordPartial 1 u (coordinatePoint x theta)^2 + coordPartial 0 u (coordinatePoint x theta)^2 := by
          fin_cases i
          · change coordPartial 0 u (coordinatePoint x theta)^2 ≤ _
            nlinarith [sq_nonneg (coordPartial 1 u (coordinatePoint x theta))]
          · change coordPartial 1 u (coordinatePoint x theta)^2 ≤ _
            nlinarith [sq_nonneg (coordPartial 0 u (coordinatePoint x theta))]
        exact hind.trans hscalar)
    simpa only [intervalIntegral.integral_const_mul] using hh
  have hiBudget : (∫ x in left..right, coordPartial i u (coordinatePoint x theta)^2) ≤
      (spatialEnergyNormBudget s0 A : ℝ)^2 := by
    have hbound := hiInt.trans (mul_le_mul_of_nonneg_left hEA hC)
    change _ ≤ (Real.sqrt C * (A : ℝ))^2
    rw [mul_pow, Real.sq_sqrt hC]
    exact hbound
  have hiLp := real_slice_eLpNorm_two_le_of_square_integral hlr
    (smooth_slice_memLp_two (hd i).continuousOn hseg) hiBudget
  have heq : (fun x => spatialJet (spatialFirstJet z i) ell (coordinatePoint x theta)) =ᵐ[
      volume.restrict (Icc left right)] (fun x => coordPartial i u (coordinatePoint x theta)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [← horizontalJet_eq_spatialJet]
    exact horizontalJet_coordPartial hU hz i ell _ (hseg x hx)
  rw [eLpNorm_congr_ae heq]
  exact hiLp

end SmoothLocal.HighEquation

end

end OAI
