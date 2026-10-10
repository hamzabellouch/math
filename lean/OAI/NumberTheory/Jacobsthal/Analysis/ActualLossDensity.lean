import OAI.NumberTheory.Jacobsthal.Estimates.BoundaryRadialCoefficient
import OAI.NumberTheory.Jacobsthal.Estimates.OmissionSeries
import OAI.NumberTheory.Jacobsthal.Estimates.StandardBoundaryCoefficient

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosContinuousOmission
open ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.LinearSieveFunctions NumberTheoryLean.BuchstabBridge
open ErdosBoundaryIntegral Erdos970Dependency.StandardBoundary

noncomputable def sourceWeight : Side → ℝ → ℝ
  | .even,y => y^2-1
  | .odd,y => y^2

def sourceDomain : Side → Set ℝ
  | .even => Ioi 1
  | .odd => Ioi 0

noncomputable def lossDensity (i : Side) (y : ℝ) : ℝ :=
  2*sourceWeight i y*omissionDefect i (2*y+2) 2
noncomputable def omissionDensity (n : ℕ) (i : Side) (y : ℝ) : ℝ :=
  2*sourceWeight i y*gateIterate n omissionForce i (2*y+2) 2

theorem sourceWeight_nonnegative (i : Side) {y : ℝ} (hy : y ∈ sourceDomain i) :
    0 ≤ sourceWeight i y := by
  cases i with
  | even => change 1 < y at hy; change 0 ≤ y^2-1; nlinarith
  | odd => exact sq_nonneg y

theorem omissionDensity_continuous (n : ℕ) (i : Side) : Continuous (omissionDensity n i) := by
  have hw : Continuous (sourceWeight i) := by cases i <;> unfold sourceWeight <;> fun_prop
  have hc : Continuous (fun y : ℝ => gateIterate n omissionForce i (2*y+2) 2) :=
    (gateIterate_continuous omissionForce_continuous n i).comp
    (((continuous_const.mul continuous_id).add continuous_const).prodMk continuous_const)
  exact (continuous_const.mul hw).mul hc

theorem omissionDensity_nonnegative (n : ℕ) (i : Side) {y : ℝ} (hy : y ∈ sourceDomain i) :
    0 ≤ omissionDensity n i y :=
  mul_nonneg (mul_nonneg (by norm_num) (sourceWeight_nonnegative i hy))
    (gateIterate_nonnegative omissionForce_nonnegative n i (2*y+2) 2)

theorem lossDensity_nonnegative (i : Side) {y : ℝ} (hy : y ∈ sourceDomain i) :
    0 ≤ lossDensity i y :=
  mul_nonneg (mul_nonneg (by norm_num) (sourceWeight_nonnegative i hy)) (omissionDefect_nonnegative i (2*y+2) 2)

theorem lossDensity_hasSum (i : Side) (y : ℝ) :
    HasSum (fun n : ℕ => omissionDensity n i y) (lossDensity i y) :=
  (actual_omission_hasSum i (2*y+2) 2).mul_left (2*sourceWeight i y)

theorem lossDensity_even (y : ℝ) : lossDensity .even y=
    (y^2-1)*(1-f sieveA (y+1))-(y^2-1)*(lowerReference y-f sieveA (y+1)) := by
  norm_num [lossDensity,sourceWeight,omissionDefect,survivorBaseline,baseCutoff,lowerReference]
  ring

theorem lossDensity_odd (y : ℝ) : lossDensity .odd y=
    y^2*(upperReference y-F sieveA (y+1))-y^2*(1-F sieveA (y+1)) := by
  norm_num [lossDensity,sourceWeight,omissionDefect,survivorBaseline,baseCutoff,upperReference]
  ring

theorem lossDensity_integrable (i : Side) : IntegrableOn (lossDensity i) (sourceDomain i) := by
  cases i with
  | even =>
    have h := standard_coefficient_integrable.1.sub lower_coefficient_integrable
    apply h.congr_fun _ measurableSet_Ioi
    intro y _
    exact (lossDensity_even y).symm
  | odd =>
    have h := upper_coefficient_integrable.sub standard_coefficient_integrable.2
    apply h.congr_fun _ measurableSet_Ioi
    intro y _
    exact (lossDensity_odd y).symm

theorem actual_loss_integral :
    standardCoefficient-signedCoefficientI=
      (∫ y in sourceDomain .even,lossDensity .even y)+(∫ y in sourceDomain .odd,lossDensity .odd y) := by
  simp_rw [sourceDomain,lossDensity_even,lossDensity_odd]
  rw [integral_sub standard_coefficient_integrable.1 lower_coefficient_integrable,
    integral_sub upper_coefficient_integrable standard_coefficient_integrable.2]
  unfold standardCoefficient signedCoefficientI
  ring

end ErdosContinuousOmission

end

end Erdos970

end OAI
