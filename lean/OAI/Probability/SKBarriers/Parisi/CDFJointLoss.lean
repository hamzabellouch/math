import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFJointBridge
import OAI.Probability.SKBarriers.Parisi.CDFIdentityStability
import OAI.Probability.SKBarriers.Replicas.TripleContinuumTrial

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFJointSusceptibility_loss (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (h1 : α 1=1)
    {r q : ℝ} (hr : 0≤r) (hrq : r≤q) (hq : q≤1) :
    scalarCDFJointSusceptibility β α r q ≤ scalarCDFSusceptibilitySquareAverage β α r-
      α r*(β^2*(q-r))*(scalarSusceptibilityFloor (β^2) (1+2*β^2+4*(β^2)^2))^3/2 := by
  have hD := uniformCDFQuantiles_L1_tendsto α ha h1
  have hJ := scalarCDFJointSusceptibility_tendsto β ha α.mono
    (fun n => quantileCDF_bounds n (uniformCDFQuantiles n α))
    (fun n => quantileCDF_monotone n (uniformCDFQuantiles n α)) hD hr hrq hq
  have hS := scalarCDFSusceptibilitySquareAverage_tendsto β ha α.mono
    (fun n => quantileCDF_bounds n (uniformCDFQuantiles n α))
    (fun n => quantileCDF_monotone n (uniformCDFQuantiles n α)) hD ⟨hr,hrq.trans hq⟩
  have hα := uniformCDFQuantiles_pointwise_tendsto α ha h1 ⟨hr,hrq.trans hq⟩
  exact le_of_tendsto_of_tendsto hJ (hS.sub (((hα.mul_const (β^2*(q-r))).mul_const
    ((scalarSusceptibilityFloor (β^2) (1+2*β^2+4*(β^2)^2))^3)).div_const 2))
    (Eventually.of_forall (fun n => scalarCDFJointSusceptibility_quantile_loss β
      (uniformCDFQuantiles n α) (uniformCDFQuantiles_admissible n α h1) hr hrq hq))

def scalarJointLossConstant (β a : ℝ) : ℝ :=
  β^4*a*(scalarSusceptibilityFloor (β^2) (1+2*β^2+4*(β^2)^2))^3/2

theorem scalarJointLossConstant_pos {β a : ℝ} (hβ : β≠0) (ha : 0<a) :
    0<scalarJointLossConstant β a := by
  unfold scalarJointLossConstant
  have hb4 : 0<β^4 := by
    have H := sq_pos_of_ne_zero hβ
    nlinarith [sq_pos_of_pos H]
  have hf := scalarSusceptibilityFloor_pos (β^2) (1+2*β^2+4*(β^2)^2)
  positivity

theorem scalarCDFJointSusceptibility_strict_loss (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {r q u a : ℝ}
    (hr : 0≤r) (hrq : r≤q) (hq : q≤1) (hru : r<u) (hu : u≤1)
    (hΓ : ∀ s∈Icc r u,scalarCDFOverlap β α s=s) (har : a≤α r) (ha0 : 0≤a) :
    β^2*scalarCDFJointSusceptibility β α r q≤1-scalarJointLossConstant β a*(q-r) := by
  have H := mul_le_mul_of_nonneg_left (scalarCDFJointSusceptibility_loss β α ha h1 hr hrq hq) (sq_nonneg β)
  have H₀ := scalarCDF_susceptibility_square_le_one β α ha h1 hr hru hu hΓ
  have Hp := mul_le_mul le_rfl har ha0 (show 0≤β^4*((scalarSusceptibilityFloor (β^2) (1+2*β^2+4*(β^2)^2))^3)*(q-r)/2 by
    have := scalarSusceptibilityFloor_pos (β^2) (1+2*β^2+4*(β^2)^2)
    have := sub_nonneg.mpr hrq
    positivity)
  dsimp [scalarJointLossConstant]
  nlinarith

end SK.Analytic

end
end

end OAI
