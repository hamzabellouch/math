import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFJointLoss
import OAI.Probability.SKBarriers.Locking.NarrowCoefficientBound

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem narrowCDFTrialCoefficient_quantitative {β : ℝ} (hβ : β≠0)
    (α : StieltjesFunction ℝ) (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hα1 : α 1=1)
    {r h q u a θ m η : ℝ} (hh : 0< h) (hr : 0≤ r) (hrq : r≤ q) (hq : q≤1)
    (hru : r< u) (hu : u≤1) (hΓ : ∀ s∈Icc r u,scalarCDFOverlap β α s=s)
    (hm : 0 < m) (hmr : m≤α r) (ha : 1/2≤ a) (hθ : 0≤θ) (haθ : a+θ=1)
    (hS : scalarCDFSusceptibilityAverage β α q=(∫ x in q..1,α x)+α q*(q-scalarCDFOverlap β α q))
    (hdev : |q-scalarCDFOverlap β α q|≤η) :
    narrowCDFTrialCoefficient β α r h q a θ≤
      3*β^2*η/h+narrowCDFErrorConstant β*((α (r+h)-α (r-h))+θ^2)-
        (β^2*m*scalarJointLossConstant β m)*θ*(q-r) := by
  have ha0 : 0≤ a := by linarith
  have ha1 : a≤1 := by linarith
  have hθ1 : θ≤1 := by linarith
  have hη : 0≤η := (abs_nonneg _).trans hdev
  have hK0 : 0≤(2*a^2+θ^2)/h := by positivity
  have hK : (2*a^2+θ^2)/h≤3/h := by
    apply div_le_div_of_nonneg_right _ hh.le
    nlinarith [sq_nonneg (1-a),sq_nonneg (1-θ)]
  have hSq : scalarCDFSusceptibilityAverage β α q-(∫ x in q..1,α x)≤η := by
    rw [hS]
    have H := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hdev) (hα q).1
    have H' := mul_le_mul_of_nonneg_right (hα q).2 hη
    nlinarith
  have Hq : β^2*((2*a^2+θ^2)/h)*(scalarCDFSusceptibilityAverage β α q-(∫ x in q..1,α x))≤3*β^2*η/h := by
    calc
      _ ≤ β^2*((2*a^2+θ^2)/h)*η := mul_le_mul_of_nonneg_left hSq (mul_nonneg (sq_nonneg β) hK0)
      _ ≤ β^2*(3/h)*η := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (sq_nonneg β)) hη
      _ = _ := by ring
  have hJ := scalarCDFJointSusceptibility_strict_loss β α hα hα1 hr hrq hq hru hu hΓ hmr hm.le
  have hL : 0≤ scalarJointLossConstant β m := (scalarJointLossConstant_pos hβ hm).le
  have hD : 0≤ q-r := sub_nonneg.mpr hrq
  have hmean := narrowCDFMean_bounds β α.mono r hh hθ
  have hmeanm : β^2*θ*m≤ narrowCDFMean β α r h θ :=
    (mul_le_mul_of_nonneg_left hmr (mul_nonneg (sq_nonneg β) hθ)).trans hmean.1
  have hmean0 : 0≤ narrowCDFMean β α r h θ := (by positivity : 0≤β^2*θ*m).trans hmeanm
  have hmixed : β^2*θ*m≤2*a*narrowCDFMean β α r h θ := by
    have H := mul_le_mul_of_nonneg_right ha hmean0
    linarith
  have Hmix : 2*a*narrowCDFMean β α r h θ*(β^2*scalarCDFJointSusceptibility β α r q-1)≤
      -(β^2*m*scalarJointLossConstant β m)*θ*(q-r) := by
    have H := mul_le_mul_of_nonneg_left (show β^2*scalarCDFJointSusceptibility β α r q-1≤-scalarJointLossConstant β m*(q-r) by linarith)
      (show 0≤2*a*narrowCDFMean β α r h θ by positivity)
    have H' := mul_le_mul_of_nonneg_right hmixed (mul_nonneg hL hD)
    nlinarith only [H,H']
  have H := narrowCDFTrialCoefficient_le β hα α.mono r q hh ha0 hθ haθ
  linarith

end SK.Analytic

end
end

end OAI
