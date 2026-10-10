import OAI.Analysis.CircleDomains.Sobolev.CircleBranchEnergy

namespace OAI

/-! A continuous real lift of a smooth circle map is automatically smooth,
with exactly its intrinsic differential and no additional energy cost. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff ENNReal

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffOn_real_lift {U : Set E} (hU : IsOpen U)
    {f : E → UnitAddCircle} (hf : SmoothCircleOn f U)
    {u : E → ℝ} (hu : ContinuousOn u U)
    (hproj : ∀ x ∈ U, (u x : UnitAddCircle) = f x) :
    ContDiffOn ℝ ∞ u U := by
  intro x hx
  have hux : ContinuousAt u x := (hu x hx).continuousAt (hU.mem_nhds hx)
  have hb := hf x hx (circleCut f x) (circleCut_ne f x)
  have heq : (fun y => (u y : UnitAddCircle)) =ᶠ[𝓝 x]
      fun y => (circleBranch f (circleCut f x) y : UnitAddCircle) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [hproj y hy, coe_circleBranch]
  obtain ⟨m, hm⟩ := eventually_lifts_differ_by_integer hux hb.continuousAt heq
  exact ((hb.add contDiffAt_const).congr_of_eventuallyEq hm).contDiffWithinAt

theorem fderiv_real_lift {U : Set E} (hU : IsOpen U)
    {f : E → UnitAddCircle} (hf : SmoothCircleOn f U)
    {u : E → ℝ} (hu : ContinuousOn u U)
    (hproj : ∀ x ∈ U, (u x : UnitAddCircle) = f x) {x : E} (hx : x ∈ U) :
    fderiv ℝ u x = circleFDeriv f x := by
  symm
  apply circleFDeriv_eq_lift
    ((hf.continuousOn x hx).continuousAt (hU.mem_nhds hx))
    ((hu x hx).continuousAt (hU.mem_nhds hx))
  filter_upwards [hU.mem_nhds hx] with y hy
  exact hproj y hy

theorem real_lift_energy_le [MeasurableSpace E] {U A : Set E}
    (hA : IsOpen A) (hAU : A ⊆ U)
    {f : E → UnitAddCircle} (hf : SmoothCircleOn f U)
    {u : E → ℝ} (hu : ContinuousOn u A)
    (hproj : ∀ x ∈ A, (u x : UnitAddCircle) = f x) (μ : Measure E)
    (hAm : MeasurableSet A) :
    (∫⁻ x in A, ENNReal.ofReal ‖fderiv ℝ u x‖ ^ 2 ∂μ) ≤
      ∫⁻ x in U, ENNReal.ofReal ‖circleFDeriv f x‖ ^ 2 ∂μ := by
  calc
    _ = ∫⁻ x in A, ENNReal.ofReal ‖circleFDeriv f x‖ ^ 2 ∂μ := by
      apply setLIntegral_congr_fun hAm
      intro x hx
      dsimp only
      rw [fderiv_real_lift hA (fun x hx => hf x (hAU hx)) hu hproj hx]
    _ ≤ _ := lintegral_mono_set hAU

end CircleDomainRigidity.FiniteTransfer

end

end OAI
