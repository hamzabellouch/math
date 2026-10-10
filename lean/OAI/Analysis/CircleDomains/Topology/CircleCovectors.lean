import OAI.Analysis.CircleDomains.Sobolev.CircleDifferential

namespace OAI

/-!
# Smooth covector fields of periodic coordinates

The locally defined circle differential is an ordinary smooth covector
field on its open domain. This supplies the tensor used in the same
metric construction as for single-valued real coordinates.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem circleFDeriv_eventuallyEq_lift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → UnitAddCircle} {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hu : ContDiffOn ℝ ∞ u U)
    (hproj : ∀ y ∈ U, (u y : UnitAddCircle) = f y) {x : E} (hx : x ∈ U) :
    circleFDeriv f =ᶠ[𝓝 x] fderiv ℝ u := by
  filter_upwards [hU.mem_nhds hx] with y hy
  apply circleFDeriv_eq_lift (hf.continuousAt (hU.mem_nhds hy))
    (hu.continuousOn.continuousAt (hU.mem_nhds hy))
  filter_upwards [hU.mem_nhds hy] with z hz
  exact hproj z hz

theorem contDiffOn_circleFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → UnitAddCircle} {U : Set E} (hU : IsOpen U) (hf : SmoothCircleOn f U) :
    ContDiffOn ℝ ∞ (circleFDeriv f) U := by
  intro x hx
  let a := circleCut f x
  let V := U ∩ f ⁻¹' ({(a : UnitAddCircle)} : Set UnitAddCircle)ᶜ
  have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl
  have hxV : x ∈ V := ⟨hx, circleCut_ne f x⟩
  have hu : ContDiffOn ℝ ∞ (circleBranch f a) V := by
    intro y hy
    exact (hf y hy.1 a hy.2).contDiffWithinAt
  have heq := circleFDeriv_eventuallyEq_lift hV (hf.continuousOn.mono inter_subset_left)
    hu (fun y _ => coe_circleBranch f a y) hxV
  exact (((hu.fderiv_of_isOpen (m := ∞) hV (by simp)).contDiffAt (hV.mem_nhds hxV)).congr_of_eventuallyEq
    heq).contDiffWithinAt

theorem contDiffOn_circleGradient
    {f : (ℝ × ℝ) → UnitAddCircle} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hf : SmoothCircleOn f U) : ContDiffOn ℝ ∞ (circleGradient f) U := by
  have hd := contDiffOn_circleFDeriv hU hf
  exact (hd.clm_apply contDiffOn_const).prodMk (hd.clm_apply contDiffOn_const)

/-- On a local real branch the intrinsic covector field equals the
ordinary gradient on a whole neighborhood, not only at its center. -/
theorem circleGradient_eventuallyEq_lift
    {f : (ℝ × ℝ) → UnitAddCircle} {u : (ℝ × ℝ) → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hu : ContDiffOn ℝ ∞ u U)
    (hproj : ∀ y ∈ U, (u y : UnitAddCircle) = f y) {x : ℝ × ℝ} (hx : x ∈ U) :
    circleGradient f =ᶠ[𝓝 x] planarGradient u := by
  filter_upwards [circleFDeriv_eventuallyEq_lift hU hf hu hproj hx] with y hy
  simp only [circleGradient, hy, planarGradient]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
