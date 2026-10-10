import OAI.Probability.FirstPassage.ConvexC1
import OAI.Probability.FirstPassage.UniqueSupports

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

lemma actual_profile_contDiff (henv : ExponentialEnvironment P τ) :
    ContDiff ℝ 1 (fun t => actualSourceTimeConstant (direction t)) := by
  let μ := actualSourceTimeConstant
  have he (t : ℝ) : direction 0+t • transverseUnit=direction t := by
    ext i; fin_cases i <;> simp [direction,transverseUnit,PiLp.add_apply,PiLp.smul_apply]
  have hc := convex_transverse_profile μ (direction 0) transverseUnit
    actualSourceTimeConstant_norm.triangle (norm_positive_homogeneous μ actualSourceTimeConstant_norm)
  have hd : Differentiable ℝ (fun t : ℝ => μ (direction 0+t • transverseUnit)) := by
    intro t
    have hne : direction t ≠ 0 := by intro hz; have hh := congrArg xCoord hz; change (1 : ℝ)=0 at hh; norm_num at hh
    obtain ⟨ℓ,hℓ⟩ := actual_differentiable_away henv (direction t) hne
    have hh : DifferentiableAt ℝ μ (direction 0+t • transverseUnit) := by rw [he]; exact hℓ.differentiableAt
    have hm : DifferentiableAt ℝ (fun s : ℝ => direction 0+s • transverseUnit) t :=
      (((hasDerivAt_id t).smul_const transverseUnit).const_add (direction 0)).differentiableAt
    exact DifferentiableAt.comp (g := μ) (f := fun s : ℝ => direction 0+s • transverseUnit) t hh hm
  simpa only [he] using convex_contDiff_one _ hc hd

lemma plane_direction_representation (v : Plane) (hx : v 0 ≠ 0) :
    v 0 • direction (v 1/v 0)=v := by
  ext i
  fin_cases i <;> simp [direction,PiLp.smul_apply]
  field_simp

lemma actual_contDiffAt_horizontal (henv : ExponentialEnvironment P τ) (v : Plane) (hx : v 0 ≠ 0) :
    ContDiffAt ℝ 1 actualSourceTimeConstant v := by
  let y : Plane →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1
  have hxc : ContDiffAt ℝ 1 (fun z : Plane => z 0) v := xCoord.contDiff.contDiffAt
  have hyc : ContDiffAt ℝ 1 (fun z : Plane => z 1) v := y.contDiff.contDiffAt
  have hquot := hyc.div hxc hx
  have hprofile := (actual_profile_contDiff henv).contDiffAt.comp v hquot
  have habs : ContDiffAt ℝ 1 (fun z : Plane => |z 0|) v := by
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · have hn : ∀ᶠ z in 𝓝 v, z 0 < 0 := xCoord.continuous.continuousAt.eventually (gt_mem_nhds hneg)
      apply hxc.neg.congr_of_eventuallyEq
      filter_upwards [hn] with z hz
      exact abs_of_neg hz
    · have hn : ∀ᶠ z in 𝓝 v, 0 < z 0 := xCoord.continuous.continuousAt.eventually (lt_mem_nhds hpos)
      apply hxc.congr_of_eventuallyEq
      filter_upwards [hn] with z hz
      exact abs_of_pos hz
  have hprod := habs.mul hprofile
  have heq : actualSourceTimeConstant =ᶠ[𝓝 v]
      (fun z : Plane => |z 0| * actualSourceTimeConstant (direction (z 1/z 0))) := by
    have hn : ∀ᶠ z in 𝓝 v, z 0 ≠ 0 := xCoord.continuous.continuousAt.eventually (eventually_ne_nhds hx)
    filter_upwards [hn] with z hz
    conv_lhs => rw [← plane_direction_representation z hz]
    exact actualSourceTimeConstant_norm.homogeneous _ _
  exact hprod.congr_of_eventuallyEq heq

theorem actual_contDiffAt_away (henv : ExponentialEnvironment P τ) (v : Plane) (hv : v ≠ 0) :
    ContDiffAt ℝ 1 actualSourceTimeConstant v := by
  by_cases hx : v 0 ≠ 0
  · exact actual_contDiffAt_horizontal henv v hx
  · have hy : v 1 ≠ 0 := by
      intro hy
      apply hv
      ext i
      fin_cases i <;> simp_all
    have hswap : swapPlane v 0 ≠ 0 := by simpa using hy
    have hs := actual_contDiffAt_horizontal henv (swapPlane v) hswap
    have hh := hs.comp v swapPlane.toContinuousLinearEquiv.contDiff.contDiffAt
    have he : (fun z => actualSourceTimeConstant (swapPlane z))=actualSourceTimeConstant :=
      funext (actualSourceTimeConstant_swap henv)
    simpa only [Function.comp_def,he] using hh

theorem actual_C1_unit_sphere (henv : ExponentialEnvironment P τ) : C1UnitSphere actualSourceTimeConstant := by
  let μ := actualSourceTimeConstant
  let U : Set Plane := {0}ᶜ
  have hU : IsOpen U := isClosed_singleton.isOpen_compl
  have hc : ContDiffOn ℝ 1 μ U := by
    intro v hv
    exact (actual_contDiffAt_away henv v hv).contDiffWithinAt
  intro v hv
  have hne : v ≠ 0 := by intro he; have hz := (actualSourceTimeConstant_norm.zero_iff v).mpr he; linarith
  refine ⟨U,hU,hne,fun w => μ w-1,hc.sub contDiffOn_const,?_,?_⟩
  · intro w _
    exact sub_eq_zero.symm
  · intro w hw hzero
    have hw1 : μ w=1 := sub_eq_zero.mp hzero
    obtain ⟨ℓ,hℓ⟩ := actual_differentiable_away henv w hw
    have hEuler := (norm_derivative_support μ actualSourceTimeConstant_norm w ℓ hℓ).1
    refine ⟨ℓ,by simpa using hℓ.sub_const 1,?_⟩
    intro hz
    simp [hz,hw1] at hEuler

end PlanarFPP

end OAI
