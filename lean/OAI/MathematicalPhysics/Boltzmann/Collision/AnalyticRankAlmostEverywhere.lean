import OAI.MathematicalPhysics.Boltzmann.Branching.FanNullSet
import OAI.MathematicalPhysics.Boltzmann.Collision.AnalyticTools
import OAI.MathematicalPhysics.Boltzmann.Collision.MityaginPublished
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Compactness.Lindelof

namespace OAI

section

/-! # Scalar analytic zero-set nullity on a convex twenty-dimensional domain -/
noncomputable section
open MeasureTheory Set Filter
namespace BoltzmannNonuniqueness.Published

theorem fan_eq_lineMap (a : FanPhase) (y : FanRemainder) :
    fan a y = AffineMap.lineMap a (a+(1,y)) := by
  funext t
  simp only [AffineMap.lineMap_apply_module',add_sub_cancel_left,fan,Prod.smul_mk,smul_eq_mul,mul_one]
  ext <;> simp [add_comm]

theorem analytic_convex_zero_null {U : Set FanPhase} (hU : IsOpen U) (hconv : Convex ℝ U)
    {f : FanPhase → ℝ} (hf : AnalyticOnNhd ℝ f U) {a : FanPhase}
    (ha : a ∈ U) (hne : f a ≠ 0) : volume {x ∈ U | f x = 0} = 0 := by
  classical
  let g := U.piecewise f 0
  have hg : Measurable g := hf.continuousOn.measurable_piecewise continuous_zero.continuousOn hU.measurableSet
  have hZ : MeasurableSet {x ∈ U | f x = 0} := by
    have he : {x ∈ U | f x = 0} = U ∩ {x | g x = 0} := by
      ext x
      by_cases hx : x ∈ U <;> simp [g,hx]
    rw [he]
    exact hU.measurableSet.inter (measurableSet_eq_fun hg measurable_const)
  apply fan_null_set a hZ
  intro y
  let V := fan a y ⁻¹' U
  have hm : Continuous (fan a y) := by unfold fan; fun_prop
  have hV : IsOpen V := hU.preimage hm
  have hc : IsPreconnected V := by
    rw [show V = (AffineMap.lineMap a (a+(1,y))) ⁻¹' U from by rw [← fan_eq_lineMap]]
    exact (hconv.affine_preimage _).isPreconnected
  have hfa : AnalyticOnNhd ℝ (f ∘ fan a y) V := by
    intro t ht
    apply (hf _ ht).comp
    change AnalyticAt ℝ (fun s : ℝ => (a.1+s,a.2+s • y)) t
    exact (analyticAt_const.add analyticAt_id).prod
      (analyticAt_const.add (analyticAt_id.smul analyticAt_const))
  have hn := analytic_line_ae_ne_zero hV.measurableSet hc hfa
    ⟨0,by simpa [V,fan] using ha,by simpa [Function.comp_def,fan] using hne⟩
  have hn' := (ae_restrict_iff' hV.measurableSet).mp hn
  filter_upwards [hn'] with t ht
  intro hz
  exact ht hz.1 hz.2

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Scalar analytic zero sets on connected open domains -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology
namespace BoltzmannNonuniqueness.Published

theorem analytic_connected_zero_null {U : Set FanPhase} (hU : IsOpen U)
    (hconn : IsPreconnected U) {f : FanPhase → ℝ} (hf : AnalyticOnNhd ℝ f U)
    (hne : ∃ a ∈ U, f a ≠ 0) : volume {x ∈ U | f x = 0} = 0 := by
  let Z := {x ∈ U | f x = 0}
  have hlocal : ∀ x ∈ Z, ∃ r > 0, volume (ball x r ∩ Z) = 0 := by
    intro x hx
    obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp hU x hx.1
    have hex : ∃ a ∈ ball x r, f a ≠ 0 := by
      by_contra! h
      have hz : f =ᶠ[𝓝 x] 0 := by
        filter_upwards [ball_mem_nhds x hr] with y hy
        exact h y hy
      have hzU := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hx.1 hz
      obtain ⟨a,ha,hfa⟩ := hne
      exact hfa (hzU ha)
    obtain ⟨a,ha,hfa⟩ := hex
    have hn := analytic_convex_zero_null isOpen_ball (convex_ball x r)
      (hf.mono hsub) ha hfa
    refine ⟨r,hr,?_⟩
    have he : ball x r ∩ Z = {y ∈ ball x r | f y = 0} := by
      ext y
      simp only [mem_inter_iff,mem_ofPred_eq,Z]
      exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hsub h.1,h.2⟩⟩
    rwa [he]
  have hcompl : Zᶜ ∈ ae (volume : Measure FanPhase) := by
    apply (HereditarilyLindelofSpace.isLindelof Z).compl_mem_sets_of_nhdsWithin
    intro x hx
    obtain ⟨r,hr,hn⟩ := hlocal x hx
    refine ⟨ball x r ∩ Z, ?_, ?_⟩
    · simpa only [inter_comm] using inter_mem_nhdsWithin Z (ball_mem_nhds x hr)
    · exact (mem_ae_iff.mpr (by simpa only [compl_compl] using hn) :
        (ball x r ∩ Z)ᶜ ∈ ae volume)
  simpa only [compl_compl,Z] using mem_ae_iff.mp hcompl

end BoltzmannNonuniqueness.Published

end

end

section

/-! # From one regular point to almost-everywhere rank, conditionally on scalar zero sets -/

noncomputable section

open MeasureTheory Set Function

namespace BoltzmannNonuniqueness.FiveGainMap

theorem analytic_rank_ae (hM : Published.Mityagin2020FiveGainParameters)
    {U : Set Parameters} (hU : IsOpen U) (hconn : IsPreconnected U)
    {Φ : Parameters → State} (ha : AnalyticOnNhd ℝ Φ U)
    {q₀ : Parameters} (hq₀ : q₀ ∈ U) (hrank : Surjective (fderiv ℝ Φ q₀)) :
    volume {q ∈ U | ¬Surjective (fderiv ℝ Φ q)} = 0 := by
  classical
  obtain ⟨R,hR⟩ := (fderiv ℝ Φ q₀).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hrank)
  let R' : State →L[ℝ] Parameters := R.toContinuousLinearMap
  let A : Parameters → State →L[ℝ] State := fun q => (fderiv ℝ Φ q).comp R'
  have hA : AnalyticOnNhd ℝ A U := by
    intro q hq
    exact (((ContinuousLinearMap.compL ℝ State Parameters State).flip R').analyticAt _).comp
      (ha q hq).fderiv
  have hA₀ : A q₀ = ContinuousLinearMap.id ℝ State := by
    apply ContinuousLinearMap.ext
    intro v
    exact LinearMap.congr_fun hR v
  have hz := hM U hU hconn (fun q => (A q).toLinearMap.det)
    (fun q hq => determinant_analyticAt (hA q hq))
    ⟨q₀,hq₀,by rw [hA₀]; simp⟩
  apply measure_mono_null _ hz
  intro q hq
  refine ⟨hq.1,?_⟩
  by_contra hdet
  have hunit : IsUnit (A q).toLinearMap :=
    (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hsur : Surjective (A q) := LinearMap.range_eq_top.mp
    ((LinearMap.isUnit_iff_range_eq_top _).mp hunit)
  apply hq.2
  intro v
  obtain ⟨w,hw⟩ := hsur v
  exact ⟨R' w,hw⟩

end BoltzmannNonuniqueness.FiveGainMap

end

end

end OAI
