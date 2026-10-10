import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.PlaneNormalization
import OAI.Geometry.TamingCompatibility.Charts.RadialUnitCoordinates

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)

omit [CompactSpace X] [T2Space X] in
lemma unitChartVector_ne_zero (p : X) (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p).source) : unitChartVector J α hs ht p u ≠ 0 := by
  let t := trivializationAt Space (TangentSpace Model) p
  have hb : u.val.proj ∈ t.baseSet := by
    simpa only [t,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hu
  have hv : t.symmL ℝ u.val.proj (unitChartVector J α hs ht p u) = u.val.2 := by
    change t.symmL ℝ u.val.proj ((t u.val).2) = _
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem ℝ t hb]
    exact t.symmL_continuousLinearMapAt hb _
  intro h
  rw [h,map_zero] at hv
  have hh := u.property
  rw [← hv] at hh
  simp at hh

def unitChartJVector (p : X) (u : MetricUnit (hermitianMetric J α hs ht)) : Space :=
  coordinateJ J p (unitChartBase J α hs ht p u) (unitChartVector J α hs ht p u)

def unitChartFirst (p : X) (u : MetricUnit (hermitianMetric J α hs ht)) : Space :=
  first (unitChartVector J α hs ht p u)

def unitChartSecond (p : X) (u : MetricUnit (hermitianMetric J α hs ht)) : Space :=
  second (unitChartVector J α hs ht p u) (unitChartJVector J α hs ht p u)

def unitChartArea (p : X) (u : MetricUnit (hermitianMetric J α hs ht)) : ℝ :=
  area (unitChartVector J α hs ht p u) (unitChartJVector J α hs ht p u)

omit [CompactSpace X] [T2Space X] in
lemma unitChartPlane (p : X) (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p).source) :
    ‖unitChartFirst J α hs ht p u‖ = 1 ∧ ‖unitChartSecond J α hs ht p u‖ = 1 ∧
      ⟪unitChartFirst J α hs ht p u,unitChartSecond J α hs ht p u⟫ = 0 ∧
      0 < unitChartArea J α hs ht p u := by
  have ha := unitChartVector_ne_zero J α hs ht p u hu
  have hab : normalPart (unitChartVector J α hs ht p u) (unitChartJVector J α hs ht p u) ≠ 0 :=
    normalPart_complex_ne_zero _ (coordinateJ_square J p ((extChartAt Model p).map_source hu)) ha
  exact ⟨norm_first ha,norm_second hab,first_second_orthogonal ha _,area_pos ha hab⟩

omit [CompactSpace X] [T2Space X] in
lemma unitChartArea_eval (p : X) (β : TwoForm X) (hβ : IsSmooth β)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p).source) :
    unitEvaluation J (hermitianMetric J α hs ht) β hβ u =
      unitChartArea J α hs ht p u *
        ManifoldForms.pullback β (extChartAt Model p).symm (unitChartBase J α hs ht p u)
          ![unitChartFirst J α hs ht p u,unitChartSecond J α hs ht p u] := by
  rw [← unitChart_eval J α hs ht p β hβ u hu]
  exact alternating_area _ _ _

omit [CompactSpace X] [T2Space X] in
lemma unitChartJVector_continuousOn (p : X) {K : Set Space}
    (hKT : K ⊆ (extChartAt Model p).target) :
    ContinuousOn (unitChartJVector J α hs ht p) (unitChartDomain J α hs ht p K) := by
  exact ((coordinateJ_smooth J p).continuousOn.comp
    (unitChartBase_continuousOn J α hs ht p hKT)
    (fun u hu => hKT (unitChart_mem J α hs ht p hKT hu).2)).clm_apply
      (unitChartVector_continuousOn J α hs ht p hKT)

omit [CompactSpace X] [T2Space X] in
lemma unitChartArea_continuousOn (p : X) {K : Set Space}
    (hKT : K ⊆ (extChartAt Model p).target) :
    ContinuousOn (unitChartArea J α hs ht p) (unitChartDomain J α hs ht p K) := by
  intro u hu
  apply ContinuousAt.comp_continuousWithinAt
    (f := fun v => (unitChartVector J α hs ht p v,unitChartJVector J α hs ht p v))
    (area_continuousAt (b := unitChartJVector J α hs ht p u)
      (unitChartVector_ne_zero J α hs ht p u (unitChart_mem J α hs ht p hKT hu).1))
  exact ((unitChartVector_continuousOn J α hs ht p hKT) u hu).prodMk
    ((unitChartJVector_continuousOn J α hs ht p hKT) u hu)

lemma unitChartArea_bounds (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) :
    ∃ m C : ℝ, 0 < m ∧ 0 < C ∧ ∀ u ∈ unitChartDomain J α hs ht p K,
      m ≤ unitChartArea J α hs ht p u ∧ unitChartArea J α hs ht p u ≤ C := by
  have hS := (unitChartDomain_closed J α hs ht p hK hKT).isCompact
  have hc := unitChartArea_continuousOn J α hs ht p hKT
  have hp : ∀ u ∈ unitChartDomain J α hs ht p K, 0 < unitChartArea J α hs ht p u :=
    fun u hu => (unitChartPlane J α hs ht p u (unitChart_mem J α hs ht p hKT hu).1).2.2.2
  obtain ⟨C,hC⟩ := hS.exists_bound_of_continuousOn hc
  obtain ⟨M,hM⟩ := hS.exists_bound_of_continuousOn (hc.inv₀ (fun u hu => ne_of_gt (hp u hu)))
  refine ⟨(max M 1)⁻¹,max C 1,by positivity,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro u hu
  have hpos := hp u hu
  have hm := hM u hu
  have hc' := hC u hu
  change ‖(unitChartArea J α hs ht p u)⁻¹‖ ≤ M at hm
  rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hpos)] at hm
  rw [Real.norm_eq_abs,abs_of_pos hpos] at hc'
  refine ⟨?_,hc'.trans (le_max_left _ _)⟩
  exact (inv_le_comm₀ hpos (lt_of_lt_of_le zero_lt_one (le_max_right M 1))).mp
    (hm.trans (le_max_left _ _))
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
