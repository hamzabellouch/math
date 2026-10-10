import Mathlib
import OAI.Analysis.SymmetricDomains.WeightedChartTwoSided
import OAI.Analysis.SymmetricDomains.OffsetDerivative

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open scoped Classical
namespace NashBoundaryChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

lemma family_zero_not_mem (c : NashBoundaryChart (m := m) U V B q) (s) :
    0 ∉ c.family s := by
  intro h
  have hs := h.1
  have hbd := (c.graph_boundary s hs).1.2
  exact hbd (by simpa only [add_zero] using h.2.2)
end NashBoundaryChart

namespace NashBoundaryScalingChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N} {c : NashBoundaryChart (m := m) U V B q}
variable {x : Fin d → ℝ}

theorem two_sided (s : NashBoundaryScalingChart c x) (hgood : c.GoodAt x)
    (f : (Fin c.normal.normalDim → ℝ) → ℝ)
    (hf : ∀ y, Tendsto (fun p : (Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ) × ℝ =>
      offsetDistance c.family p.1 p.2 y)
      (𝓝[{p : (Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ) × ℝ | 0 < p.2}]
        (c.normal.parameters x,0)) (𝓝 (f y)))
    (hfnonneg : ∀ y, 0 ≤ f y) :
    ∃ Q : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Affine s.tangentDim) (Fin c.normal.normalDim → ℝ),
      let R : Affine s.tangentDim × Affine s.normalDim → (Fin c.normal.normalDim → ℝ) :=
        fun z => s.normalMap (Flatten.imaginaryPart s.normalDim z.2)+Q (fun _ => z.1)
      (∀ K : Set (Affine s.tangentDim × Affine s.normalDim), IsCompact K → K ⊆ {z | f (R z) ≠ 0} →
        ∀ᶠ t : ℝ in 𝓝[>] 0, K ⊆ chartScaledDomain s.offsets c.family t) ∧
      (∀ z : Affine s.tangentDim × Affine s.normalDim, f (R z) = 0 → ∀ t : ℕ → ℝ,
        Tendsto t atTop (𝓝 0) → (∀ j, 0 < t j) →
        ∃ y : ℕ → Affine s.tangentDim × Affine s.normalDim, Tendsto y atTop (𝓝 z) ∧
          (∀ j, y j ∉ chartScaledDomain s.offsets c.family (t j)) ∧
          ∀ j, weightedScale (t j) (y j) ∈ s.offsets.source) := by
  have hlin : ∀ z : Affine s.tangentDim, fderiv ℝ (fun y => (s.offsets y).2) 0 (z,0) = 0 := by
    intro z
    rw [s.offset_derivative hgood]
    simp only [map_zero]
  have hjoint : ∀ (a : ℕ → (Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ))
      (t : ℕ → ℝ), Tendsto a atTop (𝓝 (c.normal.parameters x)) → Tendsto t atTop (𝓝 0) →
      (∀ j, 0 < t j) → ∀ v, Tendsto (fun j => offsetDistance c.family (a j) (t j) v) atTop (𝓝 (f v)) := by
    intro a t ha ht htp v
    have hp : Tendsto (fun j => (a j,t j)) atTop
        (𝓝[{p : (Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ) × ℝ | 0 < p.2}]
          (c.normal.parameters x,0)) :=
      tendsto_nhdsWithin_iff.mpr ⟨ha.prodMk_nhds ht,Eventually.of_forall htp⟩
    exact Filter.Tendsto.comp (f := fun j => (a j,t j)) (g := fun p => offsetDistance c.family p.1 p.2 v) (hf v) hp
  obtain ⟨Q,hQ⟩ := weighted_chart_two_sided s.offsets c.family s.source_zero s.offsets_zero
    s.inverse_analytic.contDiffAt (c.family_zero_not_mem) (analyticAt_snd.comp s.analytic) hlin f hfnonneg hjoint
  refine ⟨Q,?_⟩
  simpa only [s.offset_derivative hgood] using hQ

theorem exists_cutoff (s : NashBoundaryScalingChart c x) (hgood : c.GoodAt x) :
    ∃ s' : NashBoundaryScalingChart c x,
      s'.tangentDim=s.tangentDim ∧ s'.normalDim=s.normalDim ∧
      ∀ z ∈ s'.offsets.source,
        c.oldParameter (s'.coordinates.symm z+c.oldPosition (c.normal.parameters x)) ∈ ball 0 c.graphRadius ∧
        ‖complexRealEquiv m (s'.coordinates.symm z+c.oldPosition (c.normal.parameters x))‖ < c.chart.radius ∧
        ‖c.oldOffset (s'.coordinates.symm z+c.oldPosition (c.normal.parameters x))‖ < 1 := by
  let a := c.oldPosition (c.normal.parameters x)
  have hs : ∀ᶠ z : Affine s.tangentDim × Affine s.normalDim in 𝓝 0,
      c.oldParameter (s.coordinates.symm z+a) ∈ ball 0 c.graphRadius := by
    have hcont : ContinuousAt (fun z => c.oldParameter (s.coordinates.symm z+a)) 0 :=
      (continuous_fst.comp (c.normal.realCoordinates.continuous.comp
        (s.coordinates.symm.continuous.add continuous_const))).continuousAt
    apply hcont.preimage_mem_nhds
    simpa only [map_zero,zero_add,a,c.oldParameter_oldPosition] using isOpen_ball.mem_nhds hgood.2.1
  have hn : ∀ᶠ z : Affine s.tangentDim × Affine s.normalDim in 𝓝 0,
      ‖complexRealEquiv m (s.coordinates.symm z+a)‖ < c.chart.radius := by
    have hcont : ContinuousAt (fun z => ‖complexRealEquiv m (s.coordinates.symm z+a)‖) 0 :=
      ((complexRealEquiv m).continuous.comp (s.coordinates.symm.continuous.add continuous_const)).norm.continuousAt
    apply hcont.eventually_lt continuousAt_const
    simpa only [map_zero,zero_add,a,NashBoundaryChart.oldPosition] using (c.graph_boundary _ hgood.2.1).2.1
  have hv : ∀ᶠ z : Affine s.tangentDim × Affine s.normalDim in 𝓝 0,
      ‖c.oldOffset (s.coordinates.symm z+a)‖ < 1 := by
    have ha : ContinuousAt (fun z : Affine s.tangentDim × Affine s.normalDim => s.coordinates.symm z+a) 0 :=
      (s.coordinates.symm.continuous.add continuous_const).continuousAt
    have hc : ContinuousAt c.oldOffset (s.coordinates.symm 0+a) := by
      simpa only [map_zero,zero_add,a] using (c.oldOffset_analyticAt hgood.2.1).continuousAt
    apply (hc.comp (f := fun z : Affine s.tangentDim × Affine s.normalDim => s.coordinates.symm z+a) (x := 0) ha).norm.eventually_lt continuousAt_const
    simp only [Function.comp_apply,map_zero,zero_add,a,c.oldOffset_oldPosition,norm_zero,zero_lt_one]
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp (hs.and (hn.and hv))
  let e := s.offsets.restr (ball 0 r)
  have he : (0 : Affine s.tangentDim × Affine s.normalDim) ∈ e.source := by
    rw [OpenPartialHomeomorph.restr_source' _ _ isOpen_ball]
    exact ⟨s.source_zero,mem_ball_self hr⟩
  let s' : NashBoundaryScalingChart c x := {s with offsets := e, source_zero := he}
  refine ⟨s',rfl,rfl,?_⟩
  intro z hz
  have hzr : z ∈ ball 0 r := by
    exact (show z ∈ s.offsets.source ∩ ball 0 r from by
      simpa only [s',e,OpenPartialHomeomorph.restr_source' _ _ isOpen_ball] using hz).2
  exact hrsub hzr
end NashBoundaryScalingChart
end Release061

end

end OAI
