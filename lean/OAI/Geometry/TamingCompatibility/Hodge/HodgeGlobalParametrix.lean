import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGaussianSchur
import OAI.Geometry.TamingCompatibility.Hodge.HodgeManifoldKernelExtension

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] Classical.propDecidable

def assemble (K : A.centers → ℝ → Space × Space → FrameSpace A →L[ℝ] FrameSpace A)
    (t : ℝ) (x y : X) : FrameSpace A →L[ℝ] FrameSpace A :=
  if 0 < t then ∑ p : A.centers, ManifoldKernelExtension.push p.val (K p t) (y,x) else 0

def globalLeading := assemble A (leadingMatrix J α ht A D)
def globalResidual := assemble A (residualMatrix J α ht A D)

omit [T2Space X] [CompactSpace X] in
lemma physicalCompact_target (p : A.centers) :
    (D p).physicalCompact ⊆ (extChartAt Model p.val).target ×ˢ (extChartAt Model p.val).target :=
  fun _ hz => ⟨(D p).chart.domain_subset ((D p).physicalCompact_domain hz).1,
    (D p).chart.domain_subset ((D p).physicalCompact_domain hz).2⟩

omit [CompactSpace X] in
lemma assemble_continuousOn
    (K : A.centers → ℝ → Space × Space → FrameSpace A →L[ℝ] FrameSpace A)
    (hsupp : ∀ p t, Function.support (K p t) ⊆ (D p).physicalCompact)
    (hcont : ∀ p t, 0 < t → ∀ z, ContinuousAt (fun v : ℝ × (Space × Space) => K p v.1 v.2) (t,z)) :
    ContinuousOn (fun v : ℝ × (X × X) => assemble A K v.1 v.2.1 v.2.2) {v | 0 < v.1} := by
  intro v hv
  apply ContinuousAt.continuousWithinAt
  have hc : ContinuousAt (fun w : ℝ × (X × X) =>
      ∑ p : A.centers, ManifoldKernelExtension.push p.val (K p w.1) (w.2.2,w.2.1)) v := by
    apply tendsto_finsetSum
    intro p _
    have hh := ManifoldKernelExtension.push_joint_continuousAt p.val (K p) (D p).physicalCompact
      (D p).physicalCompact_compact (physicalCompact_target J α ht A D p) (hsupp p) v.1
      (hcont p v.1 hv) (v.2.2,v.2.1)
    exact hh.comp (f := fun w : ℝ × (X × X) => (w.1,(w.2.2,w.2.1)))
      (continuousAt_fst.prodMk (continuousAt_snd.snd.prodMk continuousAt_snd.fst))
  apply hc.congr_of_eventuallyEq
  have hn : {w : ℝ × (X × X) | 0 < w.1} ∈ 𝓝 v :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds hv
  filter_upwards [hn] with w hw
  exact ite_eq_left hw

include hD in
lemma globalLeading_continuousOn (hs : IsSmooth α) :
    ContinuousOn (fun v : ℝ × (X × X) => globalLeading J α ht A D v.1 v.2.1 v.2.2) {v | 0 < v.1} :=
  assemble_continuousOn J α ht A D _
    (fun p t => (coordinateMatrix_support J α ht A D p _).trans
      ((subset_tsupport _).trans (partitionLeading_tsupport J α ht A D hD p t)))
    (fun p _ htpos z => (leadingMatrix_smooth J α ht A D hD hs p htpos z).continuousAt)

include hD in
lemma globalResidual_continuousOn (hs : IsSmooth α) :
    ContinuousOn (fun v : ℝ × (X × X) => globalResidual J α ht A D v.1 v.2.1 v.2.2) {v | 0 < v.1} :=
  assemble_continuousOn J α ht A D _
    (fun p t => (coordinateMatrix_support J α ht A D p _).trans
      ((subset_tsupport _).trans (partitionResidual_tsupport J α ht A D hD p t)))
    (fun p _ htpos z => (residualMatrix_smooth J α ht A D hD hs p htpos z).continuousAt)

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

omit [CompactSpace X] in
lemma assemble_measurable
    (K : A.centers → ℝ → Space × Space → FrameSpace A →L[ℝ] FrameSpace A)
    (hsupp : ∀ p t, Function.support (K p t) ⊆ (D p).physicalCompact)
    (hcont : ∀ p t, 0 < t → ∀ z, ContinuousAt (fun v : ℝ × (Space × Space) => K p v.1 v.2) (t,z)) :
    VolterraKernel.MeasurableKernel (assemble A K) := by
  have hc := assemble_continuousOn J α ht A D K hsupp hcont
  have hm := hc.measurable_piecewise (continuousOn_const (c := (0 : FrameSpace A →L[ℝ] FrameSpace A)))
    (isOpen_lt continuous_const continuous_fst).measurableSet
  have he : {v : ℝ × (X × X) | 0 < v.1}.piecewise
      (fun v => assemble A K v.1 v.2.1 v.2.2) (fun _ => 0) =
      (fun v => assemble A K v.1 v.2.1 v.2.2) := by
    funext v
    by_cases hv : 0 < v.1
    · exact ite_eq_left hv
    · simp only [Set.piecewise,Set.mem_ofPred_eq,ite_eq_right hv,assemble]
  rw [he] at hm
  exact hm.stronglyMeasurable

include hD in
lemma globalLeading_measurable (hs : IsSmooth α) :
    VolterraKernel.MeasurableKernel (globalLeading J α ht A D) :=
  assemble_measurable J α ht A D _
    (fun p t => (coordinateMatrix_support J α ht A D p _).trans
      ((subset_tsupport _).trans (partitionLeading_tsupport J α ht A D hD p t)))
    (fun p _ htpos z => (leadingMatrix_smooth J α ht A D hD hs p htpos z).continuousAt)

include hD in
lemma globalResidual_measurable (hs : IsSmooth α) :
    VolterraKernel.MeasurableKernel (globalResidual J α ht A D) :=
  assemble_measurable J α ht A D _
    (fun p t => (coordinateMatrix_support J α ht A D p _).trans
      ((subset_tsupport _).trans (partitionResidual_tsupport J α ht A D hD p t)))
    (fun p _ htpos z => (residualMatrix_smooth J α ht A D hD hs p htpos z).continuousAt)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeNormalSymbol HodgeFrame Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] Classical.propDecidable
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

omit [CompactSpace X] [T2Space X] in
lemma frameEncode_manifoldTest (p : A.centers) (f : Space → W)
    (hfd : tsupport f ⊆ (E p).chart.domain) (x : X) :
    frameEncode J α ht A E x (HodgeChart.manifoldTest J α ht p.val (E p).chart f x) =
      if x ∈ (extChartAt Model p.val).source then
        coordinateEncode J α ht A E p (extChartAt Model p.val x) (f (extChartAt Model p.val x)) else 0 := by
  by_cases hx : x ∈ (extChartAt Model p.val).source
  · rw [ite_eq_left hx]
    by_cases hfx : extChartAt Model p.val x ∈ tsupport f
    · have hd := hfd hfx
      have hr : HodgeChart.rawVector J α ht p.val (E p).chart
          (HodgeChart.manifoldTest J α ht p.val (E p).chart f) (extChartAt Model p.val x) =
          f (extChartAt Model p.val x) := by
        unfold HodgeChart.rawVector
        rw [HodgeChart.pullback_manifoldTest J α ht p.val (E p).chart f
          ((extChartAt Model p.val).map_source hx)]
        exact coordinates_reconstruct _ _ ((E p).chart.frame_gram _ hd) _
      have hh := coordinateEncode_rawVector J α ht A E p
        (HodgeChart.manifoldTest J α ht p.val (E p).chart f) hd
      rw [hr,(extChartAt Model p.val).left_inv hx] at hh
      exact hh.symm
    · have hz := image_eq_zero_of_notMem_tsupport hfx
      erw [hz,map_zero,HodgeChart.manifoldTest_zero_off J α ht p.val (E p).chart f,map_zero]
      rintro ⟨z,hz,he⟩
      have heq : extChartAt Model p.val x = z := by
        rw [← he,(extChartAt Model p.val).right_inv ((E p).chart.domain_subset (hfd hz))]
      exact hfx (heq ▸ hz)
  · erw [ite_eq_right hx,HodgeChart.manifoldTest_zero_off J α ht p.val (E p).chart f,map_zero]
    rintro ⟨z,hz,rfl⟩
    exact hx ((extChartAt Model p.val).map_target ((E p).chart.domain_subset (hfd hz)))

include hE in
omit [T2Space X] in
lemma leadingSlice_domain_all (p : A.centers) (q : Space) (t : ℝ) (u : W) :
    tsupport (leadingSlice J α ht A E p q t u) ⊆ (E p).chart.domain := by
  by_cases hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius
  · exact leadingSlice_domain J α ht A E p hq t u
  · have hz : coordinatePartition A p q = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hq (coordinatePartition_centerSupport J α ht A E hE p h))
    have he : leadingSlice J α ht A E p q t u = 0 := by
      funext y
      simp only [leadingSlice,partitionLeading_zero_center J α ht A E p hz t y,zero_apply,Pi.zero_apply]
    rw [he,tsupport_zero]
    exact empty_subset _

include hE in
omit [T2Space X] in
lemma residualSlice_domain_all (p : A.centers) (q : Space) (t : ℝ) (u : W) :
    tsupport (residualSlice J α ht A E p q t u) ⊆ (E p).chart.domain := by
  by_cases hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius
  · exact residualSlice_domain J α ht A E p hq t u
  · have hz : coordinatePartition A p q = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hq (coordinatePartition_centerSupport J α ht A E hE p h))
    have he : residualSlice J α ht A E p q t u = 0 := by
      funext y
      simp only [residualSlice,partitionResidual_zero_center J α ht A E p hz t y,zero_apply,Pi.zero_apply]
    rw [he,tsupport_zero]
    exact empty_subset _

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
