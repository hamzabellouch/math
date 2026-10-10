import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeLocalSmooth
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGlobalKernelForms

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] Classical.propDecidable

include hs hE in
lemma globalLeading_continuousAt {t : ℝ} (htp : 0 < t) (x y : X) :
    ContinuousAt (fun v : ℝ × (X × X) => globalLeading J α ht A E v.1 v.2.1 v.2.2) (t,(x,y)) :=
  (globalLeading_continuousOn J α ht A E hE hs).continuousAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds htp)

include hs hE in
lemma globalResidual_continuousAt {t : ℝ} (htp : 0 < t) (x y : X) :
    ContinuousAt (fun v : ℝ × (X × X) => globalResidual J α ht A E v.1 v.2.1 v.2.2) (t,(x,y)) :=
  (globalResidual_continuousOn J α ht A E hE hs).continuousAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds htp)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma smooth_energy_laplacian (a : PreL2 A J α hs ht true) (b : TwoForm X)
    (hb : IsSmooth b) :
    (∫ x, HodgeChart.energyPairing J α ht a.val b x ∂geometricVolume A J α) =
      ∫ x, GeometricAdjoint.pairing J α ht (hodgeLaplacian A J α hs ht a).val b x
        ∂geometricVolume A J α := by
  let b' : PreL2 A J α hs ht true := ⟨b,hb⟩
  have hh := hodgeLaplacian_green A J α hs ht a b'
  rw [hodge_smooth_energy_pair A J α hs ht a b',(smoothL2 A J α hs ht true).inner_map_map,preL2_inner] at hh
  exact hh.symm

namespace GeometricNormalCharts
open HodgeNormalSymbol
variable [T2Space X]
variable (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
lemma leadingSliceForm_weak_laplacian (p : A.centers) {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius)
    {t : ℝ} (htp : 0 < t) (u : W) (a : PreL2 A J α hs ht true) :
    HasDerivAt (fun s => ∫ x, GeometricAdjoint.pairing J α ht a.val
        (leadingSliceForm J α ht A E p q s u) x ∂geometricVolume A J α)
      ((∫ x, GeometricAdjoint.pairing J α ht a.val
        (residualSliceForm J α ht A E p q t u) x ∂geometricVolume A J α) -
       (∫ x, GeometricAdjoint.pairing J α ht (hodgeLaplacian A J α hs ht a).val
        (leadingSliceForm J α ht A E p q t u) x ∂geometricVolume A J α)) t := by
  have hh := leadingSliceForm_weak_deriv J α ht A E hE hs p hq htp u a.val a.property
  rwa [smooth_energy_laplacian A J α hs ht a _
    (leadingSliceForm_smooth J α ht A E hE hs p hq htp u)] at hh

end GeometricNormalCharts
end TamingCompatibility.GeometricHilbert

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeNormalSymbol Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] Classical.propDecidable
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
lemma leadingSliceForm_weak_laplacian_all (p : A.centers) (q : Space)
    {t : ℝ} (htp : 0 < t) (u : W) (a : PreL2 A J α hs ht true) :
    HasDerivAt (fun s => ∫ x, GeometricAdjoint.pairing J α ht a.val
        (leadingSliceForm J α ht A E p q s u) x ∂geometricVolume A J α)
      ((∫ x, GeometricAdjoint.pairing J α ht a.val
        (residualSliceForm J α ht A E p q t u) x ∂geometricVolume A J α) -
       (∫ x, GeometricAdjoint.pairing J α ht (hodgeLaplacian A J α hs ht a).val
        (leadingSliceForm J α ht A E p q t u) x ∂geometricVolume A J α)) t := by
  by_cases hq : q ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius
  · exact leadingSliceForm_weak_laplacian A J α hs ht E hE p hq htp u a
  · have hz : coordinatePartition A p q = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hq (coordinatePartition_centerSupport J α ht A E hE p h))
    have hzero (b : TwoForm X) (x : X) : GeometricAdjoint.pairing J α ht b 0 x = 0 :=
      MetricForms.pairing_zero_right (E := Space) (GeometricAdjoint.pointMetric J α ht x) (b x)
    simp only [leadingSliceForm_zero_center J α ht A E p hz,
      residualSliceForm_zero_center J α ht A E p hz,hzero,integral_zero,sub_self]
    exact hasDerivAt_const t 0

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeNormalSymbol HodgeFrame Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] Classical.propDecidable
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma pairing_zero_form (b : TwoForm X) (x : X) : GeometricAdjoint.pairing J α ht b 0 x = 0 :=
  MetricForms.pairing_zero_right (E := Space) (GeometricAdjoint.pointMetric J α ht x) (b x)

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma pairing_sum_form {ι : Type*} (s : Finset ι) (b : TwoForm X) (f : ι → TwoForm X) (x : X) :
    GeometricAdjoint.pairing J α ht b (∑ i ∈ s, f i) x =
      ∑ i ∈ s, GeometricAdjoint.pairing J α ht b (f i) x := by
  change MetricForms.pairingCLM (GeometricAdjoint.pointMetric J α ht x) 2 (b x) _ = _
  erw [Finset.sum_apply,map_sum]
  rfl

include hs in
omit [T2Space X] in
lemma integral_pairing_sum {ι : Type*} (s : Finset ι) (b : TwoForm X) (hb : IsSmooth b)
    (f : ι → TwoForm X) (hf : ∀ i ∈ s, IsSmooth (f i)) :
    (∫ x, GeometricAdjoint.pairing J α ht b (∑ i ∈ s, f i) x ∂geometricVolume A J α) =
      ∑ i ∈ s, ∫ x, GeometricAdjoint.pairing J α ht b (f i) x ∂geometricVolume A J α := by
  let := geometricVolume_finite A J α hs ht
  simp_rw [pairing_sum_form]
  apply integral_finsetSum
  intro i hi
  exact (GeometricAdjoint.pairing_two_smooth J α hs ht hb (hf i hi)).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

include hE in
lemma leadingFiberForm_weak_laplacian (p : A.centers) (y : X)
    {t : ℝ} (htp : 0 < t) (v : FrameSpace A) (a : PreL2 A J α hs ht true) :
    HasDerivAt (fun s => ∫ x, GeometricAdjoint.pairing J α ht a.val
        (leadingFiberForm J α ht A E p y s v) x ∂geometricVolume A J α)
      ((∫ x, GeometricAdjoint.pairing J α ht a.val
        (residualFiberForm J α ht A E p y t v) x ∂geometricVolume A J α) -
       (∫ x, GeometricAdjoint.pairing J α ht (hodgeLaplacian A J α hs ht a).val
        (leadingFiberForm J α ht A E p y t v) x ∂geometricVolume A J α)) t := by
  unfold leadingFiberForm residualFiberForm
  by_cases hy : y ∈ (extChartAt Model p.val).source
  · simp only [ite_eq_left hy]
    exact leadingSliceForm_weak_laplacian_all A J α hs ht E hE p _ htp _ a
  · simp only [ite_eq_right hy,pairing_zero_form,integral_zero,sub_self]
    exact hasDerivAt_const t 0

include hE in
lemma leadingKernelForm_weak_laplacian (y : X)
    {t : ℝ} (htp : 0 < t) (v : FrameSpace A) (a : PreL2 A J α hs ht true) :
    HasDerivAt (fun s => ∫ x, GeometricAdjoint.pairing J α ht a.val
        (leadingKernelForm J α ht A E s y v) x ∂geometricVolume A J α)
      ((∫ x, GeometricAdjoint.pairing J α ht a.val
        (residualKernelForm J α ht A E t y v) x ∂geometricVolume A J α) -
       (∫ x, GeometricAdjoint.pairing J α ht (hodgeLaplacian A J α hs ht a).val
        (leadingKernelForm J α ht A E t y v) x ∂geometricVolume A J α)) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun p _ =>
    leadingFiberForm_weak_laplacian A J α hs ht E hE p y htp v a)
  rw [Finset.sum_sub_distrib] at hd
  have he : (fun s => ∫ x, GeometricAdjoint.pairing J α ht a.val
        (leadingKernelForm J α ht A E s y v) x ∂geometricVolume A J α) =ᶠ[𝓝 t]
      (fun s => ∑ p : A.centers, ∫ x, GeometricAdjoint.pairing J α ht a.val
        (leadingFiberForm J α ht A E p y s v) x ∂geometricVolume A J α) := by
    filter_upwards [eventually_gt_nhds htp] with s hsp
    rw [leadingKernelForm,ite_eq_left hsp]
    exact integral_pairing_sum A J α hs ht _ a.val a.property _ (fun p _ =>
      leadingFiberForm_smooth J α ht A E hE hs p y hsp v)
  have hr := integral_pairing_sum A J α hs ht Finset.univ a.val a.property
    (fun p => residualFiberForm J α ht A E p y t v) (fun p _ =>
      residualFiberForm_smooth J α ht A E hE hs p y htp v)
  have hl := integral_pairing_sum A J α hs ht Finset.univ (hodgeLaplacian A J α hs ht a).val
    (hodgeLaplacian A J α hs ht a).property (fun p => leadingFiberForm J α ht A E p y t v)
    (fun p _ => leadingFiberForm_smooth J α ht A E hE hs p y htp v)
  rw [residualKernelForm,leadingKernelForm,ite_eq_left htp,ite_eq_left htp,hr,hl]
  exact hd.congr_of_eventuallyEq he

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
