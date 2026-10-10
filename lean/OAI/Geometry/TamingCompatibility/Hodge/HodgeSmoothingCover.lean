import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeLocalEvaluation

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

structure HodgeSmoothingPatch (r : ℝ) (hr : 0 < r) where
  chart : A.centers
  center : Space
  smoothing : LocalHodgeSmoothing A J α hs ht D hD chart center r hr

namespace HodgeSmoothingPatch
variable {A J α hs ht D hD} {r : ℝ} {hr : 0 < r}
variable (P : HodgeSmoothingPatch A J α hs ht D hD r hr)
def source : Set X := (extChartAt Model P.chart.val).source ∩
  (extChartAt Model P.chart.val) ⁻¹' P.smoothing.neighborhood
omit [T2Space X] in
lemma source_open : IsOpen P.source :=
  (continuousOn_extChartAt P.chart.val).isOpen_inter_preimage
    (isOpen_extChartAt_source P.chart.val) P.smoothing.neighborhood_open
omit [T2Space X] in
lemma source_subset : P.source ⊆ (extChartAt Model P.chart.val).source := inter_subset_left
omit [T2Space X] in
lemma source_image_subset : (extChartAt Model P.chart.val) '' P.source ⊆ P.smoothing.neighborhood := by
  rintro z ⟨x,hx,rfl⟩
  exact hx.2
end HodgeSmoothingPatch

lemma exists_hodgeSmoothingPatch (r : ℝ) (hr : 0 < r) (x : X) :
    ∃ P : HodgeSmoothingPatch A J α hs ht D hD r hr, x ∈ P.source := by
  obtain ⟨p,hp,hxp⟩ := exists_nonzero_weight_chart A J α ht (fun p => (D p).toData) hD x
  have hxs : x ∈ (extChartAt Model p.val).source := (A.subordinate p) (subset_closure hp)
  have hw : coordinateWeight A p (extChartAt Model p.val x) ≠ 0 := by
    simpa only [coordinateWeight,(extChartAt Model p.val).left_inv hxs] using hp
  let L := localHodgeSmoothing A J α hs ht D hD p (extChartAt Model p.val x) hxp hw r hr
  exact ⟨⟨p,extChartAt Model p.val x,L⟩,hxs,L.center_mem⟩

structure HodgeSmoothingCover (r : ℝ) (hr : 0 < r) where
  centers : Finset X
  patch : centers → HodgeSmoothingPatch A J α hs ht D hD r hr
  partition : SmoothPartitionOfUnity centers Model X
  subordinate : partition.IsSubordinate (fun i => (patch i).source)

lemma hodgeSmoothingCover_nonempty (r : ℝ) (hr : 0 < r) :
    Nonempty (HodgeSmoothingCover A J α hs ht D hD r hr) := by
  classical
  choose P hP using exists_hodgeSmoothingPatch A J α hs ht D hD r hr
  obtain ⟨s,hcover⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (P x).source)
    (fun x => (P x).source_open) (fun x _ => mem_iUnion_of_mem x (hP x))
  have hc : (univ : Set X) ⊆ ⋃ i : s, (P i.val).source := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion_of_mem ⟨i,hi⟩ hxi
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate Model isClosed_univ
    (fun i : s => (P i.val).source) (fun i => (P i.val).source_open) hc
  exact ⟨⟨s,fun i => P i.val,ρ,hρ⟩⟩

def hodgeSmoothingCover (r : ℝ) (hr : 0 < r) : HodgeSmoothingCover A J α hs ht D hD r hr :=
  Classical.choice (hodgeSmoothingCover_nonempty A J α hs ht D hD r hr)
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source}
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)

def coordinateSupport (i : C.centers) : Set Space :=
  (extChartAt Model (C.patch i).chart.val) '' tsupport (C.partition i)

lemma coordinateSupport_compact (i : C.centers) : IsCompact (C.coordinateSupport i) := by
  apply (isClosed_tsupport _).isCompact.image_of_continuousOn
  exact (continuousOn_extChartAt _).mono ((C.subordinate i).trans (C.patch i).source_subset)

lemma coordinateSupport_neighborhood (i : C.centers) :
    C.coordinateSupport i ⊆ (C.patch i).smoothing.neighborhood := by
  rintro z ⟨x,hx,rfl⟩
  exact (C.subordinate i hx).2

lemma coordinateSupport_target (i : C.centers) :
    C.coordinateSupport i ⊆ (extChartAt Model (C.patch i).chart.val).target :=
  (C.coordinateSupport_neighborhood i).trans
    ((C.patch i).smoothing.neighborhood_subset.trans (D (C.patch i).chart).toData.domain_subset)

def weightFunction (i : C.centers) : Space → ℝ :=
  (extChartAt Model (C.patch i).chart.val).target.indicator
    (fun z => C.partition i ((extChartAt Model (C.patch i).chart.val).symm z))

lemma weightFunction_smooth_compact (i : C.centers) :
    ContDiff ℝ ∞ (C.weightFunction i) ∧ HasCompactSupport (C.weightFunction i) := by
  apply smooth_indicator_of_compact (isOpen_extChartAt_target _)
    (C.coordinateSupport_compact i) (C.coordinateSupport_target i)
  · exact (C.partition i).contMDiff.comp_contMDiffOn
      (contMDiffOn_extChartAt_symm _) |>.contDiffOn
  · intro z hz hn
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hn ⟨_,h,(extChartAt Model (C.patch i).chart.val).right_inv hz⟩

lemma weightFunction_support (i : C.centers) : tsupport (C.weightFunction i) ⊆ C.coordinateSupport i := by
  apply closure_minimal _ (C.coordinateSupport_compact i).isClosed
  intro z hz
  by_cases ht : z ∈ (extChartAt Model (C.patch i).chart.val).target
  · refine ⟨(extChartAt Model (C.patch i).chart.val).symm z,?_,
      (extChartAt Model (C.patch i).chart.val).right_inv ht⟩
    apply subset_closure
    simpa only [Function.mem_support,weightFunction,indicator_of_mem ht] using hz
  · exact False.elim (hz (indicator_of_notMem ht _))

def weight (i : C.centers) : 𝓢(Space,ℝ) :=
  (C.weightFunction_smooth_compact i).2.toSchwartzMap (C.weightFunction_smooth_compact i).1

lemma weight_support (i : C.centers) : tsupport (C.weight i) ⊆ (C.patch i).smoothing.neighborhood :=
  (C.weightFunction_support i).trans (C.coordinateSupport_neighborhood i)

lemma weight_compact (i : C.centers) : HasCompactSupport (C.weight i : Space → ℝ) :=
  (C.weightFunction_smooth_compact i).2

lemma weight_chart (i : C.centers) {x : X}
    (hx : x ∈ (extChartAt Model (C.patch i).chart.val).source) :
    C.weight i (extChartAt Model (C.patch i).chart.val x) = C.partition i x := by
  change (C.weightFunction i) _ = _
  rw [weightFunction,indicator_of_mem ((extChartAt Model (C.patch i).chart.val).map_source hx),
    (extChartAt Model (C.patch i).chart.val).left_inv hx]

variable [T2Space X]

def basisForm (i : C.centers) (j : Fin 6) : PreL2 A J α hs ht true :=
  hodgeTest A J α hs ht D (C.patch i).chart (componentTest j (C.weight i))
    (full_componentTest_compact j (C.weight i) (C.weight_compact i))
    ((full_componentTest_support j (C.weight i)).trans
      ((C.weight_support i).trans (C.patch i).smoothing.neighborhood_subset))

lemma basisForm_zero (i : C.centers) (j : Fin 6) {x : X}
    (hx : x ∉ tsupport (C.partition i)) : (C.basisForm i j).val x = 0 := by
  apply manifoldTest_zero_off
  rintro ⟨z,hz,rfl⟩
  have hs : z ∈ C.coordinateSupport i :=
    C.weightFunction_support i (full_componentTest_support j (C.weight i) hz)
  obtain ⟨y,hy,rfl⟩ := hs
  exact hx (by rwa [(extChartAt Model (C.patch i).chart.val).left_inv
    ((C.subordinate i hy).1)])
end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
