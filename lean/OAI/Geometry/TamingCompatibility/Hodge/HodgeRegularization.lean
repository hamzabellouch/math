import Mathlib
import OAI.Geometry.TamingCompatibility.Currents.GeometricSeparatingProbability
import OAI.Geometry.TamingCompatibility.DifferentialForms.SmoothingKernel
import OAI.Geometry.TamingCompatibility.Hodge.HodgeSmoothingCover
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGlobalEvaluation

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source}
attribute [local instance] unitMeasurable unitBorel unitT2
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)
variable (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

def evaluationVector (u : MetricUnit g) : L2 A J α hs ht true :=
  (C.evaluation g u).adjoint 1

lemma evaluationVector_continuous : Continuous (C.evaluationVector g) :=
  ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := L2 A J α hs ht true) (F := ℝ)).continuous.comp
    (C.evaluation_continuous g)).clm_apply continuous_const

lemma evaluationVector_integrable (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] :
    Integrable (C.evaluationVector g) μ :=
  (C.evaluationVector_continuous g).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def regularize (μ : Measure (MetricUnit g)) : L2 A J α hs ht true :=
  ∫ u, C.evaluationVector g u ∂μ

lemma regularize_pair (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ]
    (f : L2 A J α hs ht true) :
    ⟪C.regularize g μ,f⟫ = ∫ u, C.evaluation g u f ∂μ := by
  have h := HilbertKernel.regularize_pair μ (C.evaluation g) (fun _ => (1:ℝ))
    (C.evaluationVector_integrable g μ) f
  simpa only [HilbertKernel.regularize,regularize,evaluationVector,Real.inner_apply,one_mul,mul_one] using h

def innerKernel (u v : MetricUnit g) : ℝ :=
  ⟪C.evaluationVector g u,C.evaluationVector g v⟫

lemma innerKernel_continuous : Continuous (fun p : MetricUnit g × MetricUnit g => C.innerKernel g p.1 p.2) :=
  ((C.evaluationVector_continuous g).comp continuous_fst).inner
    ((C.evaluationVector_continuous g).comp continuous_snd)

lemma regularize_inner (μ ν : Measure (MetricUnit g)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ⟪C.regularize g μ,C.regularize g ν⟫ =
      ∫ u, ∫ v, C.innerKernel g u v ∂ν ∂μ := by
  have h := HilbertKernel.regularize_kernel_pair μ ν (C.evaluation g) (C.evaluation g)
    (fun _ => (1:ℝ)) (fun _ => (1:ℝ))
    (C.evaluationVector_integrable g μ) (C.evaluationVector_integrable g ν)
  simpa only [regularize,HilbertKernel.regularize,innerKernel,evaluationVector,
    HilbertKernel.kernel_inner] using h

def wedgeKernel (u v : MetricUnit g) : ℝ :=
  ⟪C.evaluationVector g u,l2Star A J α hs ht (C.evaluationVector g v)⟫

lemma wedgeKernel_continuous : Continuous (fun p : MetricUnit g × MetricUnit g => C.wedgeKernel g p.1 p.2) :=
  ((C.evaluationVector_continuous g).comp continuous_fst).inner
    ((l2Star A J α hs ht).continuous.comp ((C.evaluationVector_continuous g).comp continuous_snd))

lemma regularize_wedge (μ ν : Measure (MetricUnit g)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ⟪C.regularize g μ,l2Star A J α hs ht (C.regularize g ν)⟫ =
      ∫ u, ∫ v, C.wedgeKernel g u v ∂ν ∂μ := by
  have hν := C.evaluationVector_integrable g ν
  have hμ := C.evaluationVector_integrable g μ
  rw [regularize,regularize,← (l2Star A J α hs ht).integral_comp_comm hν]
  have hi : Integrable (fun v => l2Star A J α hs ht (C.evaluationVector g v)) ν :=
    (l2Star A J α hs ht).integrable_comp hν
  have hp := (innerSL ℝ (∫ v, l2Star A J α hs ht (C.evaluationVector g v) ∂ν)).integral_comp_comm hμ
  simp only [innerSL_apply_apply] at hp
  rw [real_inner_comm,← hp]
  apply integral_congr_ae
  filter_upwards [] with u
  have h := (innerSL ℝ (C.evaluationVector g u)).integral_comp_comm hi
  simpa only [innerSL_apply_apply,wedgeKernel,real_inner_comm] using h.symm

lemma regularize_add (μ ν : Measure (MetricUnit g)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    C.regularize g (μ+ν) = C.regularize g μ+C.regularize g ν :=
  integral_add_measure (C.evaluationVector_integrable g μ) (C.evaluationVector_integrable g ν)
end HodgeSmoothingCover
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
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source}
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)

omit [T2Space X] in
lemma coordinate_basis_expansion (i : C.centers) (a : TwoForm X) {z : Space}
    (hz : z ∈ (D (C.patch i).chart).domain) :
    ∑ j : Fin 6, rawVector J α ht (C.patch i).chart.val (D (C.patch i).chart).toData a z j •
      coordinateTest J α ht (C.patch i).chart.val (D (C.patch i).chart).toData
        (componentTest j (C.weight i)) z =
      C.weight i z • ManifoldForms.pullback a (extChartAt Model (C.patch i).chart.val).symm z := by
  let R := HodgeFrame.reconstruct (coordinateMetric J α ht (C.patch i).chart.val z)
    (fun k => (D (C.patch i).chart).frame k z)
  let v := rawVector J α ht (C.patch i).chart.val (D (C.patch i).chart).toData a z
  have hv : ∑ j : Fin 6, v j • (C.weight i z • EuclideanSpace.single j (1:ℝ)) = C.weight i z • v := by
    ext k
    simp [WithLp.ofLp_sum,PiLp.smul_apply,EuclideanSpace.single,Pi.single_apply,smul_eq_mul,mul_ite,mul_comm]
  change ∑ j : Fin 6, v j • R (componentTest j (C.weight i) z) = _
  simp only [componentTest_apply]
  simp only [← map_smul]
  rw [← map_sum]
  rw [hv,map_smul]
  exact congrArg (C.weight i z • ·) (rawVector_expansion J α ht (C.patch i).chart.val
    (D (C.patch i).chart).toData a hz)

lemma basisForm_expansion (i : C.centers) (a : TwoForm X) {x : X}
    (hx : x ∈ tsupport (C.partition i)) :
    ∑ j : Fin 6, rawVector J α ht (C.patch i).chart.val (D (C.patch i).chart).toData a
      (extChartAt Model (C.patch i).chart.val x) j • (C.basisForm i j).val x =
      C.partition i x • a x := by
  classical
  have hxs := (C.subordinate i hx).1
  have hxD := (C.patch i).smoothing.neighborhood_subset (C.subordinate i hx).2
  let z := extChartAt Model (C.patch i).chart.val x
  let L : TangentSpace Model x →L[ℝ] Space := mfderiv Model Model (extChartAt Model (C.patch i).chart.val) x
  have hi := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := Model) hxs
  simp only [Model,modelWithCornersSelf_coe,Set.range_id,mfderivWithin_univ] at hi
  have he := C.coordinate_basis_expansion i a hxD
  have he' := congrArg (ContinuousAlternatingMap.compContinuousLinearMapCLM L) he
  change (ContinuousAlternatingMap.compContinuousLinearMapCLM L) (∑ j : Fin 6,
    rawVector J α ht (C.patch i).chart.val (D (C.patch i).chart).toData a z j •
      coordinateTest J α ht (C.patch i).chart.val (D (C.patch i).chart).toData
        (componentTest j (C.weight i)) z) =
    (ContinuousAlternatingMap.compContinuousLinearMapCLM L)
      (C.weight i z • ManifoldForms.pullback a (extChartAt Model (C.patch i).chart.val).symm z) at he'
  rw [map_sum] at he'
  simp only [map_smul] at he'
  change (∑ j : Fin 6, rawVector J α ht (C.patch i).chart.val (D (C.patch i).chart).toData a z j • (coordinateTest J α ht (C.patch i).chart.val
    (D (C.patch i).chart).toData (componentTest j (C.weight i)) z).compContinuousLinearMap L) =
    C.weight i z • (ManifoldForms.pullback a (extChartAt Model (C.patch i).chart.val).symm z).compContinuousLinearMap L at he'
  have hp : (ManifoldForms.pullback a (extChartAt Model (C.patch i).chart.val).symm z).compContinuousLinearMap L = a x := by
    unfold ManifoldForms.pullback
    change ((a ((extChartAt Model (C.patch i).chart.val).symm z) : Space [⋀^Fin 2]→L[ℝ] ℝ).compContinuousLinearMap
      ((mfderiv Model Model (extChartAt Model (C.patch i).chart.val).symm z : Space →L[ℝ] Space) ∘L
        (L : Space →L[ℝ] Space))) = (a x : Space [⋀^Fin 2]→L[ℝ] ℝ)
    erw [hi]
    change a ((extChartAt Model (C.patch i).chart.val).symm z) = a x
    erw [show (extChartAt Model (C.patch i).chart.val).symm z = x from
      (extChartAt Model (C.patch i).chart.val).left_inv hxs]
  rw [hp,C.weight_chart i hxs] at he'
  refine Eq.trans ?_ he'
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change chartLift (C.patch i).chart.val
    (coordinateTest J α ht (C.patch i).chart.val (D (C.patch i).chart).toData
      (componentTest j (C.weight i))) x = _
  rw [chartLift,ite_eq_left hxs]
end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
