import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGlobalParametrix
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGammaSplit
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGammaLocal

namespace OAI

section
noncomputable section
open MeasureTheory
variable {ι E F : Type*} [MeasurableSpace ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
namespace TamingCompatibility.KernelTransfer

def sandwich (L : E →L[ℝ] F) (R : F →L[ℝ] E) :
    (E →L[ℝ] E) →L[ℝ] (F →L[ℝ] F) :=
  (ContinuousLinearMap.compL ℝ F E F).flip R ∘L
    (ContinuousLinearMap.compL ℝ E E F L)

omit [CompleteSpace E] [CompleteSpace F] in
lemma sandwich_apply (L : E →L[ℝ] F) (R : F →L[ℝ] E) (K : E →L[ℝ] E) :
    sandwich L R K = L ∘L K ∘L R := rfl

omit [CompleteSpace E] [CompleteSpace F] in
lemma sandwich_integrable {μ : Measure ι} {K : ι → E →L[ℝ] E} (hK : Integrable K μ)
    (L : E →L[ℝ] F) (R : F →L[ℝ] E) :
    Integrable (fun s => L ∘L K s ∘L R) μ :=
  (sandwich L R).integrable_comp hK

lemma integral_sandwich {μ : Measure ι} {K : ι → E →L[ℝ] E} (hK : Integrable K μ)
    (L : E →L[ℝ] F) (R : F →L[ℝ] E) :
    (∫ s, L ∘L K s ∘L R ∂μ) = L ∘L (∫ s, K s ∂μ) ∘L R :=
  (sandwich L R).integral_comp_comm hK
end TamingCompatibility.KernelTransfer

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol NormalJets NormalMetricCalculus Set MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

lemma leadingCoordinate_gamma_integrable {r : ℝ} (hr : 0 < r) (T : ℝ)
    (ψ χ : Space → ℝ) (q z : Space) :
    IntegrableOn (fun s : ℝ => hodgeGammaWeight s •
      leadingCoordinate J α ht p D g B ψ χ (r^2*s) (q,z)) (Ioc 0 (T/r^2)) := by
  have hi := (HodgeKernelBounds.profile_integrable 3 (a := ‖z‖/r)
    (by norm_num : (0:ℝ)<1/4)).mono_set (Ioc_subset_Ioi_self : Ioc 0 (T/r^2) ⊆ Ioi 0)
  have hh : IntegrableOn (fun s : ℝ => hodgeGammaWeight s * FlatHeat.heat (r^2*s) z)
      (Ioc 0 (T/r^2)) := by
    apply (hi.const_mul ((4*Real.pi)⁻¹^2*(r⁻¹)^4)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact (HodgeKernelBounds.flat_gamma_integrand hr hs.1 z).symm
  apply ((hh.const_mul (ψ q*χ z)).smul_const (normalGauge J α ht p D g B (q,z))).congr
  filter_upwards [] with s
  simp only [leadingCoordinate,smul_smul]
  congr 1
  ring

lemma leadingPatch_gamma_integrable (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)
    {r : ℝ} (hr : 0 < r) (T : ℝ) (ψ χ : Space → ℝ) (x : Space × Space) :
    IntegrableOn (fun s : ℝ => hodgeGammaWeight s •
      leadingPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ (r^2*s) x) (Ioc 0 (T/r^2)) := by
  classical
  by_cases hx : x ∈ (geometricNormalChart g B hg hB q₀ Bq hBq).target
  · simpa only [leadingPatch,KernelExtension.push,ite_eq_left hx] using
      leadingCoordinate_gamma_integrable J α ht p D g B hr T ψ χ
        ((geometricNormalChart g B hg hB q₀ Bq hBq).symm x).1
        ((geometricNormalChart g B hg hB q₀ Bq hBq).symm x).2
  · apply (integrableOn_const (C := (0 : UnitaryFrame.W →L[ℝ] UnitaryFrame.W))
      (hs := (measure_Ioc_lt_top (μ := volume) (a := (0:ℝ)) (b := T/r^2)).ne)).congr
    filter_upwards [] with s
    apply ContinuousLinearMap.ext
    intro w
    simp [leadingPatch,KernelExtension.push,hx]

variable [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)

omit [CompactSpace X] [T2Space X] in
lemma partitionLeading_gamma_integrable {r : ℝ} (hr : 0 < r) (T : ℝ)
    (p : A.centers) (x : Space × Space) :
    IntegrableOn (fun s : ℝ => hodgeGammaWeight s •
      partitionLeading J α ht A E p (r^2*s) x) (Ioc 0 (T/r^2)) :=
  leadingPatch_gamma_integrable J α ht p.val (E p).chart (E p).metricExtension
    (E p).frameExtension (E p).metric_smooth (E p).frame_smooth (extChartAt Model p.val p.val)
    (E p).centerFrame (E p).centerFrame_eq hr T (coordinatePartition A p) (E p).normalCutoff x

omit [CompactSpace X] [T2Space X] in
lemma leadingMatrix_gamma_integrable {r : ℝ} (hr : 0 < r) (T : ℝ)
    (p : A.centers) (x : Space × Space) :
    IntegrableOn (fun s : ℝ => hodgeGammaWeight s •
      leadingMatrix J α ht A E p (r^2*s) x) (Ioc 0 (T/r^2)) := by
  have h := KernelTransfer.sandwich_integrable
    (partitionLeading_gamma_integrable J α ht A E hr T p x)
    (coordinateEncode J α ht A E p x.2) (coordinateDecode J α ht A E p x.1)
  change Integrable _ (volume.restrict (Ioc 0 (T/r^2)))
  simpa only [leadingMatrix,coordinateMatrix,ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.smul_comp] using h

omit [CompactSpace X] [T2Space X] in
lemma leadingMatrix_gamma {r : ℝ} (hr : 0 < r) (T : ℝ)
    (p : A.centers) (x : Space × Space) :
    (1/120 : ℝ) • (∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s •
      leadingMatrix J α ht A E p (r^2*s) x) =
        coordinateMatrix J α ht A E p
          (fun x => (1/120 : ℝ) • (∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s •
            partitionLeading J α ht A E p (r^2*s) x)) x := by
  have h := KernelTransfer.integral_sandwich
    (partitionLeading_gamma_integrable J α ht A E hr T p x)
    (coordinateEncode J α ht A E p x.2) (coordinateDecode J α ht A E p x.1)
  simp only [ContinuousLinearMap.comp_smul,ContinuousLinearMap.smul_comp] at h ⊢
  simp only [leadingMatrix,coordinateMatrix,ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.smul_comp,h]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
open MeasureTheory Set
open scoped Manifold
namespace TamingCompatibility.ManifoldKernelExtension
variable {E X G I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [ChartedSpace E X] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasurableSpace I]

lemma push_smul (p : X) (c : ℝ) (f : E × E → G) (x : X × X) :
    push p (fun z => c • f z) x = c • push p f x := by
  classical
  unfold push
  split_ifs <;> simp

omit [NormedSpace ℝ G] in
lemma push_integrable {μ : Measure I} (p : X) (K : I → E × E → G)
    (hK : ∀ z, Integrable (fun s => K s z) μ) (x : X × X) :
    Integrable (fun s => push p (K s) x) μ := by
  classical
  by_cases hx : x ∈ (extChartAt 𝓘(ℝ,E) p).source ×ˢ (extChartAt 𝓘(ℝ,E) p).source
  · simpa only [push,ite_eq_left hx] using hK (extChartAt 𝓘(ℝ,E) p x.1,extChartAt 𝓘(ℝ,E) p x.2)
  · simp only [push,ite_eq_right hx]
    exact integrable_zero _ _ _

lemma integral_push [CompleteSpace G] {μ : Measure I} (p : X) (K : I → E × E → G)
    (x : X × X) :
    (∫ s, push p (K s) x ∂μ) = push p (fun z => ∫ s, K s z ∂μ) x := by
  classical
  by_cases hx : x ∈ (extChartAt 𝓘(ℝ,E) p).source ×ˢ (extChartAt 𝓘(ℝ,E) p).source
  · simp only [push,ite_eq_left hx]
  · simp only [push,ite_eq_right hx,integral_zero]
end TamingCompatibility.ManifoldKernelExtension

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)

def gammaPartitionLeading (T r : ℝ) (p : A.centers) (z : Space × Space) : UnitaryFrame.W →L[ℝ] UnitaryFrame.W :=
  (1/120 : ℝ) • (∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s • partitionLeading J α ht A E p (r^2*s) z)

omit [CompactSpace X] [T2Space X] in
lemma gammaPartitionLeading_apply {r : ℝ} (hr : 0 < r) (T : ℝ)
    (p : A.centers) {z : Space × Space} (hz : z ∈ (E p).normalCompact) :
    gammaPartitionLeading J α ht A E T r p
      (z.1,normalMap (E p).metricExtension (E p).frameExtension z.1 z.2) =
      (coordinatePartition A p z.1*(E p).normalCutoff z.2*HodgeKernelBounds.leading r T ‖z.2‖) •
        normalGauge J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension z := by
  unfold gammaPartitionLeading
  have he : (fun s : ℝ => hodgeGammaWeight s • partitionLeading J α ht A E p (r^2*s)
      (z.1,normalMap (E p).metricExtension (E p).frameExtension z.1 z.2)) =
      (fun s : ℝ => hodgeGammaWeight s • leadingCoordinate J α ht p.val (E p).chart
        (E p).metricExtension (E p).frameExtension (coordinatePartition A p) (E p).normalCutoff
        (r^2*s) z) := by
    funext s
    congr 1
    exact leadingPatch_apply J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension
      (E p).metric_smooth (E p).frame_smooth (extChartAt Model p.val p.val)
      (E p).centerFrame (E p).centerFrame_eq (coordinatePartition A p) (E p).normalCutoff
      (r^2*s) ((E p).normalCompact_source hz)
  rw [he]
  exact leadingCoordinate_gamma J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension
    hr T (coordinatePartition A p) (E p).normalCutoff z.1 z.2

variable (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
include hE in
omit [T2Space X] in
lemma gammaPartitionLeading_support (T r : ℝ) (p : A.centers) :
    Function.support (gammaPartitionLeading J α ht A E T r p) ⊆ (E p).physicalCompact := by
  intro z hz
  by_contra h
  apply hz
  have he (s : ℝ) : partitionLeading J α ht A E p (r^2*s) z = 0 :=
    Function.notMem_support.mp (fun hz' => h
      (partitionLeading_tsupport J α ht A E hE p (r^2*s) (subset_tsupport _ hz')))
  have hz0 (s : ℝ) : hodgeGammaWeight s • partitionLeading J α ht A E p (r^2*s) z = 0 := by
    rw [he]
    ext w
    simp
  unfold gammaPartitionLeading
  simp only [hz0,integral_zero]
  ext w
  simp

omit [CompactSpace X] [T2Space X] in
lemma globalLeading_gamma_sum {r : ℝ} (hr : 0 < r) (T : ℝ) (x y : X) :
    HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r x y =
      ∑ p : A.centers, ManifoldKernelExtension.push p.val
        (coordinateMatrix J α ht A E p (gammaPartitionLeading J α ht A E T r p)) (y,x) := by
  classical
  have hi (p : A.centers) : IntegrableOn
      (fun s : ℝ => hodgeGammaWeight s • ManifoldKernelExtension.push p.val
        (leadingMatrix J α ht A E p (r^2*s)) (y,x)) (Ioc 0 (T/r^2)) := by
    change Integrable _ (volume.restrict (Ioc 0 (T/r^2)))
    simpa only [ManifoldKernelExtension.push_smul] using
      ManifoldKernelExtension.push_integrable p.val
        (fun s z => hodgeGammaWeight s • leadingMatrix J α ht A E p (r^2*s) z)
        (fun z => leadingMatrix_gamma_integrable J α ht A E hr T p z) (y,x)
  have he : (∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s • globalLeading J α ht A E (r^2*s) x y) =
      ∫ s : ℝ in Ioc 0 (T/r^2), ∑ p : A.centers, hodgeGammaWeight s •
        ManifoldKernelExtension.push p.val (leadingMatrix J α ht A E p (r^2*s)) (y,x) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    simp only [globalLeading,assemble,ite_eq_left (mul_pos (sq_pos_of_pos hr) hs.1),Finset.smul_sum]
  unfold HodgeKernelBounds.gammaKernel
  rw [he,integral_finsetSum _ (fun p _ => hi p),Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp_rw [← ManifoldKernelExtension.push_smul]
  rw [ManifoldKernelExtension.integral_push,← ManifoldKernelExtension.push_smul]
  apply congrArg (fun K => ManifoldKernelExtension.push p.val K (y,x))
  funext z
  exact leadingMatrix_gamma J α ht A E hr T p z

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
