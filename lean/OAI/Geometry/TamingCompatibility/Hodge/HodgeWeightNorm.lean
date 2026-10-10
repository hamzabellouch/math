import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeUniformCommutator

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

namespace LocalWeight
variable (p : A.centers) (U : Set Space) (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
  (η : X → ℝ) (hη : ContMDiff Model 𝓘(ℝ,ℝ) ∞ η)
  (hηU : tsupport η ⊆ (extChartAt Model p.val).source ∩ (extChartAt Model p.val) ⁻¹' U)

def coordinateFunction : Space → ℝ :=
  (extChartAt Model p.val).target.indicator (fun z => η ((extChartAt Model p.val).symm z))

def coordinateSupport : Set Space := (extChartAt Model p.val) '' tsupport η

include hηU in
omit [MeasurableSpace X] [BorelSpace X] in
lemma coordinateSupport_compact : IsCompact (coordinateSupport A p η) := by
  apply (isClosed_tsupport η).isCompact.image_of_continuousOn
  exact (continuousOn_extChartAt p.val).mono (fun _ hx => (hηU hx).1)

include hηU in
omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma coordinateSupport_subset : coordinateSupport A p η ⊆ U := by
  rintro z ⟨x,hx,rfl⟩
  exact (hηU hx).2

include hηU in
omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma coordinateSupport_target : coordinateSupport A p η ⊆ (extChartAt Model p.val).target := by
  rintro z ⟨x,hx,rfl⟩
  exact (extChartAt Model p.val).map_source (hηU hx).1

include hη hηU in
omit [MeasurableSpace X] [BorelSpace X] in
lemma coordinateFunction_smooth_compact :
    ContDiff ℝ ∞ (coordinateFunction A p η) ∧ HasCompactSupport (coordinateFunction A p η) := by
  apply smooth_indicator_of_compact (isOpen_extChartAt_target p.val)
    (coordinateSupport_compact A p U η hηU) (coordinateSupport_target A p U η hηU)
  · exact (hη.comp_contMDiffOn (contMDiffOn_extChartAt_symm p.val)).contDiffOn
  · intro z hz hn
    apply image_eq_zero_of_notMem_tsupport
    intro hh
    exact hn ⟨_,hh,(extChartAt Model p.val).right_inv hz⟩

include hηU in
omit [MeasurableSpace X] [BorelSpace X] in
lemma coordinateFunction_support : tsupport (coordinateFunction A p η) ⊆ U := by
  apply (closure_minimal ?_ (coordinateSupport_compact A p U η hηU).isClosed).trans
    (coordinateSupport_subset A p U η hηU)
  intro z hz
  by_cases ht : z ∈ (extChartAt Model p.val).target
  · refine ⟨(extChartAt Model p.val).symm z,?_,(extChartAt Model p.val).right_inv ht⟩
    apply subset_closure
    simpa only [Function.mem_support,coordinateFunction,indicator_of_mem ht] using hz
  · exact False.elim (hz (indicator_of_notMem ht _))

include hs hUD in
omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma density_sqrt_smooth : ContDiffOn ℝ ∞ (fun z => Real.sqrt (chartDensity J α p.val z)) U :=
  ((chartDensity_smooth J α hs ht p.val).mono (hUD.trans (D p).domain_subset)).sqrt
    (fun _z hz => ne_of_gt (chartDensity_pos J α ht p.val ((D p).domain_subset (hUD hz))))

def halfDensity : 𝓢(Space,ℝ) :=
  SchwartzCutoff.schwartz hU (density_sqrt_smooth A J α hs ht D p U hUD)
    (coordinateFunction_smooth_compact A p U η hη hηU).1
    (coordinateFunction_smooth_compact A p U η hη hηU).2
    (coordinateFunction_support A p U η hηU)

omit [MeasurableSpace X] [BorelSpace X] in
lemma halfDensity_apply (z : Space) : halfDensity A J α hs ht D p U hU hUD η hη hηU z =
    coordinateFunction A p η z * Real.sqrt (chartDensity J α p.val z) := rfl

omit [MeasurableSpace X] [BorelSpace X] in
lemma halfDensity_support : tsupport (halfDensity A J α hs ht D p U hU hUD η hη hηU) ⊆ U :=
  (tsupport_smul_subset_left _ _).trans (coordinateFunction_support A p U η hηU)

omit [MeasurableSpace X] [BorelSpace X] in
lemma halfDensity_compact : HasCompactSupport (halfDensity A J α hs ht D p U hU hUD η hη hηU : Space → ℝ) :=
  SchwartzCutoff.compact (coordinateFunction_smooth_compact A p U η hη hηU).2

lemma integral_weight_norm (f : PreL2 A J α hs ht true) :
    (∫ x, (η x)^2 * GeometricAdjoint.pairing J α ht f.val f.val x ∂geometricVolume A J α) =
      ∫ z, (halfDensity A J α hs ht D p U hU hUD η hη hηU z)^2 *
        ‖rawVector J α ht p.val (D p).toData f.val z‖^2 := by
  have hc : Continuous (fun x => (η x)^2 * GeometricAdjoint.pairing J α ht f.val f.val x) :=
    (hη.continuous.pow 2).mul (GeometricAdjoint.pairing_two_smooth J α hs ht f.property f.property).continuous
  have hsq : tsupport (fun x => (η x)^2) ⊆ tsupport η := by
    simpa only [pow_two] using (tsupport_mul_subset_left (f := η) (g := η))
  have hsource : tsupport (fun x => (η x)^2 * GeometricAdjoint.pairing J α ht f.val f.val x) ⊆
      (extChartAt Model p.val).source := (tsupport_mul_subset_left.trans hsq).trans (fun _ hx => (hηU hx).1)
  rw [integral_geometricVolume_coordinate A J α hs ht p.val _ hc hsource,
    ← integral_indicator (isOpen_extChartAt_target p.val).measurableSet]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [halfDensity_apply]
  by_cases hz : z ∈ (extChartAt Model p.val).target
  · rw [indicator_of_mem hz]
    by_cases he : coordinateFunction A p η z = 0
    · have he' : η ((extChartAt Model p.val).symm z) = 0 := by
        simpa only [coordinateFunction,indicator_of_mem hz] using he
      simp only [he,he',zero_mul,zero_pow (by decide : 2 ≠ 0),mul_zero]
    · have hzU := coordinateFunction_support A p U η hηU (subset_closure he)
      rw [rawVector_norm_sq J α ht p.val (D p).toData f.val (hUD hzU),mul_pow,
        Real.sq_sqrt (show 0 ≤ chartDensity J α p.val z from Real.sqrt_nonneg _)]
      simp only [coordinateFunction,indicator_of_mem hz]
      ring
  · rw [indicator_of_notMem hz]
    simp only [coordinateFunction,indicator_of_notMem hz,zero_mul,zero_pow (by decide : 2 ≠ 0)]

lemma integral_weight_H0_norm (τ : 𝓢(Space,ℝ))
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (f : PreL2 A J α hs ht true) (u : H Space (C 6) 0)
    (hu : toDistribution Space (C 6) 0 u =
      smulLeftCLM (C 6) (SchwartzMap.postcompCLM Complex.ofRealCLM
        (halfDensity A J α hs ht D p U hU hUD η hη hηU))
        (hodgeRawDistribution A J α hs ht D hD p τ (hodgeSmooth A J α hs ht f))) :
    (∫ x, (η x)^2 * GeometricAdjoint.pairing J α ht f.val f.val x ∂geometricVolume A J α) = ‖u‖^2 := by
  rw [integral_weight_norm A J α hs ht D p U hU hUD η hη hηU f]
  let χ := SchwartzMap.postcompCLM Complex.ofRealCLM (halfDensity A J α hs ht D p U hU hUD η hη hηU)
  have hχ : tsupport χ ⊆ U :=
    (tsupport_comp_subset (g := Complex.ofRealCLM) (map_zero _) _).trans
      (halfDensity_support A J α hs ht D p U hU hUD η hη hηU)
  rw [hodgeRawSchwartz_H0_norm_sq A J α hs ht D hD p τ χ hUD hχ hτ f u hu]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [χ,SchwartzMap.postcompCLM_apply,Complex.ofRealCLM_apply,Complex.norm_real,Real.norm_eq_abs,sq_abs]
end LocalWeight
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
