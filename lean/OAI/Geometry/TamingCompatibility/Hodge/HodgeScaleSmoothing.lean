import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGraphSmoothing

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def hodgeScaleInput (r : ℝ) (hr : 0 < r) : L2 A J α hs ht true →L[ℝ] hodgeEnergy A J α hs ht :=
  let a := (r^2)⁻¹
  let b := 1-a
  let U₁ := hodgeWeakSolution A J α hs ht r hr
  let U₂ := U₁.comp (hodgeResolvent A J α hs ht r)
  let U₃ := hodgeRegularizedGraph A J α hs ht r hr
  a • (a • U₁+b • U₂)+b • (a • U₂+b • U₃)

lemma hodgeScaleInput_spec (r : ℝ) (hr : 0 < r) (f : L2 A J α hs ht true) :
    (hodgeGraphResolvent A J α hs ht 1 zero_lt_one ^ 2) (hodgeScaleInput A J α hs ht r hr f) =
      hodgeRegularizedGraph A J α hs ht r hr f := by
  let a := (r^2)⁻¹
  let b := 1-a
  let u₁ := hodgeWeakSolution A J α hs ht r hr f
  let u₂ := hodgeWeakSolution A J α hs ht r hr (hodgeResolvent A J α hs ht r f)
  let u₃ := hodgeRegularizedGraph A J α hs ht r hr f
  have hi₁ : hodgeInclusion A J α hs ht u₁ = hodgeResolvent A J α hs ht r f := by
    rw [hodgeResolvent_eq A J α hs ht r hr]; rfl
  have hi₂ : hodgeInclusion A J α hs ht u₂ =
      hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r f) := by
    exact congrArg (fun L => L (hodgeResolvent A J α hs ht r f))
      (hodgeResolvent_eq A J α hs ht r hr).symm
  have hu₂ : hodgeGraphResolvent A J α hs ht r hr u₁ = u₂ := by
    change hodgeWeakSolution A J α hs ht r hr (hodgeInclusion A J α hs ht u₁) = _
    rw [hi₁]
  have hu₃ : hodgeGraphResolvent A J α hs ht r hr u₂ = u₃ := by
    change hodgeWeakSolution A J α hs ht r hr (hodgeInclusion A J α hs ht u₂) = _
    rw [hi₂]; rfl
  have he₁ := hodgeGraphResolvent_scale_transfer A J α hs ht r hr u₁
  have he₂ := hodgeGraphResolvent_scale_transfer A J α hs ht r hr u₂
  rw [hu₂] at he₁
  rw [hu₃] at he₂
  change hodgeGraphResolvent A J α hs ht 1 zero_lt_one
    (hodgeGraphResolvent A J α hs ht 1 zero_lt_one (a • (a • u₁+b • u₂)+b • (a • u₂+b • u₃))) = u₃
  rw [map_add,map_smul,map_smul,he₁,he₂,he₂]

lemma hodgeScaleInput_bound (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (f : L2 A J α hs ht true) :
    ‖hodgeScaleInput A J α hs ht r hr f‖ ≤ 8*(r⁻¹)^5*‖f‖ := by
  let a := (r^2)⁻¹
  let b := 1-a
  let u₁ := hodgeWeakSolution A J α hs ht r hr f
  let u₂ := hodgeWeakSolution A J α hs ht r hr (hodgeResolvent A J α hs ht r f)
  let u₃ := hodgeRegularizedGraph A J α hs ht r hr f
  let K := 2*r⁻¹*‖f‖
  have ha : 0 ≤ a := inv_nonneg.mpr (sq_nonneg _)
  have ha1 : 1 ≤ a := by
    apply (one_le_inv₀ (sq_pos_of_pos hr)).mpr
    have : r*r ≤ 1*1 := mul_le_mul hr1 hr1 hr.le zero_le_one
    simpa only [pow_two,one_mul] using this
  have hb : |b| ≤ a := by rw [abs_of_nonpos (by dsimp [b]; linarith)]; dsimp [b]; linarith
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hr.le)) (norm_nonneg f)
  have hu₁ : ‖u₁‖ ≤ K := hodgeWeakSolution_graph_small_bound A J α hs ht r hr hr1 f
  have hrf := hodgeResolvent_norm_le A J α hs ht r f
  have hrrf := hodgeResolvent_norm_le A J α hs ht r (hodgeResolvent A J α hs ht r f)
  have hu₂ : ‖u₂‖ ≤ K := (hodgeWeakSolution_graph_small_bound A J α hs ht r hr hr1 _).trans
    (mul_le_mul_of_nonneg_left hrf (mul_nonneg (by norm_num) (inv_nonneg.mpr hr.le)))
  have hu₃ : ‖u₃‖ ≤ K := (hodgeWeakSolution_graph_small_bound A J α hs ht r hr hr1 _).trans
    (mul_le_mul_of_nonneg_left (hrrf.trans hrf) (mul_nonneg (by norm_num) (inv_nonneg.mpr hr.le)))
  have hbound (u v : hodgeEnergy A J α hs ht) (hu : ‖u‖ ≤ K) (hv : ‖v‖ ≤ K) :
      ‖a • u+b • v‖ ≤ 2*a*K := by
    calc
      _ ≤ ‖a • u‖+‖b • v‖ := norm_add_le _ _
      _ = a*‖u‖+|b| *‖v‖ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg ha]
      _ ≤ a*K+a*K := add_le_add (mul_le_mul_of_nonneg_left hu ha)
        (mul_le_mul hb hv (norm_nonneg _) ha)
      _ = _ := by ring
  change ‖a • (a • u₁+b • u₂)+b • (a • u₂+b • u₃)‖ ≤ _
  calc
    _ ≤ ‖a • (a • u₁+b • u₂)‖+‖b • (a • u₂+b • u₃)‖ := norm_add_le _ _
    _ = a*‖a • u₁+b • u₂‖+|b| *‖a • u₂+b • u₃‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg ha]
    _ ≤ a*(2*a*K)+a*(2*a*K) := add_le_add (mul_le_mul_of_nonneg_left (hbound _ _ hu₁ hu₂) ha)
      (mul_le_mul hb (hbound _ _ hu₂ hu₃) (norm_nonneg _) ha)
    _ = 8*(r⁻¹)^5*‖f‖ := by dsimp [K,a]; rw [inv_pow]; ring
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
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma hodgeRegularization_uniform_local_H5 (p : A.centers) (q : Space)
    (hq : q ∈ (D p).domain) (hwq : coordinateWeight A p q ≠ 0) :
    ∃ τ : 𝓢(Space,ℝ), ∃ χ : 𝓢(Space,ℂ), ∃ U : Set Space,
      IsOpen U ∧ q ∈ U ∧ U ⊆ (D p).domain ∧
      (∀ z ∈ U, τ z * coordinateWeight A p z = 1) ∧
      (∀ z ∈ U, χ z = 1) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
        ∃ L : L2 A J α hs ht true →L[ℝ] H Space (C 6) 5,
          (∀ f, toDistribution Space (C 6) 5 (L f) =
            smulLeftCLM (C 6) χ (hodgeRawDistribution A J α hs ht D hD p τ
              (hodgeRegularizedGraph A J α hs ht r hr f))) ∧
          ∀ f, ‖L f‖ ≤ B*(r⁻¹)^5*‖f‖ := by
  obtain ⟨τ,χ,U,hU,hqU,hUD,hτ,hχ,L,hL⟩ := exists_hodgeGraphResolvent_lift A J α hs ht D hD p q hq hwq
  refine ⟨τ,χ,U,hU,hqU,hUD,hτ,hχ,8*‖L‖,by positivity,fun r hr hr1 => ?_⟩
  refine ⟨L.comp (hodgeScaleInput A J α hs ht r hr),?_,?_⟩
  · intro f
    rw [ContinuousLinearMap.comp_apply,hL,hodgeScaleInput_spec]
  · intro f
    calc
      _ ≤ ‖L‖*‖hodgeScaleInput A J α hs ht r hr f‖ := L.le_opNorm _
      _ ≤ ‖L‖*(8*(r⁻¹)^5*‖f‖) := mul_le_mul_of_nonneg_left
        (hodgeScaleInput_bound A J α hs ht r hr hr1 f) (norm_nonneg L)
      _ = _ := by ring
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart
open MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

include hD in
lemma hodgeInclusion_factor : hodgeInclusion A J α hs ht =
    chartToMetric A J α hs ht ∘L h1ToL2 A 2 ∘L hodgeEnergyToH1 A J α hs ht := by
  apply DFunLike.coe_injective
  apply (hodgeSmooth_dense A J α hs ht).equalizer
    (hodgeInclusion A J α hs ht).continuous
    (chartToMetric A J α hs ht ∘L h1ToL2 A 2 ∘L hodgeEnergyToH1 A J α hs ht).continuous
  funext a
  change smoothL2 A J α hs ht true a =
    chartToMetric A J α hs ht (h1ToL2 A 2 (hodgeEnergyToH1 A J α hs ht (hodgeSmooth A J α hs ht a)))
  rw [hodgeEnergyToH1_smooth A J α hs ht D hD]
  exact (chartToMetric_smooth A J α hs ht (fun p => (D p).toData) hD a).symm

include hD in

theorem hodgeInclusion_compact : IsCompactOperator (hodgeInclusion A J α hs ht) := by
  rw [hodgeInclusion_factor A J α hs ht D hD]
  exact ((h1ToL2_compact A 2).comp_clm (hodgeEnergyToH1 A J α hs ht)).clm_comp
    (chartToMetric A J α hs ht)

include hD in
lemma hodgeEnergyToH1_injective : Function.Injective (hodgeEnergyToH1 A J α hs ht) := by
  intro u v h
  apply hodgeInclusion_injective A J α hs ht
  rw [hodgeInclusion_factor A J α hs ht D hD]
  change chartToMetric A J α hs ht (h1ToL2 A 2 (hodgeEnergyToH1 A J α hs ht u)) =
    chartToMetric A J α hs ht (h1ToL2 A 2 (hodgeEnergyToH1 A J α hs ht v))
  rw [h]
include hD in

lemma hodgeResolvent_compact (r : ℝ) (hr : 0 < r) :
    IsCompactOperator (hodgeResolvent A J α hs ht r) := by
  rw [hodgeResolvent_eq A J α hs ht r hr]
  exact (hodgeInclusion_compact A J α hs ht D hD).comp_clm
    (hodgeWeakSolution A J α hs ht r hr)

include hD in
lemma hodgeRegularization_compact (r : ℝ) (hr : 0 < r) :
    IsCompactOperator (hodgeRegularization A J α hs ht r) := by
  change IsCompactOperator ((hodgeResolvent A J α hs ht r).comp
    ((hodgeResolvent A J α hs ht r).comp (hodgeResolvent A J α hs ht r)))
  exact (hodgeResolvent_compact A J α hs ht D hD r hr).comp_clm _
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
