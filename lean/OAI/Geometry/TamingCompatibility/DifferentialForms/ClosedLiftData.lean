import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.SmoothUnitEvaluation
import OAI.Geometry.TamingCompatibility.DifferentialForms.SmoothGeometricInverse

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart GeometricAdjoint Set
open scoped Manifold ContDiff RealInnerProductSpace SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def closedLiftOfInverse
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht) :
    antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2 :=
  let B₁ : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2 := (d.comp (antiDelta A J α hs ht)).comp Gs
  let B₂ : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2 := (antiPre A J α hs ht).subtype.comp H
  B₁ + B₂

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma closedLiftOfInverse_apply
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (f : antiPre A J α hs ht) :
    (closedLiftOfInverse A J α hs ht H Gs f).val =
      (fun a b : TwoForm X => a+b) (exteriorDerivative (codifferential J α ht (Gs f).val.val)) (H f).val.val := rfl

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma closedLiftOfInverse_closed
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (hH : ∀ f, IsClosed (H f).val.val) (f : antiPre A J α hs ht) :
    IsClosed (closedLiftOfInverse A J α hs ht H Gs f).val := by
  rw [closedLiftOfInverse_apply]
  exact IsClosed.add ((codifferential_smooth J α hs ht (Gs f).val.property).closed_exteriorDerivative)
    (hH f) (Smooth.exteriorDerivative (codifferential_smooth J α hs ht (Gs f).val.property))
    (H f).val.property

omit [T2Space X] in
lemma closedLiftOfInverse_rightInverse
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (hweak : ∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
      weakDelta A J α hs ht v⟫ =
      ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫)
    (f : antiPre A J α hs ht) :
    antiInvariantPart J (closedLiftOfInverse A J α hs ht H Gs f).val = f.val.val := by
  rw [closedLiftOfInverse_apply,antiInvariantPart_add,(H f).property]
  change (fun a b : TwoForm X => a+b) (rdd J α ht (Gs f).val.val) (H f).val.val = _
  rw [strong_weak_equation A J α hs ht (Gs f) (f-H f) (hweak f)]
  exact congrArg (fun a : antiPre A J α hs ht => a.val.val) (sub_add_cancel f (H f))

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in

lemma closedLiftOfInverse_complexLine
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (f : antiPre A J α hs ht) (x : X) (v : TangentSpace Model x) :
    eval (closedLiftOfInverse A J α hs ht H Gs f).val x v (J.endomorphism x v) =
      eval (exteriorDerivative (codifferential J α ht (Gs f).val.val)) x v (J.endomorphism x v) := by
  rw [closedLiftOfInverse_apply]
  change eval (exteriorDerivative (codifferential J α ht (Gs f).val.val)) x v (J.endomorphism x v) +
    eval (H f).val.val x v (J.endomorphism x v) = _
  rw [← (H f).property,eval_antiInvariantPart_complexLine,add_zero]

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma closedLiftOfInverse_pullback_sub
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (f : antiPre A J α hs ht) (p : X) (z : Space) :
    ManifoldForms.pullback (closedLiftOfInverse A J α hs ht H Gs f).val (extChartAt Model p).symm z -
      ManifoldForms.pullback (k := 2) (H f).val.val (extChartAt Model p).symm z =
      ManifoldForms.pullback (exteriorDerivative (codifferential J α ht (Gs f).val.val))
        (extChartAt Model p).symm z := by
  rw [closedLiftOfInverse_apply,ManifoldForms.pullback_add]
  exact add_sub_cancel_right _ _
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.LocalMatrixOperator
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open EuclideanEnergy AntiInvariantFrame
open scoped ContDiff RealInnerProductSpace

def frameRecover (g : Metric V) (b : Fin 4 → V) : V →L[ℝ] MetricForms.Form V 1 :=
  ∑ i, (EuclideanSpace.proj i).smulRight (ofSubsingletonLIE (0 : Fin 1) (g.bilinear (b i)))

lemma frameVector_injective (g : Metric V) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) :
    Function.Injective (frameVector b) := by
  apply (frameVector b).ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro a ha
  change frameVector b a = 0 at ha
  apply (pairing_self_eq_zero g a).mp
  rw [← frameVector_pairing g b hb a a,ha,inner_zero_left]

lemma frameVector_recover (g : Metric V) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) (u : V) :
    frameVector b (frameRecover g b u) = u := by
  ext j
  simp only [frameVector_apply,frameRecover,_root_.sum_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousAlternatingMap.sum_apply,ContinuousAlternatingMap.smul_apply,smul_eq_mul]
  change (∑ i : Fin 4, u i * g.bilinear (b i) (b j)) = u j
  simp [hb]

lemma frameRecover_vector (g : Metric V) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) (a : MetricForms.Form V 1) :
    frameRecover g b (frameVector b a) = a := by
  apply frameVector_injective g b hb
  exact frameVector_recover g b hb _

lemma frameRecover_smooth {U : Set V} (g : V → Metric V) (b : Fin 4 → V → V)
    (hg : ContDiffOn ℝ ∞ (fun z => (g z).bilinear) U)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U) :
    ContDiffOn ℝ ∞ (fun z => frameRecover (g z) (fun i => b i z)) U := by
  unfold frameRecover
  apply ContDiffOn.sum
  intro i _
  exact contDiffOn_const.smulRight
    ((ofSubsingletonLIE (0 : Fin 1) : (V →L[ℝ] ℝ) ≃ₗᵢ[ℝ] MetricForms.Form V 1).contDiff.comp_contDiffOn
      (hg.clm_apply (hb i)))

end TamingCompatibility.LocalMatrixOperator

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : Data J α ht p)

def deltaA (i : Fin 4) (z : Space) : EuclideanEnergy.Pair →L[ℝ] MetricForms.Form Space 1 :=
  -(frameRecover (coordinateMetric J α ht p z) (fun j => D.frame j z)).comp (normalA J α ht p D i z)

def deltaB (z : Space) : EuclideanEnergy.Pair →L[ℝ] MetricForms.Form Space 1 :=
  -(frameRecover (coordinateMetric J α ht p z) (fun j => D.frame j z)).comp (normalB J α ht p D z)

include hs in
lemma deltaA_smooth (i : Fin 4) : ContDiffOn ℝ ∞ (deltaA J α ht p D i) D.domain := by
  exact ((frameRecover_smooth (coordinateMetric J α ht p) D.frame
    ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset) D.frame_smooth).clm_comp
    (normalA_smooth J α ht p D i)).neg

include hs in
lemma deltaB_smooth : ContDiffOn ℝ ∞ (deltaB J α ht p D) D.domain := by
  exact ((frameRecover_smooth (coordinateMetric J α ht p) D.frame
    ((coordinateMetric_smooth J α hs ht p).mono D.domain_subset) D.frame_smooth).clm_comp
    (normalB_smooth J α hs ht p D)).neg

include hs in
lemma delta_coefficient_expansion {a : TwoForm X} (ha : IsSmooth a)
    (hanti : antiInvariantPart J a = a) {z : Space} (hz : z ∈ D.domain) :
    ManifoldForms.pullback (codifferential J α ht a) (extChartAt Model p).symm z =
      (∑ i, deltaA J α ht p D i z
        (fderiv ℝ (rawPair J α ht p D a) z (EuclideanEnergy.e i))) +
          deltaB J α ht p D z (rawPair J α ht p D a z) := by
  have he := congrArg (frameRecover (coordinateMetric J α ht p z) (fun j => D.frame j z))
    (normal_delta J α hs ht p D ha hanti hz)
  rw [frameRecover_vector _ _ (D.frame_gram z hz)] at he
  rw [he]
  simp only [map_neg,map_add,map_sum,deltaA,deltaB,neg_apply,
    ContinuousLinearMap.comp_apply,Finset.sum_neg_distrib,neg_add_rev,add_comm]

end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
