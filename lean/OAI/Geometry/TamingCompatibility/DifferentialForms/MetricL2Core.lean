import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.PairingSmooth

namespace OAI


noncomputable section
namespace TamingCompatibility.MetricForms
open MetricModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
lemma pairing_zero_left (g : Metric E) {k : ℕ} (a : Form E k) : pairing g 0 a = 0 := by
  change FormMetric.pairing (MetricHodge.formEquiv g k 0) (MetricHodge.formEquiv g k a) = 0
  rw [map_zero]
  simp [FormMetric.pairing]
lemma pairing_add_left' (g : Metric E) {k : ℕ} (a b c : Form E k) :
    pairing g (a+b) c = pairing g a c + pairing g b c := by
  change FormMetric.pairing (MetricHodge.formEquiv g k (a+b)) (MetricHodge.formEquiv g k c) = _
  rw [map_add]
  simp only [FormMetric.pairing,map_add,inner_add_left]
  rfl
end TamingCompatibility.MetricForms

namespace TamingCompatibility.GeometricHilbert
open MeasureTheory ManifoldForms ManifoldHodge ManifoldVolume ManifoldLocalization GeometricAdjoint
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def l2Pairing {k : ℕ} (a b : smoothForms X k) : ℝ :=
  ∫ x, pairing J α ht a.val b.val x ∂geometricVolume A J α

omit [CompactSpace X] [BorelSpace X] in
lemma l2_nonneg {k : ℕ} (a : smoothForms X k) : 0 ≤ l2Pairing A J α ht a a :=
  integral_nonneg (fun x => MetricForms.pairing_self_nonneg (pointMetric J α ht x) (a.val x))

omit [CompactSpace X] [BorelSpace X] in
lemma l2_symm {k : ℕ} (a b : smoothForms X k) :
    l2Pairing A J α ht a b = l2Pairing A J α ht b a := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => MetricForms.pairing_symm _ _ _)

@[instance_reducible] def l2Core (k : ℕ)
    (hcont : ∀ a b : smoothForms X k, Continuous (pairing J α ht a.val b.val)) :
    InnerProductSpace.Core ℝ (smoothForms X k) := by
  let := geometricVolume_finite A J α hs ht
  let := geometricVolume_openPos A J α hs ht
  have hint (a b : smoothForms X k) : Integrable (pairing J α ht a.val b.val)
      (geometricVolume A J α) :=
    (hcont a b).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine {
    inner := l2Pairing A J α ht
    conj_inner_symm := ?_
    re_inner_nonneg := fun a => l2_nonneg A J α ht a
    add_left := ?_
    smul_left := ?_
    definite := ?_ }
  · intro a b
    exact l2_symm A J α ht b a
  · intro a b c
    change (∫ x, pairing J α ht (a.val+b.val) c.val x ∂geometricVolume A J α) = _
    have he : pairing J α ht (a.val+b.val) c.val =
        pairing J α ht a.val c.val + pairing J α ht b.val c.val := by
      funext x
      exact MetricForms.pairing_add_left' _ _ _ _
    rw [he]
    exact integral_add (hint a c) (hint b c)
  · intro a b r
    change (∫ x, pairing J α ht (r • a.val) b.val x ∂geometricVolume A J α) =
      r * l2Pairing A J α ht a b
    have he : pairing J α ht (r • a.val) b.val =
        fun x => r * pairing J α ht a.val b.val x := by
      funext x
      exact MetricForms.pairing_smul_left _ _ _ _
    rw [he,integral_const_mul]
    rfl
  · intro a haz
    apply Subtype.ext
    funext x
    apply (MetricForms.pairing_self_eq_zero (pointMetric J α ht x) (a.val x)).mp
    have he : pairing J α ht a.val a.val = 0 :=
      Measure.eq_of_ae_eq ((integral_eq_zero_iff_of_nonneg
        (fun y => MetricForms.pairing_self_nonneg (pointMetric J α ht y) (a.val y))
        (hint a a)).mp haz) (hcont a a) continuous_zero
    exact congrFun he x

@[instance_reducible] def oneCore : InnerProductSpace.Core ℝ (smoothForms X 1) :=
  l2Core A J α hs ht 1 (fun a b =>
    (pairing_one_smooth J α hs ht a.property b.property).continuous)
@[instance_reducible] def twoCore : InnerProductSpace.Core ℝ (smoothForms X 2) :=
  l2Core A J α hs ht 2 (fun a b =>
    (pairing_two_smooth J α hs ht a.property b.property).continuous)

end TamingCompatibility.GeometricHilbert

end

end OAI
