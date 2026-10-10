import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.ChartScalarBound
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGeometricCoefficients

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldLocalization ManifoldHodge
open Set MetricForms AntiInvariantFrame GeometricChart
open FormMetric (pairLeft pairRight)
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def scalar (p : A.centers) (a : TwoForm X) (j : Fin 6) : Space → ℝ :=
  (D p).domain.indicator (fun x => localizedFunction A p a x ![(D p).frame (pairLeft j) x,(D p).frame (pairRight j) x])

omit [T2Space X] [CompactSpace X] in
lemma scalar_zero_off (p : A.centers) (a : TwoForm X) (j : Fin 6)
    {x : Space} (hx : x ∉ coordinateSupport A p) : scalar A J α ht D p a j x = 0 := by
  unfold scalar
  by_cases he : x ∈ (D p).domain
  · rw [indicator_of_mem he,localizedFunction_zero_off A p a hx]
    rfl
  · exact indicator_of_notMem he _

omit [T2Space X] in
lemma scalar_tsupport_subset (p : A.centers) (a : TwoForm X) (j : Fin 6) :
    tsupport (scalar A J α ht D p a j) ⊆ coordinateSupport A p := by
  apply closure_minimal _ (coordinateSupport_compact A p).isClosed
  intro x hx
  by_contra hn
  exact hx (scalar_zero_off A J α ht D p a j hn)

include hD in
omit [T2Space X] in
lemma scalar_smooth_compact (p : A.centers) (a : TwoForm X) (ha : IsSmooth a) (j : Fin 6) :
    ContDiff ℝ ∞ (scalar A J α ht D p a j) ∧ HasCompactSupport (scalar A J α ht D p a j) := by
  apply smooth_indicator_of_compact (D p).domain_open (coordinateSupport_compact A p)
    (coordinateSupport_domain A J α ht D hD p)
  · exact FormSmooth.contDiffOn_apply_two
      (localizedFunction_smooth_compact A p a ha).1.contDiffOn
      ((D p).frame_smooth (pairLeft j)) ((D p).frame_smooth (pairRight j))
  · intro x _ hx
    rw [localizedFunction_zero_off A p a hx]
    rfl

def scalarSchwartz (p : A.centers) (a : TwoForm X) (ha : IsSmooth a) (j : Fin 6) :
    𝓢(Space,ℝ) :=
  (scalar_smooth_compact A J α ht D hD p a ha j).2.toSchwartzMap
    (scalar_smooth_compact A J α ht D hD p a ha j).1

omit [T2Space X] in
lemma scalarSchwartz_support (p : A.centers) (a : TwoForm X) (ha : IsSmooth a) (j : Fin 6) :
    tsupport (scalarSchwartz A J α ht D hD p a ha j) ⊆
      Metric.closedBall (extChartAt Model p.val p.val) (D p).radius :=
  (scalar_tsupport_subset A J α ht D p a j).trans (coordinateSupport_small A J α ht D hD p)

include hD in
omit [T2Space X] [CompactSpace X] in
lemma scalar_expansion (p : A.centers) (a : TwoForm X) (x : Space) :
    localizedFunction A p a x = ∑ j : Fin 6, scalar A J α ht D p a j x •
      HodgeFrame.basisForm (coordinateMetric J α ht p.val x) (fun i => (D p).frame i x) j := by
  by_cases hx : x ∈ coordinateSupport A p
  · have hxU := coordinateSupport_domain A J α ht D hD p hx
    have he (j : Fin 6) : scalar A J α ht D p a j x =
        HodgeFrame.coordinates (fun i => (D p).frame i x) (localizedFunction A p a x) j := by
      simp only [scalar, indicator_of_mem hxU, HodgeFrame.coordinates_apply]
    simp only [he, ← HodgeFrame.reconstruct_apply]
    exact (HodgeFrame.reconstruct_coordinates (coordinateMetric J α ht p.val x)
      (by simp [Space]) (fun i => (D p).frame i x) ((D p).frame_gram x hxU) _).symm
  · simp only [localizedFunction_zero_off A p a hx, scalar_zero_off A J α ht D p a _ hx,
      zero_smul, Finset.sum_const_zero]
end TamingCompatibility.HodgeChart

end
end

section
noncomputable section
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldLocalization ManifoldHodge ManifoldVolume GeometricChart
open Set MeasureTheory
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in
omit [CompactSpace X] in
lemma localizedPairing_scalars (p : A.centers) (a : TwoForm X) (z : Space) :
    MetricForms.pairing (coordinateMetric J α ht p.val z)
      (localizedFunction A p a z) (localizedFunction A p a z) =
      ‖WithLp.toLp 2 (fun j : Fin 6 => scalar A J α ht D p a j z)‖^2 := by
  by_cases hz : z ∈ coordinateSupport A p
  · have hzU := coordinateSupport_domain A J α ht D hD p hz
    have he : WithLp.toLp 2 (fun j : Fin 6 => scalar A J α ht D p a j z) =
        HodgeFrame.coordinates (fun i => (D p).frame i z) (localizedFunction A p a z) := by
      ext j
      simp only [scalar,indicator_of_mem hzU,HodgeFrame.coordinates_apply]
    rw [he,← real_inner_self_eq_norm_sq]
    exact (HodgeFrame.coordinates_pairing (coordinateMetric J α ht p.val z)
      (by simp [Space]) (fun i => (D p).frame i z) ((D p).frame_gram z hzU) _ _).symm
  · rw [localizedFunction_zero_off A p a hz]
    simp only [scalar_zero_off A J α ht D p a _ hz]
    change MetricForms.pairing _ 0 0 = ‖(0 : EuclideanSpace ℝ (Fin 6))‖^2
    simp only [MetricForms.pairing_self_eq_zero _ _ |>.mpr rfl,norm_zero,ne_eq,
      OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow]

include hs hD in
lemma scalar_norm_bound (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : TwoForm X, ∀ z,
      ‖WithLp.toLp 2 (fun j : Fin 6 => scalar A J α ht D p a j z)‖^2 ≤
        C * (chartDensity J α p.val z * MetricForms.pairing (coordinateMetric J α ht p.val z)
          (localizedFunction A p a z) (localizedFunction A p a z)) := by
  obtain ⟨C,hC,hbound⟩ := density_lower_on_support A J α hs ht D hD p
  refine ⟨C,hC,?_⟩
  intro a z
  rw [localizedPairing_scalars A J α ht D hD p a]
  by_cases hz : z ∈ coordinateSupport A p
  · have hm := mul_le_mul_of_nonneg_right (hbound z hz)
      (sq_nonneg ‖WithLp.toLp 2 (fun j : Fin 6 => scalar A J α ht D p a j z)‖)
    nlinarith
  · simp only [scalar_zero_off A J α ht D p a _ hz]
    change ‖(0 : EuclideanSpace ℝ (Fin 6))‖^2 ≤ C*(chartDensity J α p.val z*‖(0 : EuclideanSpace ℝ (Fin 6))‖^2)
    simp

variable [MeasurableSpace X] [BorelSpace X]
include hs hD in
lemma integral_scalar_bound (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : TwoForm X, Smooth a →
      (∫ z, ‖WithLp.toLp 2 (fun j : Fin 6 => scalar A J α ht D p a j z)‖^2) ≤
        C * ∫ x, GeometricAdjoint.pairing J α ht (cutoffForm A p a)
          (cutoffForm A p a) x ∂geometricVolume A J α := by
  obtain ⟨C,hC,hbound⟩ := scalar_norm_bound A J α hs ht D hD p
  refine ⟨C,hC,?_⟩
  intro a ha
  have h := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => sq_nonneg _))
    ((localizedPairing_integrable A J α ht hs p (Or.inr rfl) ha).const_mul C)
    (Filter.Eventually.of_forall (hbound a))
  rw [integral_const_mul,integral_localizedPairing A J α ht hs p (Or.inr rfl) ha] at h
  simpa only [pairing_cutoff A J α ht p a] using h
end TamingCompatibility.HodgeChart

end
end

end
end

end OAI
