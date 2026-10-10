import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.ScalarPieces
import OAI.Geometry.CAT0Fillings.Slicing.CoordinateDerivative
import OAI.Geometry.CAT0Fillings.Slicing.CoordinateIntegral
import OAI.Geometry.CAT0Fillings.Currents.Summation

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))
lemma coordinateSlice_u_eq {u : X → ℝ}
    (hu : ∀ z (hz : z ∈ C.domain), u (C.param ⟨z,hz⟩) = (Prism.split k z).1)
    (t : ℝ) (hi : Integrable (fun z => (C.multiplicity (coordinateLayer k t z):ℝ))
      (volume.restrict (C.coordinateDomain t)))
    (z : (C.coordinateSlice t hi).domain) : u ((C.coordinateSlice t hi).param z) = t := by
  have h := hu (coordinateLayer k t z) z.property
  change u ((C.coordinateSlice t hi).param z) = _ at h
  simpa only [coordinateLayer,ContinuousLinearEquiv.apply_symm_apply] using h

lemma ae_coordinateSliceTotal_weighted {u : X → ℝ}
    (hu : ∀ z (hz : z ∈ C.domain), u (C.param ⟨z,hz⟩) = (Prism.split k z).1)
    {b : X → ℝ} {π : Fin k → X → ℝ} (h : Admissible b π)
    (φ : ℝ → ℝ) (hφ : BoundedLip (φ ∘ u)) :
    ∀ᵐ t : ℝ, (C.coordinateSliceTotal t).action (fun x => φ (u x)*b x) π =
      φ t * (C.coordinateSliceTotal t).action b π := by
  filter_upwards [C.ae_coordinateSliceTotal_eq] with t ht
  obtain ⟨hi,heq⟩ := ht
  rw [heq]
  have hab : Admissible (fun x => φ (u x)*b x) π := ⟨hφ.mul h.1,h.2⟩
  rw [action,ite_eq_left hab,action,ite_eq_left h,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (C.measurableSet_coordinateDomain t)] with z hz
  rw [(C.coordinateSlice t hi).scalar_eq hz,(C.coordinateSlice t hi).scalar_eq hz,
    C.coordinateSlice_u_eq hu t hi ⟨z,hz⟩]
  ring

theorem coordinateSlice_weighted_integral {u : X → ℝ} {K : ℝ≥0} (hL : LipschitzWith K u)
    (hu : ∀ z (hz : z ∈ C.domain), u (C.param ⟨z,hz⟩) = (Prism.split k z).1)
    {b : X → ℝ} {π : Fin k → X → ℝ} (h : Admissible b π)
    (φ : ℝ → ℝ) (hφ : BoundedLip (φ ∘ u)) :
    C.action (fun x => φ (u x)*b x) (Matrix.vecCons u π) =
      ∫ t : ℝ, φ t * (C.coordinateSliceTotal t).action b π := by
  calc
    _ = ∫ t : ℝ, (C.coordinateSliceTotal t).action (fun x => φ (u x)*b x) π :=
      C.coordinateSlice_action_integral hL hu ⟨hφ.mul h.1,h.2⟩
    _ = _ := integral_congr_ae (C.ae_coordinateSliceTotal_weighted hu h φ hφ)

end CAT0Fillings.IntegerChart
namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))

lemma coordinateSliceTotal_image_subset (t : ℝ) :
    (C.coordinateSliceTotal t).image ⊆ C.image := by
  classical
  unfold coordinateSliceTotal
  split_ifs with hi
  · rintro x ⟨z,rfl⟩
    exact ⟨⟨coordinateLayer k t z,z.property⟩,rfl⟩
  · rintro x ⟨z,_⟩
    exact False.elim z.property

variable [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X]

theorem exists_scalar_coarea (hX : IsCAT0 X) {u : X → ℝ} {K : ℝ≥0}
    (hK : LipschitzWith K u) :
    ∃ (S : ℝ → Functional X k) (G : ℝ → ℝ),
      Integrable G ∧ (∀ t, 0 ≤ G t) ∧
      (∀ᵐ t : ℝ, IsMetricCurrent (S t) ∧ IntegerRectifiable (S t) ∧ mass (S t) ≤ G t) ∧
      (∫ t : ℝ, G t) ≤ K * mass C.action ∧
      (∀ b π, Admissible b π → Integrable (fun t : ℝ => S t b π) ∧
        C.action b (Matrix.vecCons u π) = ∫ t : ℝ, S t b π) ∧
      (∀ b π, Admissible b π → ∀ φ : ℝ → ℝ, BoundedLip (φ ∘ u) →
        ∀ᵐ t : ℝ, S t (fun x => φ (u x)*b x) π = φ t * S t b π) := by
  obtain ⟨D,hDd,_hDsub,hDu,hDm,hDI,hDact⟩ := C.exists_scalar_straightened_charts hK
  choose G hG hG0 hGm hGI using fun i => (D i).sharp_coordinate_coarea_majorant hX hK (hDu i)
  let Q i t := (D i).coordinateSliceTotal t
  let S : ℝ → Functional X k := fun t b π => ∑' i, (Q i t).action b π
  have hGIs : Summable (fun i => ∫ t : ℝ, G i t) := by
    simp_rw [hGI]
    exact hDm.mul_left (K:ℝ)
  have hGn : Summable (fun i => ∫ t : ℝ, ‖G i t‖) := by
    simpa only [Real.norm_of_nonneg (hG0 _ _)] using hGIs
  have hGa : ∀ᵐ t : ℝ, Summable (fun i => G i t) := by
    simpa only [Real.norm_of_nonneg (hG0 _ _)] using ae_summable_norm_of_integral hG hGn
  have hQa : ∀ᵐ t : ℝ, Summable (fun i => mass (Q i t).action) := by
    filter_upwards [hGa,ae_all_iff.mpr hGm] with t hs hm
    exact hs.of_nonneg_of_le (fun i => mass_nonneg _) hm
  have hQd (t : ℝ) : Pairwise (fun i j => Disjoint (Q i t).image (Q j t).image) := by
    intro i j hij
    exact (hDd hij).mono ((D i).coordinateSliceTotal_image_subset t)
      ((D j).coordinateSliceTotal_image_subset t)
  refine ⟨S,fun t => ∑' i, G i t,integrable_series hG hGn,
    fun t => tsum_nonneg (fun i => hG0 i t),?_,?_,?_,?_⟩
  · filter_upwards [hQa,hGa,ae_all_iff.mpr hGm] with t hqt hgt hmt
    refine ⟨isMetricCurrent_tsum (fun i => (Q i t).action_isMetricCurrent) hqt,
      ⟨fun i => Q i t,hQd t,fun i => (Q i t).action_isMetricCurrent,hqt,fun _ _ => rfl⟩,?_⟩
    exact (mass_tsum_le (fun i => (Q i t).action_isMetricCurrent) hqt).trans
      (hqt.tsum_le_tsum hmt hgt)
  · rw [←integral_tsum_of_summable_integral_norm hG hGn]
    simp_rw [hGI]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hDI K.coe_nonneg
  · intro b π hab
    have hi i : Integrable (fun t : ℝ => (Q i t).action b π) :=
      (D i).coordinateSlice_action_integrable hK (hDu i) hab
    choose L hL using hab.2
    obtain ⟨M,hM⟩ := hab.1.2
    let A : ℝ := (∏ j, (L j:ℝ)) * max M 0
    have hA : 0 ≤ A := mul_nonneg (Finset.prod_nonneg fun j _ => (L j).coe_nonneg) (le_max_right _ _)
    have hbound i : ∀ᵐ t : ℝ, ‖(Q i t).action b π‖ ≤ A * G i t := by
      filter_upwards [hGm i] with t ht
      rw [Real.norm_eq_abs]
      exact ((Q i t).action_isMetricCurrent.mass_bound_uniform hab.1 L hL
        (fun x => (hM x).trans (le_max_left _ _))).trans
          (mul_le_mul_of_nonneg_left ht hA)
    have hIs : Summable (fun i => ∫ t : ℝ, ‖(Q i t).action b π‖) := by
      apply (hGIs.mul_left A).of_nonneg_of_le (fun i => integral_nonneg (fun _ => norm_nonneg _))
      intro i
      rw [←integral_const_mul]
      exact integral_mono_ae (hi i).norm ((hG i).const_mul A) (hbound i)
    refine ⟨integrable_series hi hIs,?_⟩
    rw [show C.action b (Matrix.vecCons u π) = ∑' i, (D i).action b (Matrix.vecCons u π)
      from hDact b π hab]
    simp_rw [fun i => (D i).coordinateSlice_action_integral hK (hDu i) hab]
    exact integral_tsum_of_summable_integral_norm hi hIs
  · intro b π hab φ hφ
    filter_upwards [ae_all_iff.mpr (fun i =>
      (D i).ae_coordinateSliceTotal_weighted (hDu i) hab φ hφ)] with t ht
    change (∑' i, (Q i t).action (fun x => φ (u x)*b x) π) = φ t * ∑' i, (Q i t).action b π
    exact (tsum_congr fun i => ht i).trans tsum_mul_left

end CAT0Fillings.IntegerChart

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

attribute [local instance] Classical.propDecidable

universe u

end CAT0Fillings

open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable
open BorelCoefficients BorelRestriction MassMeasure

end CAT0Fillings

end

end OAI
