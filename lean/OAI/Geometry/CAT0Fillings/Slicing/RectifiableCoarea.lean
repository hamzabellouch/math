import Mathlib
import OAI.Geometry.CAT0Fillings.Slicing.ScalarCoarea
import OAI.Geometry.CAT0Fillings.Currents.ChartSums

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

namespace CAT0Fillings
open Set MeasureTheory Filter BorelRestriction MassMeasure
open scoped Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ}
lemma chartFamily_restrict_eq {T : Functional X k} (hT : IsMetricCurrent T)
    (C : ℕ → IntegerChart X k) (hd : Pairwise (fun i j => Disjoint (C i).image (C j).image))
    (hC : ∀ i, IsMetricCurrent (C i).action)
    (hsum : Summable (fun i => mass (C i).action))
    (heq : ∀ b π, T b π = ∑' i, (C i).action b π) (i : ℕ) :
    restrictCurrent hT (C i).image = (C i).action := by
  funext b π
  rw [restrictCurrent_sum hT hC hsum heq (C i).measurableSet_image,
    tsum_eq_single i (fun j hj => by
      rw [(C j).restrictCurrent_disjoint_eq_zero (hC j) (C i).measurableSet_image (hd hj)]
      rfl),
    (C i).restrictCurrent_image_eq (hC i) (C i).measurableSet_image (subset_refl _)]

lemma chartFamily_mass_sum_le {T : Functional X k} (hT : IsMetricCurrent T)
    (C : ℕ → IntegerChart X k) (hd : Pairwise (fun i j => Disjoint (C i).image (C j).image))
    (hC : ∀ i, IsMetricCurrent (C i).action)
    (hsum : Summable (fun i => mass (C i).action))
    (heq : ∀ b π, T b π = ∑' i, (C i).action b π) :
    (∑' i, mass (C i).action) ≤ mass T := by
  have hr i := chartFamily_restrict_eq hT C hd hC hsum heq i
  simpa only [hr] using tsum_restriction_mass_le hT (fun i => (C i).image)
    (fun i => (C i).measurableSet_image) hd

theorem integerRectifiable_tsum {T : ℕ → Functional X k}
    (hT : ∀ i, IsMetricCurrent (T i)) (hI : ∀ i, IntegerRectifiable (T i))
    (hsum : Summable (fun i => mass (T i))) :
    IntegerRectifiable (fun b π => ∑' i, T i b π) := by
  choose C hd hC hCS heq using hI
  have hmass i := chartFamily_mass_sum_le (hT i) (C i) (hd i) (hC i) (hCS i) (heq i)
  have hpair : Summable (fun p : ℕ × ℕ => mass (C p.1 p.2).action) := by
    apply (summable_prod_of_nonneg (fun p => mass_nonneg _)).mpr
    exact ⟨hCS,hsum.of_nonneg_of_le (fun i => tsum_nonneg (fun j => mass_nonneg _)) hmass⟩
  let D (i : ℕ) := C (Nat.pairEquiv.symm i).1 (Nat.pairEquiv.symm i).2
  have hD i : IsMetricCurrent (D i).action := hC _ _
  have hDS : Summable (fun i => mass (D i).action) := (Nat.pairEquiv.symm.summable_iff (f := fun p : ℕ × ℕ => mass (C p.1 p.2).action)).mpr hpair
  have heq' : (fun b π => ∑' i, T i b π) = (fun b π => ∑' i, (D i).action b π) := by
    funext b π
    have hact : Summable (fun p : ℕ × ℕ => (C p.1 p.2).action b π) :=
      (Nat.pairEquiv.symm.summable_iff (f := fun p : ℕ × ℕ => (C p.1 p.2).action b π)).mp (summable_actions_all hD hDS b π)
    change (∑' i, T i b π) = ∑' i, (C (Nat.pairEquiv.symm i).1 (Nat.pairEquiv.symm i).2).action b π
    calc
      (∑' i, T i b π) = ∑' i, ∑' j, (C i j).action b π := tsum_congr (fun i => heq i b π)
      _ = ∑' p : ℕ × ℕ, (C p.1 p.2).action b π := hact.tsum_prod.symm
      _ = _ := (Nat.pairEquiv.symm.tsum_eq (fun p : ℕ × ℕ => (C p.1 p.2).action b π)).symm
  rw [heq']
  exact integerRectifiable_chartSum D hD hDS

end CAT0Fillings
namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}

theorem integerRectifiable_scalar_coarea {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hI : IntegerRectifiable T) (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∃ (S : ℝ → Functional X k) (G : ℝ → ℝ),
      Integrable G ∧ (∀ t, 0 ≤ G t) ∧
      (∀ᵐ t : ℝ, IsMetricCurrent (S t) ∧ IntegerRectifiable (S t) ∧ mass (S t) ≤ G t) ∧
      (∫ t : ℝ, G t) ≤ K * mass T ∧
      (∀ b π, Admissible b π → Integrable (fun t : ℝ => S t b π) ∧
        T b (Matrix.vecCons u π) = ∫ t : ℝ, S t b π) ∧
      (∀ b π, Admissible b π → ∀ φ : ℝ → ℝ, BoundedLip (φ ∘ u) →
        ∀ᵐ t : ℝ, S t (fun x => φ (u x)*b x) π = φ t * S t b π) := by
  obtain ⟨C,hd,hC,hCS,heq⟩ := hI
  have hmass := chartFamily_mass_sum_le hT C hd hC hCS heq
  choose Q G hG hG0 hQ hGI hQact hQweight using fun i => (C i).exists_scalar_coarea hX hK
  let S : ℝ → Functional X k := fun t b π => ∑' i, Q i t b π
  have hGIs : Summable (fun i => ∫ t : ℝ, G i t) := by
    apply (hCS.mul_left (K:ℝ)).of_nonneg_of_le
      (fun i => integral_nonneg (hG0 i)) hGI
  have hGn : Summable (fun i => ∫ t : ℝ, ‖G i t‖) := by
    simpa only [Real.norm_of_nonneg (hG0 _ _)] using hGIs
  have hGa : ∀ᵐ t : ℝ, Summable (fun i => G i t) := by
    simpa only [Real.norm_of_nonneg (hG0 _ _)] using ae_summable_norm_of_integral hG hGn
  have hQa : ∀ᵐ t : ℝ, Summable (fun i => mass (Q i t)) := by
    filter_upwards [hGa,ae_all_iff.mpr hQ] with t hs hm
    exact hs.of_nonneg_of_le (fun i => mass_nonneg _) (fun i => (hm i).2.2)
  refine ⟨S,fun t => ∑' i, G i t,integrable_series hG hGn,
    fun t => tsum_nonneg (fun i => hG0 i t),?_,?_,?_,?_⟩
  · filter_upwards [hQa,hGa,ae_all_iff.mpr hQ] with t hqt hgt hmt
    refine ⟨isMetricCurrent_tsum (fun i => (hmt i).1) hqt,
      integerRectifiable_tsum (fun i => (hmt i).1) (fun i => (hmt i).2.1) hqt,?_⟩
    exact (mass_tsum_le (fun i => (hmt i).1) hqt).trans
      (hqt.tsum_le_tsum (fun i => (hmt i).2.2) hgt)
  · rw [←integral_tsum_of_summable_integral_norm hG hGn]
    calc
      (∑' i, ∫ t : ℝ, G i t) ≤ ∑' i, (K:ℝ)*mass (C i).action :=
        hGIs.tsum_le_tsum hGI (hCS.mul_left _)
      _ = (K:ℝ)*(∑' i, mass (C i).action) := tsum_mul_left
      _ ≤ (K:ℝ)*mass T := mul_le_mul_of_nonneg_left hmass K.coe_nonneg
  · intro b π hab
    have hi i : Integrable (fun t : ℝ => Q i t b π) := (hQact i b π hab).1
    choose L hL using hab.2
    obtain ⟨M,hM⟩ := hab.1.2
    let A : ℝ := (∏ j, (L j:ℝ)) * max M 0
    have hA : 0 ≤ A := mul_nonneg (Finset.prod_nonneg fun j _ => (L j).coe_nonneg) (le_max_right _ _)
    have hbound i : ∀ᵐ t : ℝ, ‖Q i t b π‖ ≤ A * G i t := by
      filter_upwards [hQ i] with t ht
      rw [Real.norm_eq_abs]
      exact (ht.1.mass_bound_uniform hab.1 L hL
        (fun x => (hM x).trans (le_max_left _ _))).trans
          (mul_le_mul_of_nonneg_left ht.2.2 hA)
    have hIs : Summable (fun i => ∫ t : ℝ, ‖Q i t b π‖) := by
      apply (hGIs.mul_left A).of_nonneg_of_le (fun i => integral_nonneg (fun _ => norm_nonneg _))
      intro i
      rw [←integral_const_mul]
      exact integral_mono_ae (hi i).norm ((hG i).const_mul A) (hbound i)
    refine ⟨integrable_series hi hIs,?_⟩
    rw [heq]
    simp_rw [fun i => (hQact i b π hab).2]
    exact integral_tsum_of_summable_integral_norm hi hIs
  · intro b π hab φ hφ
    filter_upwards [ae_all_iff.mpr (fun i => hQweight i b π hab φ hφ)] with t ht
    change (∑' i, Q i t (fun x => φ (u x)*b x) π) = φ t * ∑' i, Q i t b π
    exact (tsum_congr fun i => ht i).trans tsum_mul_left

end CAT0Fillings

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

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

attribute [local instance] Classical.propDecidable

universe u

end CAT0Fillings

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
