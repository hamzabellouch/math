import Mathlib
import OAI.Geometry.WeakHessian.Transport.ActionIntervalIntegrable

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set
open scoped NNReal
open scoped Topology ENNReal NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

namespace WeakHessianCalculus

lemma action_dist_primitive_values {a : ℝ → ℝ≥0∞}
    (ha : AEMeasurable a (volume.restrict (Icc (0 : ℝ) 1)))
    (hfin : (∫⁻ t in Icc (0 : ℝ) 1, a t) < ∞)
    {s t u v : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hst : s ≤ t) (hqt : ENNReal.ofReal |v - u| ≤ ∫⁻ r in Icc s t, a r) :
    dist u v ≤ dist (∫ r in (0 : ℝ)..s, (a r).toReal)
      (∫ r in (0 : ℝ)..t, (a r).toReal) := by
  have hsub : Icc s t ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hs.1 ht.2
  have hstfin : (∫⁻ r in Icc s t, a r) ≠ ∞ :=
    ne_top_of_le_ne_top hfin.ne (lintegral_mono_set hsub)
  have hast : AEMeasurable a (volume.restrict (Icc s t)) :=
    ha.mono_measure (Measure.restrict_mono_set _ hsub)
  have hti := action_intervalIntegrable ha hfin
  have hi_s : IntervalIntegrable (fun r => (a r).toReal) volume 0 s :=
    hti.mono_set (by simpa only [uIcc_of_le hs.1, uIcc_of_le zero_le_one]
      using (Icc_subset_Icc le_rfl hs.2))
  have hi_t : IntervalIntegrable (fun r => (a r).toReal) volume 0 t :=
    hti.mono_set (by simpa only [uIcc_of_le ht.1, uIcc_of_le zero_le_one]
      using (Icc_subset_Icc le_rfl ht.2))
  have hreal : (∫⁻ r in Icc s t, a r).toReal = ∫ r in s..t, (a r).toReal := by
    rw [← integral_toReal hast (ae_lt_top' hast hstfin),
      integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hst]
  calc
    dist u v = |v - u| := by rw [dist_comm, Real.dist_eq]
    _ ≤ (∫⁻ r in Icc s t, a r).toReal := by
      simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using ENNReal.toReal_mono hstfin hqt
    _ = (∫ r in (0 : ℝ)..t, (a r).toReal) - ∫ r in (0 : ℝ)..s, (a r).toReal :=
      hreal.trans (intervalIntegral.integral_interval_sub_left hi_t hi_s).symm
    _ ≤ _ := by rw [dist_comm, Real.dist_eq]; exact le_abs_self _

lemma eq_of_dense_action_bounds {q : ℝ → ℝ} {a : ℝ → ℝ≥0∞}
    (hq : AbsolutelyContinuousOnInterval q 0 1)
    (ha : AEMeasurable a (volume.restrict (Icc (0 : ℝ) 1)))
    (hfin : (∫⁻ t in Icc (0 : ℝ) 1, a t) < ∞)
    (d : ℕ → Icc (0 : ℝ) 1) (hd : DenseRange d)
    {t b : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hbound : ∀ i, ENNReal.ofReal |b - q (d i)| ≤ ∫⁻ r in uIcc (d i : ℝ) t, a r) :
    q t = b := by
  let A : ℝ → ℝ := fun s => ∫ r in (0 : ℝ)..s, (a r).toReal
  have hA : AbsolutelyContinuousOnInterval A 0 1 :=
    (action_intervalIntegrable ha hfin).absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hcA : Continuous (fun s : Icc (0 : ℝ) 1 => A s) := by
    apply hA.continuousOn.comp_continuous continuous_subtype_val
    intro s
    simpa only [uIcc_of_le zero_le_one] using s.property
  have hcq : Continuous (fun s : Icc (0 : ℝ) 1 => q s) := by
    apply hq.continuousOn.comp_continuous continuous_subtype_val
    intro s
    simpa only [uIcc_of_le zero_le_one] using s.property
  have hi : ∀ i, dist (q (d i)) b ≤ dist (A (d i)) (A t) := by
    intro i
    rcases le_total (d i : ℝ) t with h|h
    · exact action_dist_primitive_values ha hfin (d i).property ht h
        (by simpa only [uIcc_of_le h] using hbound i)
    · simpa only [dist_comm] using
        action_dist_primitive_values ha hfin ht (d i).property h
          (by simpa only [uIcc_of_ge h, abs_sub_comm] using hbound i)
  have hall := hd.induction_on (p := fun s : Icc (0 : ℝ) 1 =>
      dist (q s) b ≤ dist (A s) (A t)) (⟨t,ht⟩ : Icc (0 : ℝ) 1)
    (isClosed_le (hcq.dist continuous_const) (hcA.dist continuous_const)) hi
  exact dist_le_zero.mp (by simpa only [dist_self] using hall)

end WeakHessianCalculus

end
end InlinedFile0

end OAI
