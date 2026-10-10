import OAI.Probability.InvariantIsing.Fields.PhysicalFieldPermutation
import OAI.Probability.InvariantIsing.Core.FiniteFieldMatchingBound
import OAI.Probability.InvariantIsing.Pressure.GroundStateMean

namespace OAI

/-! Field populations with nearby label proportions have nearby Haar-mean pressures. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace InvariantIsing

lemma abs_rotatedPressure_fields_le {N : ℕ} (eig c d : Fin N → ℝ) (U : Rotation N) :
    |rotatedPressure eig U c-rotatedPressure eig U d| ≤
      (N : ℝ)⁻¹*∑ i, |c i-d i| := by
  have hh := abs_logPartition_sub_le
    (fun σ => rotatedEnergy eig U σ+fieldEnergy c σ)
    (fun σ => rotatedEnergy eig U σ+fieldEnergy d σ)
    (∑ i, |c i-d i|) (fun σ => by
      simpa only [add_sub_add_left_eq_sub] using abs_fieldEnergy_sub_le c d σ)
  have hni : (0 : ℝ)≤(N : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg N)
  simpa only [rotatedPressure,← mul_sub,abs_mul,abs_of_nonneg hni] using
    mul_le_mul_of_nonneg_left hh hni

lemma physical_mean_field_l1_le {N : ℕ} (hN : 0<N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] (eig c d : Fin N → ℝ) :
    |(∫ U, rotatedPressure eig (matrixRotation U⁻¹) c ∂μ)-
      ∫ U, rotatedPressure eig (matrixRotation U⁻¹) d ∂μ| ≤
      (N : ℝ)⁻¹*∑ i, |c i-d i| := by
  have hc := integrable_physicalPressure hN μ id measurable_id eig c
  have hd := integrable_physicalPressure hN μ id measurable_id eig d
  simp only [id_eq] at hc hd
  change |(∫ U, rotatedPressure eig (matrixRotation U⁻¹) c ∂μ)-
      ∫ U, rotatedPressure eig (matrixRotation U⁻¹) d ∂μ| ≤ _
  rw [← integral_sub hc hd]
  have hh := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun U => rotatedPressure eig (matrixRotation U⁻¹) c-rotatedPressure eig (matrixRotation U⁻¹) d)
    (C := (N : ℝ)⁻¹*∑ i, |c i-d i|)
    (ae_of_all _ fun U => by simpa only [Real.norm_eq_abs] using abs_rotatedPressure_fields_le eig c d (matrixRotation U⁻¹))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

lemma physical_mean_field_counts_le {N : ℕ} (hN : 0<N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (eig : Fin N → ℝ) {A : Type*} [Fintype A] [DecidableEq A]
    (g h : Fin N → A) (b : A → ℝ) {B : ℝ} (hB : 0≤B) (hb : ∀ a, |b a|≤B) :
    |(∫ U, rotatedPressure eig (matrixRotation U⁻¹) (fun i => b (g i)) ∂μ)-
      ∫ U, rotatedPressure eig (matrixRotation U⁻¹) (fun i => b (h i)) ∂μ| ≤
      2*B*∑ a, |(spinGroupSize g a : ℝ)/N-(spinGroupSize h a : ℝ)/N| := by
  obtain ⟨p,hp⟩ := exists_field_permutation_l1_bound g h b hB hb
  rw [← physical_meanPressure_field_permutation μ p eig (fun i => b (h i))]
  refine (physical_mean_field_l1_le hN μ eig _ _).trans
    ((mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr (Nat.cast_nonneg N))).trans_eq ?_)
  have hnz : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  simp_rw [← sub_div,abs_div,abs_of_pos hnz]
  rw [← Finset.sum_div]
  ring

end InvariantIsing

end

end OAI
