import OAI.Probability.IsingPerceptron.NamespaceSplit

namespace OAI

/-! Centering a logpartition difference using its two pressure variances. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

/-- The frozen CGF of one perturbation is a scaled difference of two
pressures. Both variances suffice even though those pressures are dependent. -/
theorem centered_scaled_difference_L1_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {F G Z : Ω → ℝ} {a B : ℝ}
    (hF : MemLp F 2 P) (hG : MemLp G 2 P)
    (hvF : variance F P ≤ B) (hvG : variance G P ≤ B)
    (he : Z =ᵐ[P] fun ω => a * (F ω - G ω)) :
    MemLp Z 2 P ∧
      (∫ ω, |Z ω - ∫ ω', Z ω' ∂P| ∂P) ≤ 2 * |a| * Real.sqrt B := by
  have hiF := hF.integrable (by norm_num)
  have hiG := hG.integrable (by norm_num)
  have hZ : MemLp Z 2 P := MemLp.ae_eq he.symm ((hF.sub hG).const_mul a)
  have hcF : (∫ ω, |F ω - ∫ ω', F ω' ∂P| ∂P) ≤ Real.sqrt B :=
    (l1_center_le_sqrt_variance hF).trans (Real.sqrt_le_sqrt hvF)
  have hcG : (∫ ω, |G ω - ∫ ω', G ω' ∂P| ∂P) ≤ Real.sqrt B :=
    (l1_center_le_sqrt_variance hG).trans (Real.sqrt_le_sqrt hvG)
  have hc := centered_sub_L1_bound P hiF hiG hcF hcG
  have hm : (∫ ω, Z ω ∂P) = a * (∫ ω, F ω - G ω ∂P) := by
    rw [integral_congr_ae he, integral_const_mul]
  refine ⟨hZ, ?_⟩
  rw [hm]
  calc
    _ = ∫ ω, |a| * |F ω - G ω - ∫ ω', F ω' - G ω' ∂P| ∂P := by
      apply integral_congr_ae
      filter_upwards [he] with ω hω
      rw [hω, ← mul_sub, abs_mul]
    _ = |a| * (∫ ω, |F ω - G ω - ∫ ω', F ω' - G ω' ∂P| ∂P) := integral_const_mul _ _
    _ ≤ |a| * (Real.sqrt B + Real.sqrt B) :=
      mul_le_mul_of_nonneg_left hc (abs_nonneg _)
    _ = _ := by ring

end InvariantIsing

end

end OAI
