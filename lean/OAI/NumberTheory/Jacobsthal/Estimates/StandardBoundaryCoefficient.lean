import OAI.NumberTheory.Jacobsthal.Probability.StandardDeficitMoments

namespace OAI

namespace Erdos970

section

open Set MeasureTheory
namespace Erdos970Dependency.StandardBoundary
open NumberTheoryLean.LinearSieveFunctions NumberTheoryLean.BuchstabBridge
open NumberTheoryLean.NormalizedDeficits

noncomputable def standardCoefficient : ℝ :=
  (∫ y in Ioi 1,(y^2-1)*(1-f sieveA (y+1)))-
    ∫ y in Ioi 0,y^2*(1-F sieveA (y+1))

theorem standard_coefficient_integrable :
    IntegrableOn (fun y : ℝ => (y^2-1)*(1-f sieveA (y+1))) (Ioi 1) ∧
    IntegrableOn (fun y : ℝ => y^2*(1-F sieveA (y+1))) (Ioi 0) := by
  have h2 := shifted_deficit_moments_integrable.1.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))
  constructor
  · apply (h2.sub lower_deficit_shift_tail.1).congr_fun _ measurableSet_Ioi
    intro y _
    change y^2*lowerDeficit (y+1)-lowerDeficit (y+1) = (y^2-1)*(1-f sieveA (y+1))
    unfold lowerDeficit
    ring
  · apply shifted_deficit_moments_integrable.2.neg.congr_fun _ measurableSet_Ioi
    intro y _
    change -(y^2*upperDeficit (y+1))=y^2*(1-F sieveA (y+1))
    unfold upperDeficit
    ring

theorem standard_coefficient_decomposition :
    standardCoefficient = sieveA-(1:ℝ)/3-(sieveA-3) := by
  have h2 := shifted_deficit_moments_integrable.1.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))
  have he : (∫ y in Ioi 1,(y^2-1)*(1-f sieveA (y+1)))=
      (∫ y in Ioi 1,y^2*lowerDeficit (y+1))-(∫ y in Ioi 1,lowerDeficit (y+1)) := by
    rw [← integral_sub h2 lower_deficit_shift_tail.1]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y _
    dsimp only
    unfold lowerDeficit
    ring
  have ho : (∫ y in Ioi 0,y^2*(1-F sieveA (y+1)))=
      -(∫ y in Ioi 0,y^2*upperDeficit (y+1)) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y _
    dsimp only
    unfold upperDeficit
    ring
  have hu : (∫ y : ℝ in 0..1,y^2*lowerDeficit (y+1))=(1:ℝ)/3 := by
    calc
      _ = ∫ y : ℝ in 0..1,y^2 := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at hy
        change y^2*(1-f sieveA (y+1))=y^2
        rw [f_initial sieveA (by linarith [hy.2]),sub_zero,mul_one]
      _ = _ := by norm_num
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi shifted_deficit_moments_integrable.1 (by norm_num : (0:ℝ)≤1)
  rw [hu] at hsplit
  unfold standardCoefficient
  rw [he,ho,lower_deficit_shift_tail.2]
  linarith [shifted_deficit_moment_sum]

theorem standard_coefficient_eq : standardCoefficient=(8:ℝ)/3 := by
  rw [standard_coefficient_decomposition]
  ring

theorem literal_standard_coefficient :
    ((∫ y in Ioi 1,(y^2-1)*(1-f sieveA (y+1)))-
      ∫ y in Ioi 0,y^2*(1-F sieveA (y+1)))=(8:ℝ)/3 :=
  standard_coefficient_eq

end Erdos970Dependency.StandardBoundary

end

end Erdos970

end OAI
