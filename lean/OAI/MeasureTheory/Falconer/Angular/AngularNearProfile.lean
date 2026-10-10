import OAI.MeasureTheory.Falconer.Graphs.ProductEnergyMaximum

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ENNReal

theorem angular_near_profile_factor (N : ℕ) (hN : 0 < N)
    (m₁ m₂ : ℝ → ℝ) (a p lam : ℝ) :
    (2:ℝ)^(2*(p-a))*
      ((((2:ℝ)^N)^(-m₁ p)/((2:ℝ)^N)^(-m₁ a))^2*
       (((2:ℝ)^N)^(-m₂ p)/((2:ℝ)^N)^(-m₂ a))^2) *
      3748096 * (4096*((2:ℝ)^N)^(m₁ p-m₁ a+(m₂ p-m₂ a)+12*lam)) =
      15352201216*((2:ℝ)^N)^(-(m₁ p-p/N-(m₁ a-a/N))-(m₂ p-p/N-(m₂ a-a/N))+12*lam) := by
  have hR : 0 < (2:ℝ)^N := by positivity
  rw [two_rpow_as_scale N hN]
  simp only [← Real.rpow_sub hR,pow_two]
  have he (x y z t : ℝ) : x*(y*y*(z*z))*3748096*(4096*t) = 15352201216*(x*y*y*z*z*t) := by ring
  rw [he]
  simp only [← Real.rpow_add hR]
  congr 2
  ring

theorem angular_near_profile_sum_bound {ι : Type*} (S : Finset ι) (E : ι → ℝ≥0∞)
    (N : ℕ) (hN : 0 < N) (m₁ m₂ : ℝ → ℝ) (a p lam : ℝ)
    (hcard : (S.card:ℝ) ≤ 4096*((2:ℝ)^N)^(m₁ p-m₁ a+(m₂ p-m₂ a)+12*lam)) :
    (2:ℝ)^(2*(p-a))*
      ((((2:ℝ)^N)^(-m₁ p)/((2:ℝ)^N)^(-m₁ a))^2*
       (((2:ℝ)^N)^(-m₂ p)/((2:ℝ)^N)^(-m₂ a))^2) *
      (3748096 * ∑ i ∈ S, (E i).toReal) ≤
      15352201216*((2:ℝ)^N)^(-(m₁ p-p/N-(m₁ a-a/N))-(m₂ p-p/N-(m₂ a-a/N))+12*lam)*
        finiteEnergyMaximum S E := by
  have hh := (sum_energy_le_maximum S E).trans
    (mul_le_mul_of_nonneg_right hcard (finiteEnergyMaximum_nonneg S E))
  calc
    _ ≤ (2:ℝ)^(2*(p-a))*
      ((((2:ℝ)^N)^(-m₁ p)/((2:ℝ)^N)^(-m₁ a))^2*
       (((2:ℝ)^N)^(-m₂ p)/((2:ℝ)^N)^(-m₂ a))^2) *
      (3748096 * ((4096*((2:ℝ)^N)^(m₁ p-m₁ a+(m₂ p-m₂ a)+12*lam))*finiteEnergyMaximum S E)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh (by norm_num)) (by positivity)
    _ = _ := by
      rw [← mul_assoc,← mul_assoc,angular_near_profile_factor N hN]

end PlanarFalconer

end OAI
