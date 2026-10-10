import Mathlib
import OAI.Probability.GaussianInformation.Kernel.MassPotential

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal
namespace KernelPotential.MassPotential
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Coercivity Bayes
lemma energy_zero {d : ℕ} : energy (0 : Measure (Ambient d))=0 := by simp [energy]
lemma energy_smul {d : ℕ} (ρ : Measure (Ambient d)) [IsFiniteMeasure ρ] (a : ℝ) (ha : 0 ≤ a) :
    energy (ENNReal.ofReal a • ρ)=a*energy ρ := by
  have := proper_probability ρ
  calc energy (ENNReal.ofReal a • ρ) = energy (ENNReal.ofReal (a*(ρ univ).toReal) • proper ρ) := by
         rw [ENNReal.ofReal_mul ha,mul_smul,mass_smul_proper]
       _ = (a*(ρ univ).toReal)*Phi (proper ρ) := energy_smul_probability _ _ (mul_nonneg ha ENNReal.toReal_nonneg)
       _ = a*energy ρ := by rw [energy_proper]; ring
lemma density_mass {d : ℕ} (ν : Measure (Ambient d)) [IsFiniteMeasure ν]
    (r : Ambient d → ℝ) (hr : Measurable r) (hr0 : ∀ s,0 ≤ r s) (hr1 : ∀ s,r s ≤ 1) :
    (ν.withDensity (fun s => ENNReal.ofReal (r s))) univ=ENNReal.ofReal (mass ν r) := by
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal (integrable_rule ν r hr hr0 hr1) (ae_of_all _ hr0)).symm
lemma density_le {d : ℕ} (ν : Measure (Ambient d)) [SFinite ν] (r : Ambient d → ℝ) (hr1 : ∀ s,r s ≤ 1) :
    ν.withDensity (fun s => ENNReal.ofReal (r s)) ≤ ν := by
  simpa using density_bounded ν r hr1
lemma density_finite {d : ℕ} (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (r : Ambient d → ℝ) (hr1 : ∀ s,r s ≤ 1) :
    IsFiniteMeasure (ν.withDensity (fun s => ENNReal.ofReal (r s))) := isFiniteMeasure_of_le ν (density_le ν r hr1)
lemma energy_density {d : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (r : Ambient d → ℝ) (hr : Measurable r) (hr0 : ∀ s,0 ≤ r s) (hr1 : ∀ s,r s ≤ 1) :
    energy (ν.withDensity (fun s => ENNReal.ofReal (r s)))=mass ν r*Phi (post ν r) := by
  have ha : 0 ≤ mass ν r := integral_nonneg hr0
  by_cases haz : mass ν r=0
  · have hz : ν.withDensity (fun s => ENNReal.ofReal (r s))=0 := Measure.measure_univ_eq_zero.mp (by
      rw [density_mass ν r hr hr0 hr1,haz,ENNReal.ofReal_zero])
    simp [hz,haz,energy_zero]
  · have hap := lt_of_le_of_ne ha (Ne.symm haz)
    have := post_probability ν r hr hr0 hr1 hap
    have he : ν.withDensity (fun s => ENNReal.ofReal (r s))=ENNReal.ofReal (mass ν r) • post ν r := by
      rw [post,← withDensity_smul _ (hr.div_const _).ennreal_ofReal]
      congr 1
      ext s
      change ENNReal.ofReal (r s)=ENNReal.ofReal (mass ν r)*ENNReal.ofReal (r s/mass ν r)
      rw [ENNReal.ofReal_div_of_pos hap,div_eq_mul_inv,mul_left_comm,
        ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hap).ne' ENNReal.ofReal_ne_top,mul_one]
    rw [he,energy_smul_probability _ _ ha]
end KernelPotential.MassPotential

end OAI
