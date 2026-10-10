import Mathlib
import OAI.Probability.GaussianInformation.Kernel.GeneralDrift

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
open Coercivity Bayes NoisyDrift
lemma local_energy_bound {d N : ℕ} (hd : 16 ≤ d) (hN : 0 < N)
    (ρ : Measure (Ambient d)) [IsFiniteMeasure ρ] (hρ : ρ ≤ sphereProbability d)
    (rule : LocalRule (d/16) d N) :
    (∑ w,energy (ρ.withDensity (fun s => ENNReal.ofReal (rule.response w s)))) ≤
      energy ρ+(ρ univ).toReal*(95*(d:ℝ)+6*Real.log (1/(ρ univ).toReal)/(d:ℝ)+
        2*Real.log (N:ℝ)/(d:ℝ)+Real.log (N:ℝ)/(d/16:ℕ)) := by
  by_cases hz : ρ univ=0
  · have he := Measure.measure_univ_eq_zero.mp hz
    simp [he,energy_zero]
  · let a := (ρ univ).toReal
    have ha : 0 < a := ENNReal.toReal_pos hz (measure_ne_top _ _)
    have ha1 : a ≤ 1 := by
      have hh := hρ univ
      rw [measure_univ (μ := sphereProbability d)] at hh
      simpa [a] using ENNReal.toReal_mono ENNReal.one_ne_top hh
    let ν := proper ρ
    have : IsProbabilityMeasure ν := proper_probability ρ
    have hH : 1 ≤ 1/a := (le_div_iff₀ ha).mpr (by simpa using ha1)
    have hν : ν ≤ ENNReal.ofReal (1/a) • sphereProbability d := by
      have he : ENNReal.ofReal (1/a)=(ρ univ)⁻¹ := by
        rw [one_div,ENNReal.ofReal_inv_of_pos ha,ENNReal.ofReal_toReal (measure_ne_top _ _)]
      rw [he]
      change proper ρ ≤ _
      rw [proper,ite_eq_right hz]
      exact smul_le_smul_left _ hρ
    have he (w : Fin N) : energy (ρ.withDensity (fun s => ENNReal.ofReal (rule.response w s)))=
        a*(mass ν (rule.response w)*Phi (post ν (rule.response w))) := by
      have := density_finite ν (rule.response w) (fun s => (rule.response_bounds w s).2)
      calc _ = energy (ENNReal.ofReal a • ν.withDensity (fun s => ENNReal.ofReal (rule.response w s))) := by
                 congr 1
                 rw [← withDensity_smul_measure]
                 congr 1
                 exact (mass_smul_proper ρ).symm
           _ = a*energy (ν.withDensity (fun s => ENNReal.ofReal (rule.response w s))) := energy_smul _ a ha.le
           _ = _ := by rw [energy_density ν _ (rule.measurable_response w)
                       (fun s => (rule.response_bounds w s).1) (fun s => (rule.response_bounds w s).2)]
    have hh := mul_le_mul_of_nonneg_left (borel_bound hd hN ν hH hν rule) ha.le
    simp_rw [he]
    rw [← Finset.mul_sum]
    rw [energy_proper]
    change _ ≤ a*Phi ν+a*(95*(d:ℝ)+6*Real.log (1/a)/(d:ℝ)+2*Real.log (N:ℝ)/(d:ℝ)+Real.log (N:ℝ)/(d/16:ℕ))
    calc _ ≤ a*(Phi ν+95*(d:ℝ)+6*Real.log (1/a)/(d:ℝ)+2*Real.log (N:ℝ)/(d:ℝ)+Real.log (N:ℝ)/(d/16:ℕ)) := hh
         _ = _ := by ring
end KernelPotential.MassPotential

end OAI
