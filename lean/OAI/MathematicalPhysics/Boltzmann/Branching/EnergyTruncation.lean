import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveRestrictedChain
import OAI.MathematicalPhysics.Boltzmann.Branching.Moments

namespace OAI

/-! # Bounded velocity truncations determine the full energy inequality -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness

def truncatedEnergyWeight (n : ℕ) (p : Phase) : ℝ := min (‖p.2‖^2) (n:ℝ)

theorem truncatedEnergyWeight_measurable (n : ℕ) : Measurable (truncatedEnergyWeight n) :=
  (measurable_snd.norm.pow_const 2).min measurable_const

theorem truncatedEnergyWeight_nonneg (n : ℕ) (p : Phase) : 0 ≤ truncatedEnergyWeight n p :=
  le_min (sq_nonneg _) (Nat.cast_nonneg n)

theorem truncatedEnergyWeight_abs_le (n : ℕ) (p : Phase) : |truncatedEnergyWeight n p| ≤ n := by
  rw [abs_of_nonneg (truncatedEnergyWeight_nonneg n p)]
  exact min_le_right _ _

theorem truncatedEnergy_integrable {f : Density} (hf : Integrable f) (n : ℕ) :
    Integrable (fun p => truncatedEnergyWeight n p*f p) :=
  hf.bdd_mul (truncatedEnergyWeight_measurable n).aestronglyMeasurable
    (ae_of_all _ (truncatedEnergyWeight_abs_le n))

theorem energy_le_of_truncated {f : Density} (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : FiniteEntropyDatum f) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n, (∫ p, truncatedEnergyWeight n p*f p) ≤ C) : energy f ≤ C := by
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  rw [energy,ofReal_integral_eq_lintegral_ofReal hi.integrable_energy
    (ae_of_all _ (fun p => mul_nonneg (sq_nonneg _) (hf p)))]
  apply lintegral_of_ae_tendsto_le
    (fun n => (truncatedEnergyWeight_measurable n).mul hfm)
  · apply ae_of_all
    intro p
    apply (tendsto_const_nhds (x := ‖p.2‖^2*f p)).congr'
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop (‖p.2‖^2))] with n hn
    change ‖p.2‖^2*f p = min (‖p.2‖^2) (n:ℝ)*f p
    rw [min_eq_left hn]
  · intro n
    change (∫⁻ p, ENNReal.ofReal (truncatedEnergyWeight n p*f p)) ≤ ENNReal.ofReal C
    rw [← ofReal_integral_eq_lintegral_ofReal (truncatedEnergy_integrable hi.integrable n)
      (ae_of_all _ (fun p => mul_nonneg (truncatedEnergyWeight_nonneg n p) (hf p)))]
    exact ENNReal.ofReal_le_ofReal (hb n)

end BoltzmannNonuniqueness

end

end OAI
