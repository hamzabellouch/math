import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTailEnergyOperations
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRadialPairL2

namespace OAI

/-! Conversion between the two radial channel energies and the pair norm. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
local notation "V" => ℂ × ℂ

theorem spectralWeighted_pair_integrable (U : ℝ → V) (R : ℝ) (hR : 0≤R)
    (hU : ContinuousOn U (Ioi R))
    (hp : IntegrableOn (fun r => r^11*‖(U r).1‖^2) (Ioi R))
    (hm : IntegrableOn (fun r => r^11*‖(U r).2‖^2) (Ioi R)) :
    IntegrableOn (fun r => r^11*‖U r‖^2) (Ioi R) := by
  have hi := radial_pair_energy_integrable (fun r => (U r).1) (fun r => (U r).2) R hp hm
  apply hi.mono' (((continuousOn_id.pow 11).mul (hU.norm.pow 2)).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr₀ : 0≤r := hR.trans hr.le
  change ‖(r^11*‖U r‖^2 : ℝ)‖ ≤ r^11*homogeneousPairEnergy ((U r).1,(U r).2)
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (pow_nonneg hr₀ 11) (sq_nonneg ‖U r‖))]
  exact mul_le_mul_of_nonneg_left (homogeneousPairEnergy_lower (U r)) (pow_nonneg hr₀ 11)

theorem spectralWeighted_scalar_of_pair (U : ℝ → V) (f : ℝ → ℂ) (R : ℝ) (hR : 0≤R)
    (hf : ContinuousOn f (Ioi R)) (hb : ∀ r, R<r → ‖f r‖≤‖U r‖)
    (hU : IntegrableOn (fun r => r^11*‖U r‖^2) (Ioi R)) :
    IntegrableOn (fun r => r^11*‖f r‖^2) (Ioi R) := by
  apply hU.mono' (((continuousOn_id.pow 11).mul (hf.norm.pow 2)).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr₀ : 0≤r := hR.trans hr.le
  change ‖(r^11*‖f r‖^2 : ℝ)‖ ≤ r^11*‖U r‖^2
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (pow_nonneg hr₀ 11) (sq_nonneg ‖f r‖))]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (hb r hr) 2) (pow_nonneg hr₀ 11)

end DefocusingNLS

end OAI
