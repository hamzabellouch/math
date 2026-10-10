import OAI.Analysis.IrrationalRotation.Sampling.CircleDigitEnergy
import OAI.Analysis.IrrationalRotation.Couplings.ProductDensity

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Invariant233.CircleDigitCoupling
open OneCoordinateCoupling

theorem marginalDensity_second_moment_le {κ m a b t : ℝ} (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) (side : Bool) :
    (∫ x, marginalDensity side κ m a b t x ^ 2 ∂baseLaw) ≤
      1 + 50 * (κ ^ 2 / m + t / m) := by
  rw [ProductDensity.integral_sq_eq_one_add_centered_sq
    (marginalDensity_memLp side κ m a b t)
    (marginalDensity_integral hm ha ha' hb hb' side)]
  exact add_le_add_right (marginalDensity_energy hm ha ha' hb hb' ht0 ht side) 1

theorem binAverage_marginalDensity_second_moment_le
    {κ m a b t : ℝ} (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) (side : Bool) (r : ℕ) [NeZero r] :
    (∫ d, (UniformQuantization.binAverage r (marginalDensity side κ m a b t) d) ^ 2
      ∂(PMF.uniformOfFintype (Fin r)).toMeasure) ≤
        1 + 50 * (κ ^ 2 / m + t / m) := by
  have hh : MemLp (marginalDensity side κ m a b t) 2
      (volume.restrict (Ico (0 : ℝ) 1)) := by
    simpa only [baseLaw_eq_restrict] using marginalDensity_memLp side κ m a b t
  have hmean : (∫ d,
      UniformQuantization.binAverage r (marginalDensity side κ m a b t) d
      ∂(PMF.uniformOfFintype (Fin r)).toMeasure) = 1 := by
    rw [UniformQuantization.integral_binAverage r (hh.integrable (by norm_num))]
    simpa only [baseLaw_eq_restrict] using
      (marginalDensity_integral (κ := κ) (t := t) hm ha ha' hb hb' side)
  rw [ProductDensity.integral_sq_eq_one_add_centered_sq MemLp.of_discrete hmean]
  apply add_le_add_right
  apply (UniformQuantization.integral_binAverage_energy_le r hh).trans
  simpa only [baseLaw_eq_restrict] using
    (marginalDensity_energy (κ := κ) hm ha ha' hb hb' ht0 ht side)

end Invariant233.CircleDigitCoupling

end

end OAI
