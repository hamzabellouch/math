import OAI.NumberTheory.Ostmann.Construction.LogCellBounds
import OAI.NumberTheory.Ostmann.Construction.WeightedSelection

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

abbrev LogCellSample (c : ℝ) (E : Finset ℕ) := ↥(logCellPrimes c \ E)

theorem logCell_sample_sum (c : ℝ) (E : Finset ℕ) :
    (∑ p : LogCellSample c E, logCellWeight c p)=logCellMass c E := by
  exact Finset.sum_coe_sort _ _

def logCellPrior (c : ℝ) (E : Finset ℕ) (hZ : 0<logCellMass c E) :
    FinitePrior (LogCellSample c E) :=
  FinitePrior.fromWeights (fun p => logCellWeight c p)
    (fun p => logCellWeight_nonneg c p) (by rw [logCell_sample_sum]; exact hZ)

theorem logCellPrior_mass (c : ℝ) (E : Finset ℕ) (hZ : 0<logCellMass c E)
    (p : LogCellSample c E) :
    (logCellPrior c E hZ).mass p =
      Ostmann.smoothPartition (Real.log (p:ℕ)-c)/((p:ℕ)*logCellMass c E) := by
  change logCellWeight c p/(∑ q : LogCellSample c E, logCellWeight c q)=_
  rw [logCell_sample_sum, logCellWeight, div_div]

theorem logCellSample_prime {c : ℝ} {E : Finset ℕ} (p : LogCellSample c E) :
    Nat.Prime (p:ℕ) := (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.property).1).2

theorem logCellSample_not_deleted {c : ℝ} {E : Finset ℕ} (p : LogCellSample c E) :
    (p:ℕ)∉E := (Finset.mem_sdiff.mp p.property).2

theorem logCellPrior_mass_le (c : ℝ) (E : Finset ℕ) (hZ : 0<logCellMass c E)
    (p : LogCellSample c E) :
    (logCellPrior c E hZ).mass p ≤ 1/((p:ℕ)*logCellMass c E) := by
  rw [logCellPrior_mass]
  exact div_le_div_of_nonneg_right (Ostmann.smoothPartition_le_one _)
    (mul_nonneg (Nat.cast_nonneg _) hZ.le)

end Ostmann.Construction

end

end OAI
