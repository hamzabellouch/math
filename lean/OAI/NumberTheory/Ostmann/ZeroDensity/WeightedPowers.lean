import OAI.NumberTheory.Ostmann.ZeroDensity.OccurrenceSum
import OAI.NumberTheory.Ostmann.ZeroDensity.ZeroFreeWeights

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.ZeroDensity

theorem exists_unconditional_zero_power_constants :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (Q H : ℕ)
      (exception : Option (PrimitiveFamily Q)) (X : ℝ),
      0 < Q → 0 < H → 1 < X →
      2*(10*Real.log ((Q^2*H : ℕ) : ℝ)) ≤ Real.log X →
      (∑ z ∈ retainedZeros Q exception (1/2) (H : ℝ), X^z.point.re) ≤
        X*(⌊Real.log X/2⌋₊+1 : ℝ)*(C*(1+Real.log (Q*H : ℕ))^11)*
          Real.exp (1-Real.log X*(c/Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight Q (H : ℝ))/2) := by
  obtain ⟨c,C,hc,hC,hweighted⟩ := exists_unconditional_weighted_zero_constants
  refine ⟨c,C,hc,hC,?_⟩
  intro Q H exception X hQ hH hX hscale
  have hXp : 0 < X := by linarith
  have hw := hweighted Q H exception (Real.log X) hQ hH (Real.log_pos hX) hscale
  have he (z : ZeroOccurrence Q (H : ℝ)) :
      X^z.point.re = X*Real.exp (-Real.log X*(1-z.point.re)) := by
    rw [Real.rpow_def_of_pos hXp]
    calc
      Real.exp (Real.log X*z.point.re) =
          Real.exp (Real.log X)*Real.exp (-Real.log X*(1-z.point.re)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ = _ := by rw [Real.exp_log hXp]
  simp_rw [he]
  rw [← Finset.mul_sum]
  calc
    _ ≤ X*((⌊Real.log X/2⌋₊+1 : ℝ)*(C*(1+Real.log (Q*H : ℕ))^11)*
        Real.exp (1-Real.log X*(c/Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight Q (H : ℝ))/2)) :=
      mul_le_mul_of_nonneg_left hw hXp.le
    _ = _ := by ring

end Ostmann.ZeroDensity

end

end OAI
