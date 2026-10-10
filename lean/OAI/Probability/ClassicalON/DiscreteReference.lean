import OAI.Probability.ClassicalON.BondSigns

namespace OAI

universe uV

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace ClassicalON

variable {V : Type uV} [Fintype V]

theorem isingReference_singleton (s : V → Bool) :
    isingReference {s}=(2 : ℝ≥0∞)⁻¹^Fintype.card V := by
  classical
  rw [isingReference,Measure.pi_singleton]
  simp [signLaw]

open scoped Classical in
theorem integral_isingReference (f : (V → Bool) → ℝ) :
    (∫ s,f s ∂isingReference)=(2 : ℝ)⁻¹^Fintype.card V*∑ s,f s := by
  classical
  rw [integral_fintype (compact_integrable continuous_of_discreteTopology)]
  simp only [Measure.real,isingReference_singleton,ENNReal.toReal_pow,ENNReal.toReal_inv,
    ENNReal.toReal_ofNat,smul_eq_mul,← Finset.mul_sum]

end ClassicalON

end

end OAI
