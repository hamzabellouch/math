import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualWitnessMomentsGrid
import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveFrequencyNumericUniform

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

theorem eventually_witnessNontrivialFamily_energy :
    ∀ᶠ T : ℝ in atTop, ∀ Z z L : ℕ,
      1 ≤ Z → T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z → Real.log z ≤ 2*T^auxiliaryExponent →
      Squarefree L → L.primeFactors.card=auxiliaryK Z z →
      (L:ℝ) ≤ (Z:ℝ)^(1/50:ℝ) → (∀p∈L.primeFactors,z ≤ p) →
      ∀ A : ∀p:ℕ,Finset (ZMod p), ∀b∈witnessNontrivialFamily L Z A,
      (∑s∈adaptiveArraySupport L Z,
        ((((2*gridMomentParameter T:ℕ):ℝ)^2)^s.primeFactors.card)*‖b s‖^2) ≤ 1/(Z:ℝ) := by
  classical
  filter_upwards [positiveDivisorArray_actual_uniform_energy_eventually] with T hE
  intro Z z L hZ hZl hZu hz hzl hzu hL hLK hLsize hprimes A b hb
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨ha,hPa⟩ := Finset.mem_filter.mp ha
  have hab := mem_adaptiveArrayParameters ha (by omega)
  have he := hE Z z L a.modulusResidue a.multiple hZ hZl hZu hz hzl hzu hL hLK hLsize hprimes
    hPa A (adaptiveInverse a.modulusResidue) a.radius a.phaseResidue a.theta (by linarith [hab.2.2.2.2.2.2.1])
  convert he using 1
  apply Finset.sum_congr rfl
  intro s hs
  simp only [witnessGridArray,adaptiveContinuousArray,ite_eq_left hs]
  push_cast
  rfl

end Ostmann.QuadraticCenter

end

end OAI
