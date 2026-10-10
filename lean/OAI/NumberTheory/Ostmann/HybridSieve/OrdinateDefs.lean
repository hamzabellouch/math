import OAI.NumberTheory.Ostmann.HybridSieve.CharacterFamily
import OAI.NumberTheory.Ostmann.HybridSieve.Integral

namespace OAI

open MeasureTheory FourierTransform
open scoped Classical FourierTransform Real
namespace Ostmann.HybridSieve

noncomputable def physicalDyadicSum (N : ℕ) (a : ℕ → ℂ) {Q : ℕ}
    (i : PrimitiveFamily Q) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2*N), a n * familyValue i n *
    Complex.exp (-Complex.I*(t:ℂ)*(Real.log n:ℂ))

lemma physicalDyadicSum_continuous (N : ℕ) (a : ℕ → ℂ) {Q : ℕ}
    (i : PrimitiveFamily Q) : Continuous (physicalDyadicSum N a i) := by
  unfold physicalDyadicSum
  fun_prop

lemma physicalDyadicSum_scaled (N : ℕ) (a : ℕ → ℂ) {Q : ℕ}
    (i : PrimitiveFamily Q) (T t : ℝ) :
    physicalDyadicSum N a i (T*t) = dyadicPhaseSum N a i (T/(2*Real.pi)) t := by
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  simp only [fourierPhase, Real.fourierChar_apply]
  congr 1
  push_cast
  have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

end Ostmann.HybridSieve

end OAI
