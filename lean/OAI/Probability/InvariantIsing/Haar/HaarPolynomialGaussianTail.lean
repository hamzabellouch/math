import OAI.Probability.InvariantIsing.Haar.HaarPolynomialTail

namespace OAI

/-! Optimization of the polynomial Chernoff bound. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Set
namespace InvariantIsing

theorem haarPolynomial_upper_tail {N : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (p : MatrixPolynomial N) (C : ℝ) (hC : 0 < C)
    (hG : ∀ U : SpecialOrthogonal N, haarPolynomialValue (haarPolynomialGamma p p) U ≤ C)
    {r : ℝ} (hr : 0 < r) :
    μ.real {U | r ≤ haarPolynomialValue p U-(∫ V, haarPolynomialValue p V ∂μ)} ≤
      Real.exp (-((N:ℝ)-2)*r^2/(2*C)) := by
  have hρ : 0 < (N:ℝ)-2 := by exact_mod_cast (show 0 < (N:ℤ)-2 by omega)
  have hb : 0 < ((N:ℝ)-2)*r/C := div_pos (mul_pos hρ hr) hC
  have h := haarPolynomial_chernoff hN μ p C hC.le hG r (((N:ℝ)-2)*r/C) hb
  convert h using 1
  congr 1
  field_simp
  ring

end InvariantIsing

end

end OAI
