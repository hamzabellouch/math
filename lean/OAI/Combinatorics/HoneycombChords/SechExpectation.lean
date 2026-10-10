import OAI.Combinatorics.HoneycombChords.SechTransform

namespace OAI

/-! Normalized expectation for the hyperbolic secant measure. -/

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real Filter Topology MeasureTheory Analytic

/-- The probability average under dp/cosh(cp), pushed forward by p ↦ p².
The transform below also proves its normalization. -/
noncomputable def sechExpectation (c : ℝ) (H : ℝ → ℝ) : ℝ :=
  (2*c/Real.pi)*(∫ p in Set.Ioi (0:ℝ),H (p^2)/Real.cosh (c*p))
lemma sechExpectation_one {c : ℝ} (hc : 0 < c) : sechExpectation c (fun _=>1)=1 := by
  unfold sechExpectation
  have h:=sech_kernel_integral hc (m:=0) (by simpa using hc)
  simp only [zero_mul,Real.cosh_zero,Real.cos_zero,div_one,mul_zero,zero_div] at h
  rw [h]
  field_simp

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end OAI
