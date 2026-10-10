import OAI.NumberTheory.CubicGram.MellinNorm
import OAI.NumberTheory.CubicMoment.Estimates.FullStructuredMeanValue

namespace OAI

/-! Exact conversion of the existing Poisson/Mellin kernel's Fourier
frequency to the norm heights used by the proved structured moments. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma gramMellinPhase_eq_mellinPhase (t x : ℝ) :
    gramMellinPhase t x = mellinPhase (2*Real.pi*t) x := by
  rw [gramMellinPhase,Real.fourierChar_apply]
  unfold mellinPhase
  congr 1
  push_cast
  ring

lemma mellinPhase_add_height (u v x : ℝ) :
    mellinPhase (u+v) x = mellinPhase u x*mellinPhase v x := by
  unfold mellinPhase
  rw [show (((u+v)*Real.log x:ℝ):ℂ)*Complex.I =
    ((u*Real.log x:ℝ):ℂ)*Complex.I+((v*Real.log x:ℝ):ℂ)*Complex.I by push_cast; ring,
    Complex.exp_add]

lemma gramMellinPhase_ratio (t : ℝ) {x N : ℝ} (hx : 0 < x) (hN : 0 < N) :
    gramMellinPhase t (x/N) =
      mellinPhase (2*Real.pi*t) x*mellinPhase (-(2*Real.pi*t)) N := by
  rw [gramMellinPhase_eq_mellinPhase]
  unfold mellinPhase
  rw [Real.log_div hx.ne' hN.ne']
  rw [show (((2*Real.pi*t)*(Real.log x-Real.log N):ℝ):ℂ)*Complex.I =
    (((2*Real.pi*t)*Real.log x:ℝ):ℂ)*Complex.I+
      ((-(2*Real.pi*t)*Real.log N:ℝ):ℂ)*Complex.I by push_cast; ring,
    Complex.exp_add]

lemma fullStructuredPrimeSum_gram_twist {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ℝ) (h v e : Eisenstein) (u t : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    {N : ℝ} (hN : 0 < N) :
    (∑ b ∈ (orderedConvolutionSupport (fullPrimeSupport R W X)).filter (fun b => IsCoprime b e),
      fullPrimeCoefficient R W X b*mellinPhase u (norm b)*cubicSymbol b (v*h)*
        gramMellinPhase t (norm b/N)) =
      mellinPhase (-(2*Real.pi*t)) N*fullStructuredPrimeSum R h 1 v e (u+2*Real.pi*t) W X := by
  classical
  unfold fullStructuredPrimeSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hbp := orderedPrimarySupport_primary (fullPrimeSupport R W X)
    (fun i p hp => (fullPrimeSupport_prime R W X i p hp).1) (Finset.mem_filter.mp hb).1
  rw [gramMellinPhase_ratio t (zero_lt_one.trans_le (one_le_norm (primary_ne_zero hbp))) hN,
    mellinPhase_add_height]
  simp only [one_pow,mul_one]
  ring

end CubicFirstMoment

end

end OAI
