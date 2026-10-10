import OAI.NumberTheory.Ostmann.Supply.FourierKernelBounds

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]

theorem fourierKernel_conj (E : Finset (ZMod p)) (x : ZMod p) :
    conj (fourierKernel E x) = fourierKernel E (-x) := by
  simp only [fourierKernel, map_mul, map_inv₀, map_natCast, map_sum,
    conj_stdAddChar, mul_neg]

theorem fourierKernel_neg (E : Finset (ZMod p))
    (hE : ∀ h : ZMod p, -h ∈ E ↔ h ∈ E) (x : ZMod p) :
    fourierKernel E (-x) = fourierKernel E x := by
  unfold fourierKernel
  congr 1
  apply Finset.sum_bij (fun h _ => -h)
  · intro h hh
    exact (hE h).mpr hh
  · intro a ha b hb hab
    exact neg_injective hab
  · intro h hh
    exact ⟨-h,(hE h).mpr hh,neg_neg h⟩
  · intro h hh
    rw [mul_neg, neg_mul]

theorem fourierKernel_real (E : Finset (ZMod p))
    (hE : ∀ h : ZMod p, -h ∈ E ↔ h ∈ E) (x : ZMod p) :
    (fourierKernel E x).im = 0 := by
  have hc := (fourierKernel_conj E x).trans (fourierKernel_neg E hE x)
  have hi := congrArg Complex.im hc
  simp only [Complex.conj_im] at hi
  linarith

def localKernel (S : Finset (ZMod p)) (t : ℝ) (x : ZMod p) : ℝ :=
  t*(fourierKernel (largeSpectrum S) x).re

theorem localKernel_cast (S : Finset (ZMod p)) (t : ℝ) (x : ZMod p) :
    (localKernel S t x : ℂ) = (t:ℂ)*fourierKernel (largeSpectrum S) x := by
  have hi := fourierKernel_real (largeSpectrum S) (neg_mem_largeSpectrum S) x
  apply Complex.ext <;> simp [localKernel,hi]

theorem localKernel_norm_le (S : Finset (ZMod p)) (t : ℝ) (x : ZMod p) :
    |localKernel S t x| ≤ |t| * ((largeSpectrum S).card:ℝ)/p := by
  have h := fourierKernel_norm_le (largeSpectrum S) x
  have hc : |localKernel S t x| = |t| * ‖fourierKernel (largeSpectrum S) x‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, localKernel_cast, norm_mul]
    simp
  rw [hc, div_eq_mul_inv, mul_assoc]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg t)

end Ostmann.Supply

end

end OAI
