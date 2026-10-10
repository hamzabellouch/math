import Mathlib.Analysis.Fourier.AddCircle

namespace OAI

noncomputable section

namespace Invariant233.Fejer

abbrev Circle := AddCircle (1 : ℝ)

def geometricPolynomial (H : ℕ) (x : Circle) : ℂ :=
  ∑ k ∈ Finset.range H, fourier (k : ℤ) x

def kernel (H : ℕ) (x : Circle) : ℝ :=
  Complex.normSq (geometricPolynomial H x) / H

def frequencies (H : ℕ) : Finset ℤ := Finset.Ioo (-(H : ℤ)) (H : ℤ)

def coefficient (H : ℕ) (n : ℤ) : ℂ :=
  fourierCoeff (fun x : Circle => (kernel H x : ℂ)) n

end Invariant233.Fejer

end

end OAI
