import OAI.NumberTheory.Ostmann.Supply.KernelSymmetry
import OAI.NumberTheory.Ostmann.Supply.ResidueKernel

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]

theorem fourierKernel_zero (E : Finset (ZMod p)) :
    fourierKernel E 0 = (E.card : ℂ)/p := by
  simp [fourierKernel,div_eq_mul_inv,mul_comm]

theorem fourierKernel_sum (E : Finset (ZMod p)) (hE : 0 ∉ E) :
    ∑ x, fourierKernel E x = 0 := by
  simp only [fourierKernel, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  have hz (h : ZMod p) (hh : h∈E) : ∑ x : ZMod p, ZMod.stdAddChar (h*x) = 0 := by
    have hh0 : h≠0 := by rintro rfl; exact hE hh
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p hh0)
  simp only [Finset.sum_eq_zero hz, mul_zero]

theorem localKernel_zero (S : Finset (ZMod p)) (t : ℝ) :
    localKernel S t 0 = t*((largeSpectrum S).card:ℝ)/p := by
  simp [localKernel, fourierKernel_zero, mul_div_assoc]

theorem localKernel_sum (S : Finset (ZMod p)) (t : ℝ) :
    ∑ x, localKernel S t x = 0 := by
  simp only [localKernel, ← Finset.mul_sum, ← Complex.re_sum,
    fourierKernel_sum _ (zero_not_mem_largeSpectrum S), Complex.zero_re, mul_zero]

theorem localKernel_sum_sq (S : Finset (ZMod p)) (t : ℝ) :
    ∑ x, (localKernel S t x)^2 = t^2*((largeSpectrum S).card:ℝ)/p := by
  have he (x : ZMod p) : (localKernel S t x)^2 =
      t^2*‖fourierKernel (largeSpectrum S) x‖^2 := by
    have hh := congrArg (fun z : ℂ => ‖z‖^2) (localKernel_cast S t x)
    simpa only [Complex.norm_real, Real.norm_eq_abs, norm_mul, mul_pow, sq_abs] using hh
  simp_rw [he]
  rw [← Finset.mul_sum, fourierKernel_energy]
  ring

theorem localKernel_nonzero_sum (S : Finset (ZMod p)) (t : ℝ) :
    ∑ x ∈ Finset.univ.erase 0, localKernel S t x =
      -(t*((largeSpectrum S).card:ℝ)/p) := by
  have h := Finset.sum_erase_add Finset.univ (localKernel S t) (Finset.mem_univ 0)
  rw [localKernel_sum,localKernel_zero] at h
  linarith

theorem localKernel_nonzero_sum_sq (S : Finset (ZMod p)) (t : ℝ) :
    ∑ x ∈ Finset.univ.erase 0, (localKernel S t x)^2 =
      t^2*(((largeSpectrum S).card:ℝ)/p-(((largeSpectrum S).card:ℝ)/p)^2) := by
  have h := Finset.sum_erase_add Finset.univ
    (fun x => (localKernel S t x)^2) (Finset.mem_univ 0)
  rw [localKernel_sum_sq,localKernel_zero] at h
  calc
    _ = t^2*((largeSpectrum S).card:ℝ)/p-(t*((largeSpectrum S).card:ℝ)/p)^2 := by linarith
    _ = _ := by ring

end Ostmann.Supply

end

end OAI
