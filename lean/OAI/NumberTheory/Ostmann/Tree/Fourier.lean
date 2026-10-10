import Mathlib

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]

def mean (f : ZMod p → ℂ) : ℂ := (p : ℂ)⁻¹ * ∑ x, f x

def fourier (f : ZMod p → ℂ) (a : ZMod p) : ℂ :=
  (p : ℂ)⁻¹ * ZMod.dft f a

def l2Sq (f : ZMod p → ℂ) : ℝ := (p : ℝ)⁻¹ * ∑ x, ‖f x‖ ^ 2

noncomputable instance characterFintype : Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

def mixedCorrelation (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (a : ZMod p) : ℂ :=
  mean (fun x => g x * χ x * ZMod.stdAddChar (a * x))

def correlationBound (g : ZMod p → ℂ) : NNReal :=
  Finset.univ.sup (fun z : MulChar (ZMod p) ℂ × ZMod p => ‖mixedCorrelation g z.1 z.2‖₊)

@[simp] theorem fourier_zero (f : ZMod p → ℂ) : fourier f 0 = mean f := by
  simp only [fourier, ZMod.dft_apply_zero, mean]

theorem fourier_apply (f : ZMod p → ℂ) (a : ZMod p) :
    fourier f a = (p : ℂ)⁻¹ * ∑ x, f x * ZMod.stdAddChar (-(a*x)) := by
  simp only [fourier, ZMod.dft_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [mul_comm x a, mul_comm]

theorem mixedCorrelation_eq_fourier (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ)
    (a : ZMod p) : mixedCorrelation g χ a = fourier (fun x => g x * χ x) (-a) := by
  simp only [mixedCorrelation, mean, fourier_apply, neg_mul, neg_neg]

theorem norm_mixedCorrelation_le (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ)
    (a : ZMod p) : ‖mixedCorrelation g χ a‖ ≤ (correlationBound g : ℝ) := by
  exact_mod_cast (Finset.le_sup (s := Finset.univ)
    (f := fun z : MulChar (ZMod p) ℂ × ZMod p => ‖mixedCorrelation g z.1 z.2‖₊)
    (Finset.mem_univ (χ,a)))

theorem l2Sq_nonneg (f : ZMod p → ℂ) : 0 ≤ l2Sq f := by
  unfold l2Sq
  positivity

theorem fourier_inversion (f : ZMod p → ℂ) (x : ZMod p) :
    f x = ∑ a, fourier f a * ZMod.stdAddChar (a*x) := by
  have h := congrFun (ZMod.dft.symm_apply_apply f) x
  rw [ZMod.invDFT_apply] at h
  change (p : ℂ)⁻¹ * (∑ a, ZMod.stdAddChar (a*x) * ZMod.dft f a) = f x at h
  rw [← h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  dsimp [fourier]
  ring

end
end Ostmann.FiniteField

end OAI
