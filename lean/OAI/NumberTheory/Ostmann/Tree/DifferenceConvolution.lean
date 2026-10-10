import OAI.NumberTheory.Ostmann.Tree.AffineFourier
import OAI.NumberTheory.Ostmann.Tree.MellinTransform

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

def differenceConvolution (f h : ZMod p → ℂ) (y : ZMod p) : ℂ :=
  mean (fun d => f d*h (d-y))

theorem fourier_subRight (h : ZMod p → ℂ) (d a : ZMod p) :
    fourier (fun y => h (d-y)) a=ZMod.stdAddChar (-(a*d))*fourier h (-a) := by
  have he : (fun y => h (d-y))=(fun y => (fun x => h (x+d)) ((-1:(ZMod p)ˣ)*y)) := by
    funext y
    congr 1
    simp only [Units.val_neg,Units.val_one]
    ring
  rw [he,fourier_unitMul (fun x => h (x+d)) (-1:(ZMod p)ˣ) a,fourier_translate]
  simp

theorem fourier_differenceConvolution (f h : ZMod p → ℂ) (a : ZMod p) :
    fourier (differenceConvolution f h) a=fourier f a*fourier h (-a) := by
  unfold differenceConvolution mean
  rw [fourier_const_mul,fourier_sum]
  simp_rw [fourier_const_mul,fourier_subRight]
  rw [fourier_apply f a]
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem differenceConvolution_parseval (f h : ZMod p → ℂ) :
    l2Sq (differenceConvolution f h)=
      ∑ a : ZMod p, ‖fourier f a‖^2*‖fourier h (-a)‖^2 := by
  rw [← fourier_parseval]
  simp only [fourier_differenceConvolution,norm_mul,mul_pow]

def doubleMellin (f : (ZMod p)ˣ → (ZMod p)ˣ → ℂ)
    (χ ψ : MulChar (ZMod p) ℂ) : ℂ :=
  mellin (fun t => mellin (fun s => f s t) χ) ψ

theorem doubleMellin_parseval (f : (ZMod p)ˣ → (ZMod p)ˣ → ℂ) :
    (∑ χ : MulChar (ZMod p) ℂ,∑ ψ : MulChar (ZMod p) ℂ, ‖doubleMellin f χ ψ‖^2) =
      (Fintype.card (ZMod p)ˣ:ℝ)⁻¹^2*∑ s : (ZMod p)ˣ,∑ t : (ZMod p)ˣ, ‖f s t‖^2 := by
  simp only [doubleMellin,mellin_parseval]
  rw [← Finset.mul_sum,Finset.sum_comm]
  simp_rw [mellin_parseval]
  rw [← Finset.mul_sum,Finset.sum_comm]
  ring

end
end Ostmann.FiniteField

end OAI
