import OAI.NumberTheory.CubicMoment.Estimates.DivisorFrequency
import OAI.NumberTheory.CubicMoment.Estimates.FinitePoissonRadial

namespace OAI

/-! Exact reindexing by the effective frequency d*h for a square-divisor
Poisson block. The additive phase uses the actual inverse on the image. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def divisorFourierPhase (d h : Eisenstein) : ℂ :=
  (Real.fourierChar (tracePair (((Function.invFun (fun h : Eisenstein => d*h) h):Eisenstein):ℂ)
    (1/(3*traceLambda))):ℂ)

@[simp] lemma norm_divisorFourierPhase (d h : Eisenstein) : ‖divisorFourierPhase d h‖ = 1 := by
  simp [divisorFourierPhase]

lemma divisorFourierPhase_mul {d : Eisenstein} (hd : d ≠ 0) (h : Eisenstein) :
    divisorFourierPhase d (d*h) = (Real.fourierChar (tracePair (h:ℂ) (1/(3*traceLambda))):ℂ) := by
  unfold divisorFourierPhase
  rw [Function.leftInverse_invFun (fun a b he => mul_left_cancel₀ hd he)]

def finiteDivisorPoissonContribution (d : Eisenstein) (S H : Finset Eisenstein)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑ h ∈ H, ∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then
    (β a*normTwist u a)*star (β b*normTwist u b)*
      ((A/(norm d)^2)/(9*Real.sqrt (norm (b*a))):ℝ)*
      (mixedSymbol b a (d^2)*gramDualTerm b a W (A/(norm d)^2) h) else 0

theorem finiteDivisorPoissonContribution_radial {d : Eisenstein} (hd : d ≠ 0)
    (S H : Finset Eisenstein) (hS : ∀ a ∈ S, primary a)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ)
    {A L J : ℝ} (hA : 0 ≤ A) (hL : 0 < L) (hJ : 0 < J) :
    finiteDivisorPoissonContribution d S H β u W A =
      (A/(9*(norm d)^2*L):ℝ)*normCoprimeRadialForm S (H.image (fun h => d*h))
        (fun a => star (β a*mellinPhase u (norm a)))
        (fun a => star (β a*mellinPhase u (norm a)))
        (divisorFourierPhase d) (fun h => norm h/J) (fun a => norm a/L) W
        (A*J/(27*(norm d)^3*L^2)) := by
  unfold finiteDivisorPoissonContribution normCoprimeRadialForm
  rw [Finset.sum_image (fun a _ b _ he => mul_left_cancel₀ hd he)]
  simp only [Finset.mul_sum,divisorFourierPhase_mul hd]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hc : IsCoprime b a ↔ IsCoprime a b := isCoprime_comm
  simp only [hc]
  split_ifs with hab
  · rw [divisor_gram_radial (hS b hb) (hS a ha) hd W hA]
    have harg : A*J/(27*(norm d)^3*L^2)*(norm (d*h)/J)/((norm a/L)*(norm b/L)) =
        A*norm (d*h)/(27*(norm d)^3*norm (a*b)) := by
      simp only [norm_mul_eq]
      field_simp
    rw [harg,poisson_scaled_sqrt hL a b]
    simp only [star_mul,star_star,normTwist_eq_mellinPhase,Complex.ofReal_div,
      Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat]
    have hs : (Real.sqrt (norm (b*a)):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (norm_pos_of_ne_zero (mul_ne_zero (primary_ne_zero (hS b hb))
        (primary_ne_zero (hS a ha))))).ne'
    have hl : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
    have hd' : (norm d:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hd).ne'
    rw [mul_comm b a]
    field_simp
  · simp

end CubicFirstMoment

end

end OAI
