import OAI.NumberTheory.CubicMoment.Estimates.NormCoprimeMellin
import OAI.NumberTheory.CubicMoment.Estimates.DispersionPoisson
import OAI.NumberTheory.CubicMoment.Estimates.MellinWeights

namespace OAI

/-! Exact identification of a finite Poisson frequency block with the
radial form used in the Mellin estimates, including its scalar. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def finitePoissonContribution (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑ h ∈ H, ∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then
    (β a*normTwist u a)*star (β b*normTwist u b)*
      (A/(9*Real.sqrt (norm (b*a))):ℝ)*gramDualTerm b a W A h else 0

lemma poisson_scaled_sqrt {L : ℝ} (hL : 0 < L) (a b : Eisenstein) :
    Real.sqrt ((norm a/L)*(norm b/L)) = Real.sqrt (norm (b*a))/L := by
  have he : (norm a/L)*(norm b/L) = norm (b*a)/L^2 := by
    rw [norm_mul_eq]
    ring
  rw [he,Real.sqrt_div (norm_nonneg _),Real.sqrt_sq hL.le]

theorem finitePoissonContribution_radial (S H : Finset Eisenstein)
    (hS : ∀ a ∈ S, a ≠ 0) (β : Eisenstein → ℂ) (u : ℝ)
    (W : ℝ → ℂ) {A L J : ℝ} (hA : 0 ≤ A) (hL : 0 < L) (hJ : 0 < J) :
    finitePoissonContribution S H β u W A =
      (A/(9*L):ℝ)*normCoprimeRadialForm S H
        (fun a => star (β a*mellinPhase u (norm a)))
        (fun a => star (β a*mellinPhase u (norm a)))
        (fun h => (Real.fourierChar (tracePair (h:ℂ) (1/(3*traceLambda))):ℂ))
        (fun h => norm h/J) (fun a => norm a/L) W (A*J/(27*L^2)) := by
  unfold finitePoissonContribution normCoprimeRadialForm
  simp only [Finset.mul_sum]
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
  · rw [gramDualTerm_radial a b W hA h]
    have harg : A*J/(27*L^2)*(norm h/J)/((norm a/L)*(norm b/L)) =
        A*norm h/(27*norm (a*b)) := by
      rw [norm_mul_eq]
      field_simp
    rw [harg,poisson_scaled_sqrt hL a b]
    simp only [star_mul,star_star,normTwist_eq_mellinPhase,Complex.ofReal_div,
      Complex.ofReal_mul,Complex.ofReal_ofNat]
    have hs : (Real.sqrt (norm (b*a)):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (norm_pos_of_ne_zero (mul_ne_zero (hS b hb) (hS a ha)))).ne'
    have hl : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
    rw [mul_comm b a]
    field_simp
  · simp

end CubicFirstMoment

end

end OAI
