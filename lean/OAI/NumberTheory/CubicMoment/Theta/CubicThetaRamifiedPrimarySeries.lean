import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedPrimaryFactor

namespace OAI

/-! The finite ramified factors separated from the remaining primary
Fourier series. These are identities for the actual convergent Dirichlet
sum, with no residue formula assumed. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaPrimaryFourierTerm (e : Eisensteinˣ) (n : ℕ) (s : ℂ)
    (h : Eisenstein) (a : CubicThetaPrimaryPart) : ℂ :=
  (cubicSymbol a.val (e:Eisenstein)*(cubicSymbol a.val lambdaE)^n)^2*
    cubicThetaSymbolFourier a.val (primary_ne_zero a.property) h*(norm a.val:ℂ)^(-s)

def cubicThetaPrimaryFourierSeries (e : Eisensteinˣ) (n : ℕ) (s : ℂ)
    (h : Eisenstein) : ℂ := ∑' a : CubicThetaPrimaryPart, cubicThetaPrimaryFourierTerm e n s h a

def cubicThetaRamifiedFactor (e : Eisensteinˣ) (n : ℕ) (s : ℂ) (h : Eisenstein) : ℂ :=
  cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^(n+2)) h*
    (norm ((e:Eisenstein)*lambdaE^(n+2)):ℂ)^(-s)

theorem cubicThetaRamifiedTerm_factor (e : Eisensteinˣ) (n : ℕ) (s : ℂ)
    (h : Eisenstein) (a : CubicThetaPrimaryPart) :
    cubicThetaRamifiedTerm s h (e,n,a)=
      cubicThetaRamifiedFactor e n s h*cubicThetaPrimaryFourierTerm e n s h a := by
  change cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^(n+2)*a.val) h*
    (norm ((e:Eisenstein)*lambdaE^(n+2)*a.val):ℂ)^(-s)=_
  rw [cubicThetaEisensteinGaussCoefficient_ramified_primary e a.property,
    norm_mul_eq,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
  unfold cubicThetaRamifiedFactor cubicThetaPrimaryFourierTerm
  ring

theorem cubicThetaFrequencyDirichlet_primary_finite {s : ℂ} (hs : 2<s.re)
    (h : Eisenstein) (M : ℕ) (hM : ∀ n : ℕ, M ≤ n → ¬lambdaE^n ∣ h) :
    cubicThetaFrequencyDirichlet h s=
      ∑' e : Eisensteinˣ, ∑ n ∈ Finset.range M,
        cubicThetaRamifiedFactor e n s h*cubicThetaPrimaryFourierSeries e n s h := by
  rw [cubicThetaFrequencyDirichlet_ramified_finite hs h M hM]
  apply tsum_congr
  intro e
  apply Finset.sum_congr rfl
  intro n _
  simp_rw [cubicThetaRamifiedTerm_factor]
  rw [tsum_mul_left]
  rfl

end CubicFirstMoment

end

end OAI
