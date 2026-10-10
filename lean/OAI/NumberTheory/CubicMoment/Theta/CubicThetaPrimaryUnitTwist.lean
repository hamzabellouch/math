import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedResiduePeriodicity

namespace OAI

/-! Absorb the six primary-series unit twists into the actual frequency.
This keeps the ramified residue equations on one finite unit orbit. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimaryFourierSeries_unit (e : Eisensteinˣ) (n : ℕ)
    (s : ℂ) (h : Eisenstein) :
    cubicThetaPrimaryFourierSeries e n s h=
      cubicThetaPrimaryFourierSeries 1 n s (h*(e:Eisenstein)) := by
  unfold cubicThetaPrimaryFourierSeries
  apply tsum_congr
  intro a
  have hcop : IsCoprime a.val (e:Eisenstein) :=
    ⟨0,(e⁻¹:Eisensteinˣ),by simp⟩
  have h1 : cubicSymbol a.val 1=1 := by
    simpa only [pow_zero] using cubicSymbol_pow_upper a.property 1 0
  unfold cubicThetaPrimaryFourierTerm
  rw [cubicThetaSymbolFourier_mul a.property hcop,mul_pow,cubicSymbol_sq_eq_star a.property,
    Units.val_one,h1,one_mul]
  ring

lemma cubicThetaPrimaryFourierSeries_zero_shift (s : ℂ) (h : Eisenstein) :
    cubicThetaPrimaryFourierSeries 1 0 s h=
      cubicThetaPrimaryFourierSeries 1 1 s (lambdaE^2*h) := by
  rw [cubicThetaPrimaryFourierSeries_lambda_pow]
  exact (cubicThetaPrimaryFourierSeries_period 1 0 s h).symm

lemma cubicThetaPrimaryFourierSeries_two_shift (s : ℂ) (h : Eisenstein) :
    cubicThetaPrimaryFourierSeries 1 2 s h=
      cubicThetaPrimaryFourierSeries 1 1 s (lambdaE*h) := by
  simpa only [pow_one] using (cubicThetaPrimaryFourierSeries_lambda_pow 1 1 1 s h).symm

end CubicFirstMoment

end

end OAI
