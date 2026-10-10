import OAI.NumberTheory.CubicMoment.Estimates.CubicSupplementaryPeriodicityProof
import OAI.NumberTheory.CubicMoment.Estimates.PrimaryPrimePNTProofSplitting

namespace OAI

/-! Two exact cubic-symbol values detect the unit and ramified factors.
Their values are computed from the finite Euler definition. -/
noncomputable section
namespace CubicFirstMoment

lemma primary_neg_two : primary (-2:Eisenstein) := ⟨-1,by ring⟩

lemma normNat_neg_two : normNat (-2:Eisenstein)=4 := by
  apply Nat.cast_injective (R := ℝ)
  rw [normNat_cast]
  change Complex.normSq (-2:ℂ) = (4:ℝ)
  norm_num

lemma cubicSymbol_neg_two_omega : cubicSymbol (-2:Eisenstein) omegaE = omega := by
  rw [cubicSymbol_omega_norm primary_neg_two,normNat_neg_two]
  norm_num

lemma cubicSymbol_neg_two_lambda : cubicSymbol (-2:Eisenstein) lambdaE = 1 := by
  have he : (-2:Eisenstein) ∣ lambdaE-1 := ⟨-omegaE,by dsimp [lambdaE]; ring⟩
  rw [cubicSymbol_congr (residue_eq_of_dvd_sub he)]
  simpa using (cubicSymbol_pow_upper primary_neg_two (1:Eisenstein) 0)

lemma primary_seven_factor : primary (1+3*omegaE) := ⟨omegaE,by ring⟩

lemma normNat_seven_factor : normNat (1+3*omegaE)=7 := by
  apply Nat.cast_injective (R := ℝ)
  rw [normNat_cast]
  change Complex.normSq ((1:ℂ)+3*omega) = (7:ℝ)
  have h := coordinates_norm 1 3
  norm_num at h
  exact h

lemma primaryPrime_seven_factor : primaryPrime (1+3*omegaE) :=
  ⟨primary_seven_factor,prime_of_normNat_prime (by rw [normNat_seven_factor]; norm_num)⟩

lemma cubicSymbol_seven_factor_lambda : cubicSymbol (1+3*omegaE) lambdaE = omega^2 := by
  rw [cubicSymbol_prime primaryPrime_seven_factor]
  apply cubicSymbol_euler_value primaryPrime_seven_factor
    (residue_isUnit_of_isCoprime (primary_coprime_lambda primary_seven_factor)) (2:Fin 3)
  rw [normNat_seven_factor]
  norm_num only
  apply residue_eq_of_dvd_sub
  refine ⟨1+omegaE,?_⟩
  dsimp [lambdaE]
  ring

lemma cubicSymbol_seven_factor_omega : cubicSymbol (1+3*omegaE) omegaE = omega^2 := by
  rw [cubicSymbol_omega_norm primary_seven_factor,normNat_seven_factor]
  norm_num

end CubicFirstMoment

end

end OAI
