import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeHeckeContinuation

namespace OAI

/-! Exact normalization of the unramified three-frequency relation at
the theta pole. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeFactor_pole {p : Eisenstein} (hp : primaryPrime p) :
    (norm p:ℂ)^3*((norm p:ℂ)^(-(4/3:ℂ)))^3=(norm p:ℂ)⁻¹ := by
  have hq : (norm p:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_pos_of_ne_zero hp.2.ne_zero).ne'
  rw [← Complex.cpow_mul_nat]
  norm_num only [show (-(4/3:ℂ))*(3:ℕ)=-(4:ℂ) by norm_num]
  rw [Complex.cpow_neg,show (4:ℂ)=((4:ℕ):ℂ) by rfl,Complex.cpow_natCast]
  field_simp

lemma cubicThetaPrimeFirstFactor_pole {p : Eisenstein} (hp : primaryPrime p) (h : Eisenstein) :
    cubicThetaPrimeFirstFactor p (4/3) h=
      star (cubicSymbol p h)*gauss p*(norm p:ℂ)^(-(5/6:ℂ)) := by
  have hq : (norm p:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_pos_of_ne_zero hp.2.ne_zero).ne'
  have hsqrt : (Real.sqrt (norm p):ℂ)=(norm p:ℂ)^(1/2:ℂ) := by
    rw [show (1/2:ℂ)=((1/2:ℝ):ℂ) by norm_num,← Complex.ofReal_cpow (norm_nonneg p)]
    congr 1
    exact Real.sqrt_eq_rpow _
  unfold cubicThetaPrimeFirstFactor
  rw [hsqrt]
  calc
    _ = star (cubicSymbol p h)*gauss p*
        ((norm p:ℂ)^(1/2:ℂ)*(norm p:ℂ)^(-(4/3:ℂ))) := by ring
    _ = _ := by rw [← Complex.cpow_add _ _ hq]; congr 1; norm_num

theorem cubicThetaArithmeticFourierResidue_primeHecke_explicit {p : Eisenstein}
    (hp : primaryPrime p) (h : Eisenstein) (hh : ¬p ∣ h) :
    cubicThetaArithmeticFourierResidue (p^3*h) (4/3)=
      (1+(norm p:ℂ)⁻¹)*cubicThetaArithmeticFourierResidue h (4/3)-
      (star (cubicSymbol p h)*gauss p*(norm p:ℂ)^(-(5/6:ℂ)))*
        cubicThetaArithmeticFourierResidue (p*h) (4/3) := by
  rw [cubicThetaArithmeticFourierResidue_primeHecke hp h hh,
    cubicThetaPrimeCubeFactor_pole hp,cubicThetaPrimeFirstFactor_pole hp]

end CubicFirstMoment

end

end OAI
