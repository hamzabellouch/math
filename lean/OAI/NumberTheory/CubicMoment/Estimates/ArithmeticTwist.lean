import OAI.NumberTheory.CubicMoment.Estimates.ShortMoebiusProducts
import OAI.NumberTheory.CubicMoment.Estimates.ResidueIdealCharacters
import OAI.NumberTheory.CubicMoment.Estimates.RamifiedIdealParts

namespace OAI

/-! Twisting actual ideal arithmetic functions by a residue character and
norm phase commutes with convolution. Different original factors may
therefore retain different Mellin heights throughout short inversion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def residueNormTwist (q : Eisenstein) (η : MulChar (Residues q) ℂ) (t : ℝ)
    (ν : EisensteinIdealExponent) : ℂ :=
  residueIdealChar q η ν*mellinPhase t (idealExponentNorm ν)

lemma residueNormTwist_add (q : Eisenstein) (η : MulChar (Residues q) ℂ) (t : ℝ)
    (ν κ : EisensteinIdealExponent) :
    residueNormTwist q η t (ν+κ) = residueNormTwist q η t ν*residueNormTwist q η t κ := by
  rw [residueNormTwist,residueIdealChar_add,idealExponentNorm_add,
    mellinPhase_mul_pos t (idealExponentNorm_pos ν) (idealExponentNorm_pos κ)]
  unfold residueNormTwist
  ring

def twistArithmetic (q : Eisenstein) (η : MulChar (Residues q) ℂ) (t : ℝ)
    (A : EisensteinArithmeticFunction) : MvPowerSeries EisensteinIdealPrime ℂ :=
  fun ν => ((MvPowerSeries.coeff ν A:ℝ):ℂ)*residueNormTwist q η t ν

lemma twistArithmetic_mul (q : Eisenstein) (η : MulChar (Residues q) ℂ) (t : ℝ)
    (A B : EisensteinArithmeticFunction) :
    twistArithmetic q η t (A*B) = twistArithmetic q η t A*twistArithmetic q η t B := by
  apply MvPowerSeries.ext
  intro ν
  change ((MvPowerSeries.coeff ν (A*B):ℝ):ℂ)*residueNormTwist q η t ν = _
  rw [MvPowerSeries.coeff_mul,Complex.ofReal_sum,Finset.sum_mul,MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  change ((MvPowerSeries.coeff p.1 A*MvPowerSeries.coeff p.2 B:ℝ):ℂ)*
      residueNormTwist q η t ν = _
  rw [← he,residueNormTwist_add,Complex.ofReal_mul]
  change _ = (((MvPowerSeries.coeff p.1 A:ℝ):ℂ)*residueNormTwist q η t p.1)*
    (((MvPowerSeries.coeff p.2 B:ℝ):ℂ)*residueNormTwist q η t p.2)
  ring

lemma twistArithmetic_add (q : Eisenstein) (η : MulChar (Residues q) ℂ) (t : ℝ)
    (A B : EisensteinArithmeticFunction) :
    twistArithmetic q η t (A+B) = twistArithmetic q η t A+twistArithmetic q η t B := by
  ext ν
  change ((MvPowerSeries.coeff ν (A+B):ℝ):ℂ)*residueNormTwist q η t ν =
    ((MvPowerSeries.coeff ν A:ℝ):ℂ)*residueNormTwist q η t ν +
      ((MvPowerSeries.coeff ν B:ℝ):ℂ)*residueNormTwist q η t ν
  rw [map_add,Complex.ofReal_add,add_mul]

lemma twistArithmetic_sub (q : Eisenstein) (η : MulChar (Residues q) ℂ) (t : ℝ)
    (A B : EisensteinArithmeticFunction) :
    twistArithmetic q η t (A-B) = twistArithmetic q η t A-twistArithmetic q η t B := by
  ext ν
  change ((MvPowerSeries.coeff ν (A-B):ℝ):ℂ)*residueNormTwist q η t ν =
    ((MvPowerSeries.coeff ν A:ℝ):ℂ)*residueNormTwist q η t ν -
      ((MvPowerSeries.coeff ν B:ℝ):ℂ)*residueNormTwist q η t ν
  rw [map_sub,Complex.ofReal_sub,sub_mul]

lemma twistArithmetic_coeff_primary (q : Eisenstein) (η : MulChar (Residues q) ℂ)
    (hu : ∀ e : Eisensteinˣ, η (Ideal.Quotient.mk (modulus q) e) = 1)
    (t : ℝ) (A : EisensteinArithmeticFunction) {n : Eisenstein} (hn : primary n) :
    MvPowerSeries.coeff (idealExponentOf n) (twistArithmetic q η t A) =
      ((MvPowerSeries.coeff (idealExponentOf n) A:ℝ):ℂ)*
        η (Ideal.Quotient.mk (modulus q) n)*mellinPhase t (norm n) := by
  change ((MvPowerSeries.coeff (idealExponentOf n) A:ℝ):ℂ)*
    (residueIdealChar q η (idealExponentOf n)*mellinPhase t (idealExponentNorm (idealExponentOf n))) = _
  rw [residueIdealChar_primaryNormalize η hu,idealPrimaryGenerator_at_element hn,
    idealExponentOf_norm (primary_ne_zero hn)]
  ring

end CubicFirstMoment

end

end OAI
