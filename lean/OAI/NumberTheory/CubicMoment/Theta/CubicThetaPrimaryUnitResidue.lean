import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedPrimaryResidue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedContraction

namespace OAI

/-! The base residue on the six-unit orbit of a primary frequency is
supported precisely on the two signed primary representatives. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaPrimary_mul_unit_iff {h : Eisenstein} (hh : primary h)
    (e : Eisensteinˣ) : primary (h*(e:Eisenstein)) ↔ e=1 := by
  constructor
  · intro hp
    have h3 : (3:Eisenstein)∣(e:Eisenstein)-1 := by
      convert dvd_sub hp (dvd_mul_of_dvd_left hh (e:Eisenstein)) using 1
      ring
    exact Units.ext (primary_unit_eq_one e.isUnit h3)
  · rintro rfl
    simpa using hh

theorem cubicThetaArithmeticFourierResidue_primary_unit {h : Eisenstein}
    (hh : primary h) (e : Eisensteinˣ) :
    cubicThetaArithmeticFourierResidue (h*(e:Eisenstein)) (4/3)=
      if e=1 ∨ e=-1 then cubicThetaArithmeticFourierResidue h (4/3) else 0 := by
  by_cases he : e=1 ∨ e=-1
  · rw [ite_eq_left he]
    rcases he with he | he
    · subst e
      simp
    · subst e
      simpa using cubicThetaArithmeticFourierResidue_neg (primary_ne_zero hh)
  · rw [ite_eq_right he]
    have hn : ¬lambdaE∣h*(e:Eisenstein) := by
      intro hd
      rcases lambdaE_prime.dvd_mul.mp hd with hd | hd
      · exact lambdaE_prime.not_isUnit ((primary_coprime_lambda hh).isRelPrime hd dvd_rfl)
      · exact lambdaE_prime.not_isUnit (isUnit_of_dvd_unit hd e.isUnit)
    apply cubicThetaArithmeticFourierResidue_primary_support hn
    · intro hp
      exact he (Or.inl ((cubicThetaPrimary_mul_unit_iff hh e).mp hp))
    · intro hp
      have hneg : primary (h*((-e:Eisensteinˣ):Eisenstein)) := by simpa using hp
      have hu := (cubicThetaPrimary_mul_unit_iff hh (-e)).mp hneg
      exact he (Or.inr (neg_eq_iff_eq_neg.mp hu))

end CubicFirstMoment

end

end OAI
