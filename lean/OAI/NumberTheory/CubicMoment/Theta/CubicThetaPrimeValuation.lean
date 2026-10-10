import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFrequencyDirichlet

namespace OAI

/-! Unique separation of an unramified prime power in an actual admissible
Eisenstein denominator. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

abbrev CubicThetaDenominator := {c : Eisenstein // (3:Eisenstein) ∣ c ∧ c≠0}
abbrev CubicThetaPrimeFreeDenominator (p : Eisenstein) :=
  {c : Eisenstein // (3:Eisenstein) ∣ c ∧ c≠0 ∧ ¬p ∣ c}

lemma cubicThetaPrimePower_unique {p c d : Eisenstein} (hp : p≠0)
    (hc : ¬p ∣ c) (hd : ¬p ∣ d) {n m : ℕ} (he : p^n*c=p^m*d) : n=m ∧ c=d := by
  have hle {n m : ℕ} {c d : Eisenstein} (hc : ¬p ∣ c)
      (he : p^n*c=p^m*d) (hnm : n ≤ m) : n=m ∧ c=d := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hnm
    have hcd : c=p^k*d := by
      apply mul_left_cancel₀ (pow_ne_zero n hp)
      rw [← mul_assoc,← pow_add]
      exact he
    have hk : k=0 := by
      by_contra hk
      apply hc
      rw [hcd]
      exact dvd_mul_of_dvd_left (dvd_pow_self p hk) d
    subst k
    exact ⟨by omega,by simpa using hcd⟩
  rcases le_total n m with hnm | hmn
  · exact hle hc he hnm
  · obtain ⟨hn,hcd⟩ := hle hd he.symm hmn
    exact ⟨hn.symm,hcd.symm⟩

def cubicThetaPrimePowerDenominator (p : Eisenstein) (hp : primaryPrime p)
    (v : ℕ × CubicThetaPrimeFreeDenominator p) : CubicThetaDenominator :=
  ⟨p^v.1*v.2.val,dvd_mul_of_dvd_right v.2.property.1 _,
    mul_ne_zero (pow_ne_zero _ hp.2.ne_zero) v.2.property.2.1⟩

theorem cubicThetaPrimePowerDenominator_bijective {p : Eisenstein} (hp : primaryPrime p) :
    Function.Bijective (cubicThetaPrimePowerDenominator p hp) := by
  constructor
  · intro v w he
    have hv := congrArg Subtype.val he
    obtain ⟨hn,hc⟩ := cubicThetaPrimePower_unique hp.2.ne_zero v.2.property.2.2 w.2.property.2.2 hv
    exact Prod.ext hn (Subtype.ext hc)
  · intro c
    obtain ⟨n,d,hpd,he⟩ := WfDvdMonoid.max_power_factor c.property.2 hp.2.irreducible
    have hd0 : d≠0 := (mul_ne_zero_iff.mp (he ▸ c.property.2)).2
    have h3p : IsCoprime (3:Eisenstein) p :=
      isCoprime_of_residue_isUnit (unit_residue_of_dvd_primary hp.1 (dvd_refl p))
    have h3d : (3:Eisenstein) ∣ d := (h3p.pow_right).dvd_of_dvd_mul_left (he ▸ c.property.1)
    refine ⟨(n,⟨d,h3d,hd0,hpd⟩),?_⟩
    exact Subtype.ext he.symm

def cubicThetaPrimePowerDenominatorEquiv (p : Eisenstein) (hp : primaryPrime p) :
    (ℕ × CubicThetaPrimeFreeDenominator p) ≃ CubicThetaDenominator :=
  Equiv.ofBijective _ (cubicThetaPrimePowerDenominator_bijective hp)

end CubicFirstMoment

end

end OAI
