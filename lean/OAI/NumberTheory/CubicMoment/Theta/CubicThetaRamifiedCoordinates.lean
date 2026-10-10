import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFactorUniqueness
import OAI.NumberTheory.CubicMoment.Estimates.RamifiedPrimaryDecomposition

namespace OAI

/-! Uniqueness of the unit, ramified exponent and primary coordinates
needed to define the cubic theta coefficients without choices of associates. -/
noncomputable section
namespace CubicFirstMoment

lemma primary_lambda_emultiplicity {a : Eisenstein} (ha : primary a) :
    emultiplicity lambdaE a = 0 := by
  apply emultiplicity_eq_zero.mpr
  intro hd
  exact lambdaE_prime.not_isUnit ((primary_coprime_lambda ha).isRelPrime hd dvd_rfl)

lemma unit_lambda_emultiplicity (u : Eisensteinˣ) :
    emultiplicity lambdaE (u:Eisenstein) = 0 := by
  apply emultiplicity_eq_zero.mpr
  intro hd
  exact lambdaE_prime.not_isUnit (isUnit_of_dvd_unit hd u.isUnit)

/-- The published decomposition is unique after imposing primarity. -/
theorem unit_ramified_primary_unique {u u' : Eisensteinˣ} {k k' : ℕ}
    {a a' : Eisenstein} (ha : primary a) (ha' : primary a')
    (he : (u:Eisenstein)*lambdaE^k*a = (u':Eisenstein)*lambdaE^k'*a') :
    u = u' ∧ k = k' ∧ a = a' := by
  have hm := congrArg (emultiplicity lambdaE) he
  simp only [emultiplicity_mul lambdaE_prime,emultiplicity_pow_self_of_prime lambdaE_prime,
    unit_lambda_emultiplicity,primary_lambda_emultiplicity ha,primary_lambda_emultiplicity ha',
    zero_add,add_zero] at hm
  have hk : k = k' := by exact_mod_cast hm
  subst k'
  have hc : (u:Eisenstein)*a = (u':Eisenstein)*a' := by
    apply mul_right_cancel₀ (pow_ne_zero k lambdaE_prime.ne_zero)
    calc
      _ = (u:Eisenstein)*lambdaE^k*a := by ring
      _ = (u':Eisenstein)*lambdaE^k*a' := he
      _ = _ := by ring
  have haa : a = a' := by
    apply primary_associated_eq ha ha'
    refine ⟨u*u'⁻¹,?_⟩
    rw [Units.val_mul]
    calc
      _ = ((u':Eisenstein)*a')*((u'⁻¹:Eisensteinˣ):Eisenstein) := by rw [←hc]; ring
      _ = _ := by simp [mul_assoc,mul_comm]
  have huu : u = u' := by
    apply Units.ext
    rw [←haa] at hc
    exact mul_right_cancel₀ (primary_ne_zero ha) hc
  exact ⟨huu,rfl,haa⟩

end CubicFirstMoment

end

end OAI
