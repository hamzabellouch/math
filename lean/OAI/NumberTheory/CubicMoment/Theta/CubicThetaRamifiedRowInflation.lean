import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedRowConductor
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteInflation

namespace OAI

/-! Reduce every ramified row to one fixed residue ring. Only three
ramified exponents remain in its weight; the frequency and primary part
are retained exactly. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaEisensteinWeight_lambda_mod (k : ℕ) (a : Eisenstein) :
    cubicThetaEisensteinWeight (lambdaE^k) a=
      cubicThetaEisensteinWeight (lambdaE^(k%3)) a := by
  rw [cubicThetaEisensteinWeight_lambda_pow,cubicThetaEisensteinWeight_lambda_pow]
  by_cases ha : primary a
  · rw [ite_eq_left ha,ite_eq_left ha]
    have hc := cubicSymbol_cube_of_isCoprime ha lambdaE (primary_coprime_lambda ha)
    conv_lhs => rw [← Nat.mod_add_div k 3]
    rw [pow_add,pow_mul,hc,one_pow,mul_one]
  · rw [ite_eq_right ha,ite_eq_right ha]

lemma cubicThetaEisensteinWeight_ramified_mod {u : Eisenstein}
    (hu : primary u) (k : ℕ) (a : Eisenstein) :
    cubicThetaEisensteinWeight (lambdaE^k*u) a=
      cubicThetaEisensteinWeight (lambdaE^(k%3)*u) a := by
  rw [mul_comm (lambdaE^k) u,mul_comm (lambdaE^(k%3)) u,
    cubicThetaEisensteinWeight_factor hu,cubicThetaEisensteinWeight_factor hu,
    cubicThetaEisensteinWeight_lambda_mod]

lemma cubicThetaEisensteinWeight_ramified_congr {u : Eisenstein}
    (hu : primary u) (k : ℕ) {a b : Eisenstein} (hab : (9*u) ∣ a-b) :
    cubicThetaEisensteinWeight (lambdaE^k*u) a=
      cubicThetaEisensteinWeight (lambdaE^k*u) b := by
  obtain ⟨t,ht⟩ := hab
  have ha : a=b+9*u*t := by linear_combination ht
  rw [ha,cubicThetaEisensteinWeight_ramified_periodic hu]

def cubicThetaRamifiedBaseRow (u : Eisenstein) (hu : u≠0) (j : ℕ)
    (h : Eisenstein) : ℂ :=
  ∑' x : Residues (3*lambdaE^2*u),
    cubicThetaEisensteinWeight (lambdaE^j*u)
      (residueRepresentative (3*lambdaE^2*u) x)*
    residueFourierChar (3*lambdaE^2*u)
      (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ lambdaE_prime.ne_zero)) hu)
      (Ideal.Quotient.mk (modulus (3*lambdaE^2*u)) h*x)

theorem cubicThetaEisensteinGaussCoefficient_ramified_inflation {u : Eisenstein}
    (hu : primary u) (n : ℕ) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient (lambdaE^(n+2)*u) (lambdaE^n*h)=
      (norm (lambdaE^n):ℂ)*
        cubicThetaRamifiedBaseRow u (primary_ne_zero hu) ((n+2)%3) h := by
  let q : Eisenstein := 3*(lambdaE^(n+2)*u)
  let d : Eisenstein := 3*lambdaE^2*u
  have hq : q≠0 := mul_ne_zero (by norm_num)
    (mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) (primary_ne_zero hu))
  have hd : d≠0 := mul_ne_zero
    (mul_ne_zero (by norm_num) (pow_ne_zero _ lambdaE_prime.ne_zero)) (primary_ne_zero hu)
  have he : q=d*lambdaE^n := by
    dsimp only [q,d]
    rw [pow_add]
    ring
  have hdq : d ∣ q := ⟨lambdaE^n,he⟩
  have hw (x : Residues q) :
      cubicThetaEisensteinWeight (lambdaE^(n+2)*u) (residueRepresentative q x)=
      cubicThetaEisensteinWeight (lambdaE^((n+2)%3)*u)
        (residueRepresentative d (residueReduction hdq x)) := by
    rw [cubicThetaEisensteinWeight_ramified_mod hu]
    apply cubicThetaEisensteinWeight_ramified_congr hu
    have hr : Ideal.Quotient.mk (modulus d) (residueRepresentative q x)=
        Ideal.Quotient.mk (modulus d)
          (residueRepresentative d (residueReduction hdq x)) := by
      rw [residueRepresentative_spec]
      have ht := congrArg (residueReduction hdq) (residueRepresentative_spec q x)
      simpa only [residueReduction_mk] using ht
    have hdiv := Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp (show
        Ideal.Quotient.mk (modulus d)
          (residueRepresentative q x-residueRepresentative d (residueReduction hdq x))=0 by
          rw [map_sub,hr,sub_self]))
    have hde : d= -(9*u) := by dsimp only [d]; rw [lambdaE_sq]; ring
    have hb : 9*u ∣ d := ⟨-1,by rw [hde]; ring⟩
    exact hb.trans hdiv
  rw [cubicThetaEisensteinGaussCoefficient_fourier_of_eq
    (mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) (primary_ne_zero hu)) hq rfl]
  simp_rw [hw]
  exact residueFourier_inflation_of_eq hq hd (pow_ne_zero _ lambdaE_prime.ne_zero)
    he hdq (fun x => cubicThetaEisensteinWeight (lambdaE^((n+2)%3)*u)
      (residueRepresentative d x)) h

end CubicFirstMoment

end

end OAI
