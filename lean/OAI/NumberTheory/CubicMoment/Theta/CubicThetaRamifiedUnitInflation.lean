import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryFourierTwist

namespace OAI

/-! Exact inflation of a ramified row with its global unit retained. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaEisensteinWeight_unit_lambda_mod (e : Eisensteinˣ) (k : ℕ) (a : Eisenstein) :
    cubicThetaEisensteinWeight ((e:Eisenstein)*lambdaE^k) a=
      cubicThetaEisensteinWeight ((e:Eisenstein)*lambdaE^(k%3)) a := by
  rw [cubicThetaEisensteinWeight_unit_lambda,cubicThetaEisensteinWeight_unit_lambda]
  by_cases ha : primary a
  · rw [ite_eq_left ha,ite_eq_left ha]
    have hc := cubicSymbol_cube_of_isCoprime ha lambdaE (primary_coprime_lambda ha)
    have he : (cubicSymbol a lambdaE)^k=(cubicSymbol a lambdaE)^(k%3) := by
      conv_lhs => rw [← Nat.mod_add_div k 3]
      rw [pow_add,pow_mul,hc,one_pow,mul_one]
    rw [he]
  · rw [ite_eq_right ha,ite_eq_right ha]

lemma cubicThetaEisensteinWeight_unit_lambda_congr (e : Eisensteinˣ) (k : ℕ)
    {a b : Eisenstein} (hab : (9:Eisenstein) ∣ a-b) :
    cubicThetaEisensteinWeight ((e:Eisenstein)*lambdaE^k) a=
      cubicThetaEisensteinWeight ((e:Eisenstein)*lambdaE^k) b := by
  obtain ⟨t,ht⟩ := hab
  rw [show a=b+9*t by linear_combination ht,
    cubicThetaEisensteinWeight_unit_lambda_periodic]

def cubicThetaUnitRamifiedBase (e : Eisensteinˣ) (j : ℕ) (h : Eisenstein) : ℂ :=
  ∑' x : Residues (3*(e:Eisenstein)*lambdaE^2),
    cubicThetaEisensteinWeight ((e:Eisenstein)*lambdaE^j)
      (residueRepresentative (3*(e:Eisenstein)*lambdaE^2) x)*
      residueFourierChar (3*(e:Eisenstein)*lambdaE^2)
        (mul_ne_zero (mul_ne_zero (by norm_num) e.ne_zero)
          (pow_ne_zero _ lambdaE_prime.ne_zero))
        (Ideal.Quotient.mk (modulus (3*(e:Eisenstein)*lambdaE^2)) h*x)

theorem cubicThetaEisensteinGaussCoefficient_unit_ramified_inflation
    (e : Eisensteinˣ) (n : ℕ) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^(n+2)) (lambdaE^n*h)=
      (norm (lambdaE^n):ℂ)*cubicThetaUnitRamifiedBase e ((n+2)%3) h := by
  let q : Eisenstein := 3*((e:Eisenstein)*lambdaE^(n+2))
  let d : Eisenstein := 3*(e:Eisenstein)*lambdaE^2
  have hq : q≠0 := mul_ne_zero (by norm_num)
    (mul_ne_zero e.ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero))
  have hd : d≠0 := mul_ne_zero (mul_ne_zero (by norm_num) e.ne_zero)
    (pow_ne_zero _ lambdaE_prime.ne_zero)
  have he : q=d*lambdaE^n := by dsimp only [q,d]; rw [pow_add]; ring
  have hdq : d ∣ q := ⟨lambdaE^n,he⟩
  have h9d : (9:Eisenstein) ∣ d := by
    refine ⟨-(e:Eisenstein),?_⟩
    dsimp only [d]
    rw [lambdaE_sq]
    ring
  have hw (x : Residues q) :
      cubicThetaEisensteinWeight ((e:Eisenstein)*lambdaE^(n+2)) (residueRepresentative q x)=
      cubicThetaEisensteinWeight ((e:Eisenstein)*lambdaE^((n+2)%3))
        (residueRepresentative d (residueReduction hdq x)) := by
    rw [cubicThetaEisensteinWeight_unit_lambda_mod]
    apply cubicThetaEisensteinWeight_unit_lambda_congr
    have hr : Ideal.Quotient.mk (modulus d) (residueRepresentative q x)=
        Ideal.Quotient.mk (modulus d)
          (residueRepresentative d (residueReduction hdq x)) := by
      rw [residueRepresentative_spec]
      have ht := congrArg (residueReduction hdq) (residueRepresentative_spec q x)
      simpa only [residueReduction_mk] using ht
    apply h9d.trans
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub]
    exact sub_eq_zero.mpr hr
  rw [cubicThetaEisensteinGaussCoefficient_fourier_of_eq
    (mul_ne_zero e.ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero)) hq rfl]
  simp_rw [hw]
  exact residueFourier_inflation_of_eq hq hd (pow_ne_zero _ lambdaE_prime.ne_zero)
    he hdq (fun x => cubicThetaEisensteinWeight ((e:Eisenstein)*lambdaE^((n+2)%3))
      (residueRepresentative d x)) h

end CubicFirstMoment

end

end OAI
