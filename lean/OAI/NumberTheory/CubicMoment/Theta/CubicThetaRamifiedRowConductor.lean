import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowFiniteFourier
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteConductor
import OAI.NumberTheory.CubicMoment.Estimates.CubicSupplementaryPeriodicityProof

namespace OAI

/-! The ramified row weight has conductor dividing nine times its primary
part. Consequently the lambda exponent of a nonzero Fourier row is bounded
by the lambda exponent of its frequency plus two. These are finite character
identities, with the original zero extension retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaEisensteinWeight_lambda_pow (k : ℕ) (a : Eisenstein) :
    cubicThetaEisensteinWeight (lambdaE^k) a=
      if primary a then (cubicSymbol a lambdaE)^k else 0 := by
  unfold cubicThetaEisensteinWeight
  by_cases ha : primary a
  · rw [ite_eq_left ⟨ha,(primary_coprime_lambda ha).symm.pow_left⟩,ite_eq_left ha,
      cubicSymbol_pow_upper ha]
  · rw [ite_eq_right (fun h => ha h.1),ite_eq_right ha]

lemma cubicThetaEisensteinWeight_lambda_periodic (k : ℕ) (a b : Eisenstein) :
    cubicThetaEisensteinWeight (lambdaE^k) (a+9*b)=
      cubicThetaEisensteinWeight (lambdaE^k) a := by
  have hp : primary (a+9*b) ↔ primary a := by
    constructor
    · rintro ⟨t,ht⟩
      exact ⟨t-3*b,by linear_combination ht⟩
    · rintro ⟨t,ht⟩
      exact ⟨t+3*b,by linear_combination ht⟩
  rw [cubicThetaEisensteinWeight_lambda_pow,cubicThetaEisensteinWeight_lambda_pow]
  by_cases ha : primary a
  · rw [ite_eq_left (hp.mpr ha),ite_eq_left ha,
      cubicSymbol_lambda_periodic (hp.mpr ha) ha ⟨b,by ring⟩]
  · rw [ite_eq_right (fun h => ha (hp.mp h)),ite_eq_right ha]

lemma cubicThetaEisensteinWeight_ramified_periodic {u : Eisenstein}
    (hu : primary u) (k : ℕ) (a b : Eisenstein) :
    cubicThetaEisensteinWeight (lambdaE^k*u) (a+9*u*b)=
      cubicThetaEisensteinWeight (lambdaE^k*u) a := by
  rw [mul_comm (lambdaE^k) u,cubicThetaEisensteinWeight_factor hu,
    cubicThetaEisensteinWeight_factor hu]
  have hc : cubicSymbol u (a+9*u*b)=cubicSymbol u a := by
    apply cubicSymbol_congr
    apply residue_eq_of_dvd_sub
    exact ⟨9*b,by ring⟩
  rw [hc,show a+9*u*b=a+9*(u*b) by ring,
    cubicThetaEisensteinWeight_lambda_periodic]

theorem cubicThetaEisensteinGaussCoefficient_ramified_support {u : Eisenstein}
    (hu : primary u) (n : ℕ) (h : Eisenstein)
    (hG : cubicThetaEisensteinGaussCoefficient (lambdaE^(n+2)*u) h≠0) :
    lambdaE^n ∣ h := by
  let c : Eisenstein := lambdaE^(n+2)*u
  have hc : c≠0 := mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) (primary_ne_zero hu)
  have hq : (3:Eisenstein)*c≠0 := mul_ne_zero (by norm_num) hc
  let : Finite (Residues (3*c)) := finite_residues hq
  let : Fintype (Residues (3*c)) := Fintype.ofFinite _
  have h3 : (3:Eisenstein)∣c := by
    refine ⟨-(lambdaE^n*u),?_⟩
    dsimp only [c]
    rw [pow_add,lambdaE_sq]
    ring
  have hf (x b : Residues (3*c)) :
      cubicThetaEisensteinResidueWeight c
        (x+Ideal.Quotient.mk (modulus (3*c)) (9*u)*b)=
      cubicThetaEisensteinResidueWeight c x := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul,← map_add,cubicThetaEisensteinResidueWeight_mk h3,
      cubicThetaEisensteinResidueWeight_mk h3]
    exact cubicThetaEisensteinWeight_ramified_periodic hu (n+2) a b
  have hd : 3*c ∣ (9*u)*h := by
    apply residueFourier_reduction_support hq
      (cubicThetaEisensteinResidueWeight c) h hf
    change cubicThetaEisensteinGaussCoefficient c h≠0 at hG
    rw [cubicThetaEisensteinGaussCoefficient_fourier hc] at hG
    simpa only [cubicThetaEisensteinResidueWeight,tsum_fintype] using hG
  have he : 3*c=(9*u)*(-lambdaE^n) := by
    dsimp only [c]
    rw [pow_add,lambdaE_sq]
    ring
  rw [he,mul_dvd_mul_iff_left (mul_ne_zero (by norm_num) (primary_ne_zero hu)),
    neg_dvd] at hd
  exact hd

theorem cubicThetaEisensteinGaussCoefficient_ramified_zero {u : Eisenstein}
    (hu : primary u) (n : ℕ) (h : Eisenstein) (hh : ¬lambdaE^n ∣ h) :
    cubicThetaEisensteinGaussCoefficient (lambdaE^(n+2)*u) h=0 := by
  by_contra hn
  exact hh (cubicThetaEisensteinGaussCoefficient_ramified_support hu n h hn)

end CubicFirstMoment

end

end OAI
