import OAI.NumberTheory.DirichletL.Detector.HighRowsScalarBounds

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma sourceWeightedScalar_norm_le (Q : ℝ) (hQ : 0<Q)
    (eta a gamma C omega x w z scalar : ℂ) (heta : ‖eta‖≤1) (ha : ‖a‖≤1)
    (hgamma : ‖gamma‖=1) (hC : ‖C‖=1) (ho : ‖omega‖=1) (e l k m : ℕ) :
    ‖sourceWeightedScalar Q eta a gamma C omega x w z scalar e l k m‖≤
      ‖scalar‖*Q^(-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)) := by
  let coeff : ℂ := (-1:ℂ)^e*gamma^(-(e:ℤ))*eta^e*(a*C)^l*
    omega^((((e+3*l)*k:ℕ):ℤ)-(e*l+l.choose 2:ℕ))
  have hn : ‖coeff‖≤1 := by
    simp only [coeff,norm_mul,norm_pow,norm_zpow,hgamma,hC,ho,norm_neg,norm_one,
      one_pow,one_zpow,mul_one,one_mul]
    exact (mul_le_of_le_one_left (by positivity) (pow_le_one₀ (norm_nonneg _) heta)).trans (pow_le_one₀ (norm_nonneg _) ha)
  change ‖coeff*scalar*(Q:ℂ)^_‖≤_
  rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  have he : (-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)).re=
      -(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ) := by simp
  rw [he]
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (norm_nonneg _) hn) (by positivity)

lemma scalar_spectral_power (Q x w z : ℝ) (hQ : 0<Q) (e l k m : ℕ) :
    (2*Q^(e+3*l)*(Real.sqrt Q)^k)*
      Q^(-(x+1/2)*(e:ℝ)-(1+3*x)*(l:ℝ)-w*(k:ℝ)-6*z*(m:ℝ))=
      2*Q^((1/2-x)*(e:ℝ)+(2-3*x)*(l:ℝ)+(1/2-w)*(k:ℝ)-6*z*(m:ℝ)) := by
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul_natCast hQ.le,←Real.rpow_natCast Q (e+3*l)]
  rw [mul_assoc 2,←Real.rpow_add hQ,mul_assoc 2,←Real.rpow_add hQ]
  congr 1
  push_cast
  ring_nf

theorem sourceRowTerm_norm_le (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (eta a rho x w z : ℂ) (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (j e l k m : ℕ) (ht : 0<e+3*l) (hk : k≤1) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^((1/2-x.re)*(e:ℝ)+(2-3*x.re)*(l:ℝ)+
        (1/2-w.re)*(k:ℝ)-6*z.re*(m:ℝ)) := by
  have hQ : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hrho := Complex.norm_eq_one_of_pow_eq_one hρ (by decide : (6:ℕ)≠0)
  rw [sourceRowTerm,norm_mul,norm_div,norm_pow,norm_pow,hrho,one_pow,one_pow,div_self (by norm_num : (1:ℝ)≠0),one_mul]
  apply (sourceWeightedScalar_norm_le _ hQ eta a _ _ _ x w z _ heta ha
    (localGamma_norm_one p hp.ne_zero hg hc 1 (by decide) (by decide))
    (by rw [norm_star];exact localGamma_norm_one p hp.ne_zero hg hc 3 (by decide) (by decide))
    (Complex.norm_eq_one_of_pow_eq_one (actualSextic_neg_one_sq _ hg) (by decide)) e l k m).trans
  have hs := positiveScalar_norm_le p hp hg hc (e+3*l-1) k (j+6*m) hk
  rw [show e+3*l-1+1=e+3*l by omega] at hs
  rw [sourceScalar,ite_eq_right (by omega)]
  exact (mul_le_mul_of_nonneg_right hs (by positivity)).trans_eq
    (scalar_spectral_power _ x.re w.re z.re hQ e l k m)

end SevenEighths.ProbeEuler
end

end OAI
