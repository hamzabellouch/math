import OAI.NumberTheory.DirichletL.Detector.HighRowsCentralStrictSelected
import OAI.NumberTheory.DirichletL.Detector.HighRowsCentralLower

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma norm_div_le_twice (A H : ℂ) (hH : 1/2≤‖H‖) : ‖A/H‖≤2*‖A‖ := by
  rw [norm_div]
  apply (div_le_iff₀ (by linarith : 0<‖H‖)).mpr
  nlinarith [norm_nonneg A]

variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
include hc in
theorem ramifiedSelected_central_quotient (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (hsmall : 198*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-10*eps)≤1/2)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j : ℕ) (hj : j<6) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    Q^(-1:ℝ)*‖ramifiedSelected p hp hg eta a rho x w z j /
      ramifiedClosed p hp hg eta a rho x w z j‖≤
      800*Q^(-(1/2:ℝ))+(if 2≤j then 12*Q^(-w.re) else 0) := by
  dsimp only
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ0 : 0<Q := by dsimp [Q];linarith
  have hQ1 : 1≤Q := by linarith
  have hH := ramifiedClosed_central_lower p hp hg hc eta a rho x w z alpha eps hQ hsmall heta ha hρ
    halpha halpha1 heps heps1 hx hw hz j hj
  have hreg := ramifiedSelected_central_regular p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ
    halpha halpha1 heps heps1 hx hw hz j hj
  have hnorm := norm_div_le_twice (ramifiedSelected p hp hg eta a rho x w z j)
    (ramifiedClosed p hp hg eta a rho x w z j) hH
  have htri := (norm_add_le _ _).trans (add_le_add hreg (le_refl ‖ramifiedStrictSelected p hp hg eta a rho x w z j‖))
  rw [sub_add_cancel] at htri
  have hpow : Q^(-1:ℝ)*Q^(1/2:ℝ)=Q^(-(1/2:ℝ)) := by rw [←Real.rpow_add hQ0];norm_num
  have hqi : 0≤Q^(-1:ℝ) := Real.rpow_nonneg hQ0.le _
  by_cases hj2 : 2≤j
  · rw [ite_eq_left hj2]
    have hs := ramifiedStrictSelected_central_norm p hp hg hc eta a rho x w z hQ heta ha hρ
      (by rw [hx];linarith) (by rw [hz]) j hj
    have hb : ‖ramifiedSelected p hp hg eta a rho x w z j‖≤385*Q^(1/2:ℝ)+6*Q^(1-w.re) := by linarith
    have hprod : Q^(-1:ℝ)*Q^(1-w.re)=Q^(-w.re) := by rw [←Real.rpow_add hQ0];congr 1;ring
    calc
      _≤Q^(-1:ℝ)*(2*(385*Q^(1/2:ℝ)+6*Q^(1-w.re))) := mul_le_mul_of_nonneg_left (hnorm.trans (by linarith)) hqi
      _=770*Q^(-(1/2:ℝ))+12*Q^(-w.re) := by nlinarith [hpow,hprod]
      _≤_ := by nlinarith [Real.rpow_nonneg hQ0.le (-(1/2:ℝ))]
  · rw [ite_eq_right hj2,add_zero]
    have hs := ramifiedStrictSelected_boundary_norm p hp hg hc eta a rho x w z hQ heta ha hρ
      (by rw [hx];linarith) (by rw [hz]) j (by omega)
    have hqw : Q^(-w.re)≤Q^(1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hw];linarith)
    have hb : ‖ramifiedSelected p hp hg eta a rho x w z j‖≤391*Q^(1/2:ℝ) := by nlinarith
    calc
      _≤Q^(-1:ℝ)*(2*(391*Q^(1/2:ℝ))) := mul_le_mul_of_nonneg_left (hnorm.trans (by linarith)) hqi
      _=782*Q^(-(1/2:ℝ)) := by nlinarith [hpow]
      _≤_ := mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hQ0.le _)
end SevenEighths.ProbeEuler
end

end OAI
