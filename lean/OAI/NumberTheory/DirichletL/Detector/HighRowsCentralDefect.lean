import OAI.NumberTheory.DirichletL.Detector.HighRowsCentralBase
import OAI.NumberTheory.DirichletL.Detector.HighRowsCentralEntry

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
include hc in
lemma rowClosedMarked_central_size (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j : ℕ) (hj : j<6) :
    ‖rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j‖≤
      132*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-10*eps) := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ1 : 1≤Q := by dsimp [Q];linarith
  have hrem := rowClosedMarked_central_remainder p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ
    halpha halpha1 heps heps1 hx hw hz j hj
  dsimp only at hrem
  simp only [Complex.ofReal_natCast] at hrem
  have ht := sourceRowTerm_central_strict_norm p hp hg hc eta a rho x w z heta ha hρ j hj
  rw [sourceRowTerm_pos p hp hg eta a rho x w z j 1 0 1 0 (by omega)] at ht
  have hr := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_R_half _ hQ a x z ha (by rw [hx];linarith) (by rw [hz]))
  have he : Q^(1-x.re-w.re)=Q^(-10*eps) := by congr 1;rw [hx,hw];ring
  have hn : Q^(1/2-x.re)≤Q^(-10*eps) := Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hx];linarith)
  have hdiv : ‖rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV Q z) rho j 1 0 1 0 /
      (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV Q z))‖≤4*Q^(-10*eps) := by
    rw [div_eq_mul_inv,norm_mul]
    have hh := mul_le_mul ht hr (norm_nonneg _) (by positivity)
    exact hh.trans_eq (by change (2*Q^(1-x.re-w.re))*2=4*Q^(-10*eps);rw [he];ring)
  dsimp only [Q] at hdiv
  have hh := (norm_add_le _ _).trans (add_le_add hrem hdiv)
  simp only [sub_add_cancel] at hh
  exact hh.trans (by change 128*Q^(1/2-x.re)+4*Q^(-10*eps)≤132*Q^(-10*eps);nlinarith)

include hc in
theorem ramifiedClosed_central_defect (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j : ℕ) (hj : j<6) :
    ‖ramifiedClosed p hp hg eta a rho x w z j-1‖≤
      198*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-10*eps) := by
  have hb := rowClosedMarked_central_size p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ
    halpha halpha1 heps heps1 hx hw hz j hj
  have hv := first_region_V_half _ hQ z (by rw [hz])
  have hs := norm_sub_le (1:ℂ) (coordV (Ideal.absNorm (Ideal.span {p})) z)
  rw [norm_one] at hs
  unfold ramifiedClosed
  rw [add_sub_cancel_left,norm_mul]
  apply (mul_le_mul (show ‖1-coordV (Ideal.absNorm (Ideal.span {p})) z‖≤3/2 by linarith)
    hb (norm_nonneg _) (by norm_num : (0:ℝ)≤3/2)).trans_eq
  ring
end SevenEighths.ProbeEuler
end

end OAI
