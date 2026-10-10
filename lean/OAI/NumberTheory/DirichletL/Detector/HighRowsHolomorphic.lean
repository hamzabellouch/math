import OAI.NumberTheory.DirichletL.Detector.HighRowsRamified
import OAI.NumberTheory.DirichletL.Detector.GlobalHolomorphic

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p})

lemma rowMarkedTerm_differentiableAt (eta a rho : ℂ) (X W V : ℂ→ℂ) (t : ℂ)
    (hX : DifferentiableAt ℂ X t) (hW : DifferentiableAt ℂ W t) (hV : DifferentiableAt ℂ V t)
    (j e l k m : ℕ) :
    DifferentiableAt ℂ (fun s=>rowMarkedTerm p hp hg eta a (X s) (W s) (V s) rho j e l k m) t := by
  unfold rowMarkedTerm
  split_ifs
  · fun_prop
  · unfold rowWeightedScalar weightedScalar
    fun_prop

lemma rowBaseFinite_differentiableAt (eta a rho : ℂ) (X W V : ℂ→ℂ) (t : ℂ)
    (hX : DifferentiableAt ℂ X t) (hW : DifferentiableAt ℂ W t) (hV : DifferentiableAt ℂ V t)
    (hv : 1-V t≠0) (j e l : ℕ) :
    DifferentiableAt ℂ (fun s=>rowBaseFinite p hp hg eta a (X s) (W s) (V s) rho j e l) t := by
  have hd (k m : ℕ) := rowMarkedTerm_differentiableAt p hp hg eta a rho X W V t hX hW hV j e l k m
  unfold rowBaseFinite
  fun_prop (disch := assumption)

lemma rowClosedMarked_differentiableAt (eta a rho : ℂ) (X W V : ℂ→ℂ) (t : ℂ)
    (hX : DifferentiableAt ℂ X t) (hW : DifferentiableAt ℂ W t) (hV : DifferentiableAt ℂ V t)
    (hv : 1-V t≠0) (hr : 1-evenRatio (Ideal.absNorm (Ideal.span {p})) a (X t) (V t)≠0) (j : ℕ) :
    DifferentiableAt ℂ (fun s=>rowClosedMarked p hp hg eta a (X s) (W s) (V s) rho j) t := by
  have hd (e l : ℕ) := rowBaseFinite_differentiableAt p hp hg eta a rho X W V t hX hW hV hv j e l
  have hR : DifferentiableAt ℂ (fun s=>evenRatio (Ideal.absNorm (Ideal.span {p})) a (X s) (V s)) t := by
    unfold evenRatio
    fun_prop
  unfold rowClosedMarked
  fun_prop (disch := assumption)

lemma ramifiedClosed_differentiableAt (eta a rho : ℂ) (X W Z : ℂ→ℂ) (t : ℂ)
    (hX : DifferentiableAt ℂ X t) (hW : DifferentiableAt ℂ W t) (hZ : DifferentiableAt ℂ Z t)
    (hv : 1-coordV (Ideal.absNorm (Ideal.span {p})) (Z t)≠0)
    (hr : 1-coordR (Ideal.absNorm (Ideal.span {p})) (a^2) (X t) (Z t)≠0) (j : ℕ) :
    DifferentiableAt ℂ (fun s=>ramifiedClosed p hp hg eta a rho (X s) (W s) (Z s) j) t := by
  have hQ : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hcx : DifferentiableAt ℂ (fun s=>(Ideal.absNorm (Ideal.span {p}):ℂ)^(-X s)) t := by
    exact hX.neg.const_cpow (Or.inl (by exact_mod_cast hQ.ne'))
  have hcw : DifferentiableAt ℂ (fun s=>(Ideal.absNorm (Ideal.span {p}):ℂ)^(-W s)) t := by
    exact hW.neg.const_cpow (Or.inl (by exact_mod_cast hQ.ne'))
  have hcv := (coordV_differentiable _ hQ).differentiableAt.comp t hZ
  change DifferentiableAt ℂ (fun s=>coordV (Ideal.absNorm (Ideal.span {p})) (Z s)) t at hcv
  have hr' := evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}):ℝ) hQ a (X t) (Z t)
  simp only [Complex.ofReal_natCast] at hr'
  have hd := rowClosedMarked_differentiableAt p hp hg eta a rho _ _ _ t hcx hcw hcv hv
    (by rw [hr'];exact hr) j
  unfold ramifiedClosed
  fun_prop

lemma ramifiedClosed_analytic_x (eta a rho w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1) (hz : (4/25:ℝ)≤z.re) (j : ℕ) :
    AnalyticOnNhd ℂ (fun x=>ramifiedClosed p hp hg eta a rho x w z j) {x : ℂ|7/8<x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := open_region_denominators _ (a^2) 0 0 x z hQ
    (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha) (by norm_num) (by norm_num) hx.le hz
  exact (ramifiedClosed_differentiableAt p hp hg eta a rho id (fun _=>w) (fun _=>z) x
    differentiableAt_id (differentiableAt_const w) (differentiableAt_const z) hd.2.1 hd.1 j).differentiableWithinAt

lemma ramifiedClosed_analytic_w (eta a rho x z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1)
    (hx : (7/8:ℝ)≤x.re) (hz : (4/25:ℝ)≤z.re) (j : ℕ) :
    Differentiable ℂ (fun w=>ramifiedClosed p hp hg eta a rho x w z j) := by
  intro w
  have hd := open_region_denominators _ (a^2) 0 0 x z hQ
    (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha) (by norm_num) (by norm_num) hx hz
  exact ramifiedClosed_differentiableAt p hp hg eta a rho (fun _=>x) id (fun _=>z) w
    (differentiableAt_const x) differentiableAt_id (differentiableAt_const z) hd.2.1 hd.1 j

lemma ramifiedClosed_analytic_z (eta a rho x w : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1) (hx : (7/8:ℝ)≤x.re) (j : ℕ) :
    AnalyticOnNhd ℂ (fun z=>ramifiedClosed p hp hg eta a rho x w z j) {z : ℂ|4/25<z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := open_region_denominators _ (a^2) 0 0 x z hQ
    (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha) (by norm_num) (by norm_num) hx hz.le
  exact (ramifiedClosed_differentiableAt p hp hg eta a rho (fun _=>x) (fun _=>w) id z
    (differentiableAt_const x) (differentiableAt_const w) differentiableAt_id hd.2.1 hd.1 j).differentiableWithinAt

end SevenEighths.ProbeEuler
end

end OAI
