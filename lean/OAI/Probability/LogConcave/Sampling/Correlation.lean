import Mathlib
import OAI.Probability.LogConcave.Complexity.VelocityNormalizedBudgetCalibrated

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter
open scoped Topology

lemma centerScaleRate {α : ℕ → ℝ} {u a : ℝ} (hα : LogPowerRate α u) :
    LogPowerRate (fun d => (α d)^2*(((d:ℝ)^(-a))⁻¹)^4) (2*u-4*a) := by
  convert! (hα.pow 2).mul ((LogPowerRate.inv_power a).pow 4) using 1
  first | rfl | (norm_num; ring)

lemma centerStateQuadratureEnvelope_rate (n : ℕ) {α : ℕ → ℝ} {u a : ℝ}
    (hα : LogPowerRate α u) :
    LogPowerRate (fun d => centerStateQuadratureEnvelope n (α d) ((d:ℝ)^(-a)))
      ((n+2)*(2*u-4*a)) := by
  have he := (((centerScaleRate (a:=a) hα).pow (n+2)).const_mul (8*(singleCellBasisBudget n)^2)).mul_const
    (centeringStateBudget (n+2))
  simpa only [centerStateQuadratureEnvelope,Nat.cast_add,Nat.cast_ofNat] using he

lemma centerInitialEnvelope_rate {α : ℕ → ℝ} {u a : ℝ} (hα : LogPowerRate α u) :
    LogPowerRate (fun d => centerInitialEnvelope (α d) ((d:ℝ)^(-a))) (2*u-4*a) :=
  ((centerScaleRate hα).const_mul 2).mul_const (centeringStateBudget 1)

lemma centerStateEnvelope_rate (n N : ℕ) {α q E : ℕ → ℝ} {u a v e z : ℝ}
    (hα : LogPowerRate α u) (hq : LogPowerRate q v) (hE : LogPowerRate E e)
    (hz₁ : z≤2*u+e) (hz₂ : z≤(n+2)*(2*u-4*a))
    (hz₃ : z≤(2*N)*v+(2*u-4*a)) :
    LogPowerRate (fun d => centerStateEnvelope n N (α d) ((d:ℝ)^(-a)) (q d) (E d)) z := by
  have hp := ((hα.pow 2).const_mul (2*(centeringRowBudget n:ℝ)^2)).mul hE
  have hp' : LogPowerRate (fun d => 2*(centeringRowBudget n:ℝ)^2*(α d)^2*E d) z := by
    apply hp.mono
    norm_num
    exact hz₁
  have hs := ((centerStateQuadratureEnvelope_rate n hα).const_mul 2).mono hz₂
  have hq' := ((hq.pow (2*N)).const_mul 2).mul (centerInitialEnvelope_rate (a:=a) hα)
  have hq'' : LogPowerRate (fun d => 2*(q d)^(2*N)*centerInitialEnvelope (α d) ((d:ℝ)^(-a))) z := by
    apply hq'.mono
    push_cast
    exact hz₃
  exact ((hp'.add hs).const_mul 8).add hq''

lemma centerMeanEnvelope_rate (n : ℕ) {α Z : ℕ → ℝ} {u a z e : ℝ}
    (hα : LogPowerRate α u) (hZ : LogPowerRate Z z)
    (he₁ : e≤2*u+z) (he₂ : e≤2*u+(n+1)*(2*u-4*a)) :
    LogPowerRate (fun d => centerMeanEnvelope n (α d) ((d:ℝ)^(-a)) (Z d)) e := by
  have hp := ((hα.pow 2).const_mul (2*(centeringRowBudget n:ℝ)^2*(Real.pi^2/2)^2)).mul hZ
  have hp' : LogPowerRate (fun d => 2*(centeringRowBudget n:ℝ)^2*(Real.pi^2/2)^2*(α d)^2*Z d) e := by
    apply hp.mono
    norm_num
    exact he₁
  have hq := (((hα.pow 2).const_mul (8*(singleCellBasisBudget n)^2)).mul
    ((centerScaleRate (a:=a) hα).pow (n+1))).mul_const (centeringMeanBudget (n+1))
  have hq' : LogPowerRate (fun d => 8*(singleCellBasisBudget n)^2*(α d)^2*
      ((α d)^2*(((d:ℝ)^(-a))⁻¹)^4)^(n+1)*centeringMeanBudget (n+1)) e := by
    apply hq.mono
    push_cast
    exact he₂
  exact hp'.add hq'

theorem centeringEnvelopes_calibrated {α q E : ℕ → ℝ} {κ J b t w : ℝ} {n N : ℕ}
    (hκ : 0<κ) (hJ : 1≤J) (hb : 1/2≤b) (ht : 0<t) (htsmall : t<1/100)
    (hw : 0<w) (hwt : w<t)
    (hnw : J+10<w*((n:ℝ)-3)) (hnt : J+10<t*((n:ℝ)-3))
    (hnn : 4*(J+10)<(n:ℝ)) (hN : 10*(J+2)≤(N:ℝ))
    (hα : LogPowerRate α (κ*b)) (hq : LogPowerRate q (κ/3))
    (hE : LogPowerRate E (2*κ*(J+8))) :
    let Z := fun d => centerStateEnvelope n N (α d) ((d:ℝ)^(-(κ*t))) (q d) (E d)
    LogPowerRate Z (2*κ*(J+8)) ∧
    LogPowerRate (fun d => centerMeanEnvelope n (α d) ((d:ℝ)^(-(κ*t))) (Z d)) (2*κ*(J+8)) := by
  intro Z
  obtain ⟨hp,hh,hiter,ha₁,ha₂,hv₁,hv₂,hlip,hbeta,hcq,hniter,hmq⟩ :=
    numerical_exponent_margins hJ hb ht htsmall hw hwt hnw hnt hnn hN
  have hκb : 0≤κ*b := mul_nonneg hκ.le (by linarith)
  have hκβ := mul_nonneg hκ.le hbeta
  have hZ : LogPowerRate Z (2*κ*(J+8)) := by
    apply centerStateEnvelope_rate n N hα hq hE
    · linarith
    · have he := mul_le_mul_of_nonneg_left hcq hκ.le
      nlinarith
    · have he := mul_le_mul_of_nonneg_left hniter hκ.le
      nlinarith
  refine ⟨hZ,?_⟩
  apply centerMeanEnvelope_rate n hα hZ
  · linarith
  · have he := mul_le_mul_of_nonneg_left hmq hκ.le
    nlinarith
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Filter Quadrature
open scoped Topology

def sourceCorrelation (a : ℝ) (d : ℕ) : ℝ := Real.sqrt (1-((d:ℝ)^(-a))^2)

lemma sourceCorrelation_eventually {a : ℝ} (ha : 0<a) :
    ∀ᶠ d : ℕ in atTop,0<sourceCorrelation a d ∧ sourceCorrelation a d<1 ∧
      ((d:ℝ)^(-a))^2=1-(sourceCorrelation a d)^2 := by
  have ht := (tendsto_rpow_neg_atTop ha).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have he := ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [he,eventually_ge_atTop (1:ℕ)] with d hd hd1
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd1
  change (d:ℝ)^(-a)<1 at hd
  have hp := Real.rpow_pos_of_pos hd0 (-a)
  have hs : 0<1-((d:ℝ)^(-a))^2 := by nlinarith
  have hsq := Real.sq_sqrt hs.le
  refine ⟨Real.sqrt_pos.mpr hs,?_,?_⟩
  · change Real.sqrt _<1
    nlinarith [Real.sqrt_nonneg (1-((d:ℝ)^(-a))^2)]
  · change ((d:ℝ)^(-a))^2=1-Real.sqrt (1-((d:ℝ)^(-a))^2)^2
    linarith

lemma sourceCorrelation_tendsto {a : ℝ} (ha : 0<a) :
    Tendsto (sourceCorrelation a) atTop (nhds 1) := by
  have ht := (tendsto_rpow_neg_atTop ha).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  change Tendsto (fun d : ℕ => Real.sqrt (1-((d:ℝ)^(-a))^2)) atTop (nhds 1)
  simpa only [Function.comp_def,zero_pow (by omega : (2:ℕ)≠0),sub_zero,Real.sqrt_one] using
    ((tendsto_const_nhds (x:=(1:ℝ))).sub (ht.pow 2)).sqrt

lemma sourceMesh_eventually {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    ∀ᶠ d : ℕ in atTop,(d:ℝ)^(-b) ≤ Real.log 2 ∧
      (d:ℝ)^(-b) ≤ logMeshLength (sourceCorrelation a d) := by
  have ht := (tendsto_rpow_neg_atTop hb).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have he := ht.eventually (gt_mem_nhds (Real.log_pos (by norm_num : (1:ℝ)<2)))
  have hc := (sourceCorrelation_tendsto ha).eventually (lt_mem_nhds (by norm_num : (1/2:ℝ)<1))
  filter_upwards [he,hc,sourceCorrelation_eventually ha] with d hd hcd hp
  refine ⟨hd.le,?_⟩
  apply hd.le.trans
  unfold logMeshLength
  rw [←Real.log_inv]
  apply Real.log_le_log (by norm_num)
  rw [inv_eq_one_div]
  apply (le_div_iff₀ (by linarith : 0<1-sourceCorrelation a d)).mpr
  linarith

lemma sourceAngle_eventually {a : ℝ} (ha : 0<a) (n : ℕ) :
    ∀ᶠ d : ℕ in atTop,(d:ℝ)^(-a)*(n:ℝ) ≤ 1 := by
  have ht := ((tendsto_rpow_neg_atTop ha).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).mul_const (n:ℝ)
  have ht' : Tendsto (fun d : ℕ => (d:ℝ)^(-a)*(n:ℝ)) atTop (nhds 0) := by
    simpa only [Function.comp_def,zero_mul] using ht
  exact (ht'.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))).mono (fun _ h => h.le)
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Filter Quadrature
open scoped Topology Classical BigOperators NNReal

lemma probabilityMeanLipschitz_rate {lam : ℕ → ℝ≥0} {r : ℕ → ℝ} {u : ℝ}
    (hl : LogPowerRate (fun d => (lam d:ℝ)*(r d)^2) u) (A : ℝ≥0) :
    LogPowerRate (fun d => (A*probabilityMeanLipschitz (lam d) (r d):ℝ≥0)) u := by
  apply (hl.const_mul ((A:ℝ)*(Real.pi^2/2))).congr
  apply Eventually.of_forall
  intro d
  change (A:ℝ)*(Real.pi^2/2)*((lam d:ℝ)*(r d)^2) =
    (A:ℝ)*((Real.pi^2/2)*(lam d:ℝ)*(r d)^2)
  ring

theorem centeringScalarCalibration (k n N : ℕ) (A Ap Ah Lp contraction : ℝ≥0) (C J₀ D : ℝ)
    {lam : ℕ → ℝ≥0} {r s : ℕ → ℝ} {κ J b t w : ℝ}
    (hκ : 0<κ) (hJ : 1≤J) (hb : 1/2≤b) (ht : 0<t) (htsmall : t<1/100)
    (hw : 0<w) (hwt : w<t)
    (hnw : J+10<w*((n:ℝ)-3)) (hnt : J+10<t*((n:ℝ)-3))
    (hnn : 4*(J+10)<(n:ℝ)) (hN : 10*(J+2)≤(N:ℝ))
    (hl : LogPowerRate (fun d => (lam d:ℝ)*(r d)^2) (κ*b))
    (hα : LogPowerRate (fun d => (lam d:ℝ)*r d/s d) (κ*b))
    (hr : ∀ᶠ d : ℕ in atTop,0<r d) (hs : ∀ᶠ d : ℕ in atTop,0<s d) :
    let R := fun d : ℕ => (d:ℝ)^(-(κ*t))
    let T := sourceCorrelation (κ*t)
    let h := fun d : ℕ => (d:ℝ)^(-(κ*w))
    let ψ := fun d : ℕ => (d:ℝ)^(-(κ*(4*t)))
    let E := fun d => velocityNormalizedBudget d k n n N (lam d) Ap Ah Lp (r d) (R d) (T d) (h d) (ψ d) C J₀ D
    let q := fun d => centeringRowBudget n*velocityJointLip n n A (lam d) (r d) (T d) (h d) (ψ d) (s d)
    let Z := fun d => centerStateEnvelope n N ((lam d:ℝ)*r d/s d) (R d) (q d:ℝ) (E d)
    ∀ᶠ d : ℕ in atTop,
      (lam d:ℝ)*(r d)^2≤1/2 ∧ contraction*probabilityMeanLipschitz (lam d) (r d)≤1/2 ∧
      q d≤1/2 ∧ Z d≤(d:ℝ)^(-(2*κ*J)) ∧
      centerMeanEnvelope n ((lam d:ℝ)*r d/s d) (R d) (Z d)≤(d:ℝ)^(-(2*κ*J)) := by
  intro R T h ψ E q Z
  have hκt := mul_pos hκ ht
  have hκw := mul_pos hκ hw
  have hκb : 0<κ*b := mul_pos hκ (by linarith)
  have hT := sourceCorrelation_eventually hκt
  have hT0 : ∀ᶠ d : ℕ in atTop,0<T d := hT.mono (fun _ h => h.1)
  have hT1 : ∀ᶠ d : ℕ in atTop,T d<1 := hT.mono (fun _ h => h.2.1)
  have hRT : ∀ᶠ d : ℕ in atTop,(R d)^2≤1-(T d)^2 := hT.mono (fun _ h => h.2.2.le)
  have hmesh := sourceMesh_eventually hκt hκw
  have hsmall := hmesh.mono (fun _ hd => hd.1)
  have hlarge := hmesh.mono (fun _ hd => hd.2)
  have hE : LogPowerRate E (2*κ*(J+8)) := velocityNormalizedBudget_calibrated k n N Ap Ah Lp C J₀ D
    hκ hJ hb ht htsmall hw hwt hnw hnt hnn hN hl hT0 hT1 hRT hsmall hlarge
  obtain ⟨Dq,hDq,hDqu⟩ := exists_basisDerivative_budget (probabilityNodes (n+1))
  have hW := terminalQuadratureWeight_rate n Dq (by linarith) hDqu (κ*t) (κ*w) hT0 hT1 hRT hsmall hlarge
  have hlip := velocityJointLip_rate n n A (show 0≤κ*w+κ*(4*t) by positivity)
    hr hs hT0 hT1 hW hα
  have hmargin : κ/3≤κ*b-κ*w-κ*(4*t) := by
    have hex := (numerical_exponent_margins hJ hb ht htsmall hw hwt hnw hnt hnn hN).2.2.2.2.2.2.2.1
    have he := mul_le_mul_of_nonneg_left hex hκ.le
    nlinarith
  have hq : LogPowerRate (fun d => (q d:ℝ)) (κ/3) := by
    simpa only [q,NNReal.coe_mul] using (hlip.const_mul (centeringRowBudget n:ℝ)).mono hmargin
  have hz := centeringEnvelopes_calibrated hκ hJ hb ht htsmall hw hwt hnw hnt hnn hN hα hq hE
  have hze := hz.1.eventually_small (show 2*κ*J<2*κ*(J+8) by nlinarith)
  have hme := hz.2.eventually_small (show 2*κ*J<2*κ*(J+8) by nlinarith)
  have hle := hl.eventually_lt_const hκb (by norm_num : (0:ℝ)<1/2)
  have hc := (probabilityMeanLipschitz_rate hl contraction).eventually_lt_const hκb (by norm_num : (0:ℝ)<1/2)
  have hqe := hq.eventually_lt_const (by linarith) (by norm_num : (0:ℝ)<1/2)
  filter_upwards [hze,hme,hle,hc,hqe] with d hzd hmd hld hcd hqd
  refine ⟨(le_abs_self _).trans hld.le,?_,?_,(le_abs_self _).trans hzd, (le_abs_self _).trans hmd⟩
  · exact_mod_cast (le_abs_self _).trans hcd.le
  · exact_mod_cast (le_abs_self _).trans hqd.le
end LogConcaveSampling

end

end

end OAI
