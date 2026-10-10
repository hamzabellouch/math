import Mathlib
import OAI.Probability.LogConcave.Sampling.VelocityJointLip
import OAI.Probability.LogConcave.Sampling.NumericalLayerCount

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter Set MeasureTheory Quadrature
open scoped Topology Classical BigOperators NNReal

theorem velocityNormalizedBudget_calibrated (k n N : ℕ) (Ap Ah Lp : ℝ≥0) (C J₀ D : ℝ)
    {lam : ℕ → ℝ≥0} {r T : ℕ → ℝ} {κ J b t w : ℝ}
    (hκ : 0<κ) (hJ : 1≤J) (hb : 1/2≤b) (ht : 0<t) (htsmall : t<1/100)
    (hw : 0<w) (hwt : w<t)
    (hnw : J+10<w*((n:ℝ)-3)) (hnt : J+10<t*((n:ℝ)-3))
    (hnn : 4*(J+10)<(n:ℝ)) (hN : 10*(J+2)≤(N:ℝ))
    (hl : LogPowerRate (fun d => (lam d:ℝ)*(r d)^2) (κ*b))
    (hT0 : ∀ᶠ d : ℕ in atTop,0<T d) (hT1 : ∀ᶠ d : ℕ in atTop,T d<1)
    (hRT : ∀ᶠ d : ℕ in atTop,((d:ℝ)^(-(κ*t)))^2≤1-(T d)^2)
    (hsmall : ∀ᶠ d : ℕ in atTop,(d:ℝ)^(-(κ*w))≤Real.log 2)
    (hlarge : ∀ᶠ d : ℕ in atTop,(d:ℝ)^(-(κ*w))≤logMeshLength (T d)) :
    LogPowerRate (fun d => velocityNormalizedBudget d k n n N (lam d) Ap Ah Lp
      (r d) ((d:ℝ)^(-(κ*t))) (T d) ((d:ℝ)^(-(κ*w))) ((d:ℝ)^(-(κ*(4*t)))) C J₀ D)
        (2*κ*(J+8)) := by
  obtain ⟨hp,hh,hiter,ha₁,ha₂,hv₁,hv₂,hlip,hbeta,hcq,hniter,hmq⟩ :=
    numerical_exponent_margins hJ hb ht htsmall hw hwt hnw hnt hnn hN
  have hB := kernelNormalizedTerm_rate k (n+1) N Ap Ah Lp (a:=κ*t) (b:=κ*w) (c:=κ*(4*t)) (e:=κ*(J+10)) (n:ℝ) hl
    (show κ*(J+10)≤((n+1:ℕ)+1:ℝ)*(κ*w) by
      have he := mul_le_mul_of_nonneg_left hp hκ.le
      push_cast; nlinarith)
    (show κ*(J+10)≤((n+1:ℕ)+1:ℝ)*(κ*(4*t)-2*(κ*t)) by
      have he := mul_le_mul_of_nonneg_left hh hκ.le
      push_cast; nlinarith)
    (show κ*(J+10)≤N*(κ*b) by
      have he := mul_le_mul_of_nonneg_left hiter hκ.le
      nlinarith)
  have hA := kernelActionNormalizedBudget_rate k (n+1) n N Ap Ah Lp C J₀ hB
    (show 2*κ*(J+9)≤2*(κ*(J+10)-κ*(4*t)) by
      have he := mul_le_mul_of_nonneg_left ha₁ hκ.le
      nlinarith)
    (show 2*κ*(J+9)≤2*(κ*(4*t))*n-4*(κ*t)*((n:ℝ)+1) by
      have he := mul_le_mul_of_nonneg_left ha₂ hκ.le
      nlinarith)
  obtain ⟨Dq,hDq,hDqu⟩ := exists_basisDerivative_budget (probabilityNodes (n+1))
  have hW := terminalQuadratureWeight_rate n Dq (by linarith) hDqu (κ*t) (κ*w)
    hT0 hT1 hRT hsmall hlarge
  exact velocityNormalizedBudget_rate k n n N Ap Ah Lp C J₀ D hW hA
    (logMeshLength_rate (κ*t) hT0 hT1 hRT)
    (by have he := mul_le_mul_of_nonneg_left hv₁ hκ.le; nlinarith)
    (by have he := mul_le_mul_of_nonneg_left hv₂ hκ.le; nlinarith)

lemma velocityJointLip_rate (n m : ℕ) (A : ℝ≥0)
    {lam : ℕ → ℝ≥0} {r s T : ℕ → ℝ} {b c u : ℝ}
    (hbc : 0≤b+c) (hr : ∀ᶠ d : ℕ in atTop,0<r d) (hs : ∀ᶠ d : ℕ in atTop,0<s d)
    (hT0 : ∀ᶠ d : ℕ in atTop,0<T d) (hT1 : ∀ᶠ d : ℕ in atTop,T d<1)
    (hW : LogPowerRate (fun d => ∑v,|terminalQuadratureWeight (T d) ((d:ℝ)^(-b)) n v|) (-b))
    (hα : LogPowerRate (fun d => (lam d:ℝ)*r d/s d) u) :
    LogPowerRate (fun d => (velocityJointLip n m A (lam d) (r d) (T d)
      ((d:ℝ)^(-b)) ((d:ℝ)^(-c)) (s d):ℝ)) (u-b-c) := by
  have hS := (LogPowerRate.inv_power c).const_mul (∑i,|derivativeWeight (angleNodes m) i|)
  have hQS := (hW.const_mul (16*(A:ℝ))).mul hS
  have h1 := (LogPowerRate.const 1).mono (show -b+-c≤0 by linarith)
  have he := (hα.const_mul (Real.pi^2)).mul (hQS.add h1)
  have he' : LogPowerRate (fun d => Real.pi^2*((lam d:ℝ)*r d/s d)*
      (16*(A:ℝ)*(∑v,|terminalQuadratureWeight (T d) ((d:ℝ)^(-b)) n v|)*
        ((∑i,|derivativeWeight (angleNodes m) i|)/(d:ℝ)^(-c))+1)) (u-b-c) := by
    convert! he using 1
    first | (simp only [div_eq_mul_inv]) | ring
  apply LogPowerRate.of_le he'
  · exact Eventually.of_forall (fun d => NNReal.coe_nonneg _)
  · filter_upwards [hr,hs,hT0,hT1,eventually_ge_atTop (1:ℕ)] with d hdr hds hdT0 hdT1 hd
    have hd0 : (0:ℝ)<d := by exact_mod_cast hd
    exact velocityJointLip_coefficient hdr hds (Real.rpow_pos_of_pos hd0 (-c)) hdT0 hdT1 (lam d) A n m

namespace LogPowerRate
lemma eventually_lt_const {f : ℕ → ℝ} {a C : ℝ} (hf : LogPowerRate f a)
    (ha : 0<a) (hC : 0<C) : ∀ᶠ d : ℕ in atTop, |f d|<C := by
  have he := hf.eventually_small (show a/2<a by linarith)
  have ht := (tendsto_rpow_neg_atTop (show 0<a/2 by linarith)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hb := ht.eventually (gt_mem_nhds hC)
  filter_upwards [he,hb] with d hd hb
  exact hd.trans_lt hb
end LogPowerRate
end LogConcaveSampling

end

end

end OAI
