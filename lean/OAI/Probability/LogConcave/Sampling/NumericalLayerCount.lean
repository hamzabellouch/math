import Mathlib
import OAI.Probability.LogConcave.Complexity.KernelAnalyticNormalizedBudget

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter Set MeasureTheory Quadrature
open scoped Topology Classical BigOperators NNReal

lemma probabilityNormalizedTerm_rate (k n : ℕ) (b : ℝ) :
    LogPowerRate (fun d => probabilityNormalizedTerm d k n ((d:ℝ)^(-b))) ((n+1)*b) := by
  have he := (LogPowerRate.log.pow k).mul (((LogPowerRate.power b).const_mul 2).pow (n+1))
  simpa only [mul_zero,zero_add,Nat.cast_add,Nat.cast_one,probabilityNormalizedTerm,dimensionLog] using he

lemma harmonicNormalizedTerm_rate (n : ℕ) (a c z : ℝ) :
    LogPowerRate (fun d => harmonicNormalizedTerm n ((d:ℝ)^(-a)) (((d:ℝ)^(-c))*z))
      ((n+1)*(c-2*a)) := by
  have he := (((((LogPowerRate.power c).mul_const z).abs.pow (n+1)).div_const (n.factorial:ℝ)).const_mul 4).mul
    ((LogPowerRate.inv_power a).pow (2*(n+1)))
  have he' := he.mul_const (Real.sqrt (harmonicMeanBudget (n+1)))
  convert! he' using 1
  first | rfl | (push_cast; ring)

lemma kernelNormalizedTerm_rate (k n N : ℕ) (Ap Ah Lp : ℝ≥0)
    {lam : ℕ → ℝ≥0} {r : ℕ → ℝ} {a b c e u : ℝ} (z : ℝ)
    (hl : LogPowerRate (fun d => (lam d:ℝ)*(r d)^2) u)
    (heP : e≤(n+1)*b) (heH : e≤(n+1)*(c-2*a)) (heN : e≤N*u) :
    LogPowerRate (fun d => kernelNormalizedTerm d k n N (lam d) Ap Ah Lp
      (r d) ((d:ℝ)^(-a)) ((d:ℝ)^(-b)) (((d:ℝ)^(-c))*z)) e := by
  exact ((probabilityNormalizedTerm_rate k n b).mono heP).add
    ((harmonicNormalizedTerm_rate n a c z).mono heH) |>.add
      (((hl.const_mul (numericalContractionCoefficient Ap Ah Lp)).pow N).mono heN)

lemma kernelActionNormalizedBudget_rate (k n m N : ℕ) (Ap Ah Lp : ℝ≥0)
    {lam : ℕ → ℝ≥0} {r : ℕ → ℝ} {a b c e u : ℝ} (C J : ℝ)
    (hB : LogPowerRate (fun d => kernelNormalizedTerm d k n N (lam d) Ap Ah Lp
      (r d) ((d:ℝ)^(-a)) ((d:ℝ)^(-b)) (((d:ℝ)^(-c))*m)) u)
    (heB : e≤2*(u-c)) (heA : e≤2*c*m-4*a*(m+1)) :
    LogPowerRate (fun d => kernelActionNormalizedBudget d k n m N (lam d) Ap Ah Lp
      (r d) ((d:ℝ)^(-a)) ((d:ℝ)^(-b)) ((d:ℝ)^(-c)) C J) e := by
  let S := fun d : ℕ => (∑i,|derivativeWeight (angleNodes m) i|)/(d:ℝ)^(-c)
  have hS : LogPowerRate S (-c) := by
    simpa only [S,div_eq_mul_inv] using (LogPowerRate.inv_power c).const_mul
      (∑i,|derivativeWeight (angleNodes m) i|)
  have hfirst := (((hS.const_mul ((numericalContractionCoefficient Ap Ah Lp+1)*
    numericalErrorCoefficient C J)).mul hB).pow 2).const_mul 600
  have hfirst' : LogPowerRate (fun d => 600*((numericalContractionCoefficient Ap Ah Lp+1)*
      numericalErrorCoefficient C J*S d*kernelNormalizedTerm d k n N (lam d) Ap Ah Lp
        (r d) ((d:ℝ)^(-a)) ((d:ℝ)^(-b)) (((d:ℝ)^(-c))*m))^2) e := by
    apply hfirst.mono
    push_cast
    linarith
  have hp := (((LogPowerRate.power c).mul_const (m:ℝ)).pow (m+1)).div_const (m.factorial:ℝ)
  have hsecond := (((((hS.pow 2).const_mul 2).mul (hp.pow 2)).mul
    ((LogPowerRate.inv_power a).pow (4*(m+1)))).mul_const (harmonicCorrectionBudget (m+1)))
  have hsecond' : LogPowerRate (fun d => 2*(S d)^2*((((d:ℝ)^(-c))*m)^(m+1)/(m.factorial:ℝ))^2*
      (((d:ℝ)^(-a))⁻¹)^(4*(m+1))*harmonicCorrectionBudget (m+1)) e := by
    apply hsecond.mono
    push_cast
    nlinarith [heA]
  exact hfirst'.add hsecond'

lemma kernelAnalyticNormalizedBudget_rate (n : ℕ) (D b : ℝ) {T : ℕ → ℝ}
    (hT : LogPowerRate (fun d => logMeshLength (T d)) 0) :
    LogPowerRate (fun d => kernelAnalyticNormalizedBudget n d (T d) ((d:ℝ)^(-b)) D) (2*n*b) := by
  have he := (((((hT.const_mul 2).mul_const
      (Real.exp (Real.pi^2/4)*(TensorSum.terminalQ (n+1)).val.logCoefficient 0 2)).mul
        (LogPowerRate.log.pow ((TensorSum.terminalQ (n+1)).val.logDegree 0))).mul_const (2^(n+1))).mul
          ((LogPowerRate.power b).pow n))
  have he' := (he.pow 2).const_mul
    (32*(1+D^2+(∑i,|zeroHermiteWeight (probabilityNodes (n+1)) 0 i|)^2))
  convert! he' using 1
  first | rfl | ring

lemma velocityNormalizedBudget_rate (k n m N : ℕ) (Ap Ah Lp : ℝ≥0)
    {lam : ℕ → ℝ≥0} {r T : ℕ → ℝ} {a b c e u : ℝ} (C J D : ℝ)
    (hW : LogPowerRate (fun d => ∑v,|terminalQuadratureWeight (T d) ((d:ℝ)^(-b)) n v|) (-b))
    (hA : LogPowerRate (fun d => kernelActionNormalizedBudget d k (n+1) m N (lam d) Ap Ah Lp
      (r d) ((d:ℝ)^(-a)) ((d:ℝ)^(-b)) ((d:ℝ)^(-c)) C J) u)
    (hT : LogPowerRate (fun d => logMeshLength (T d)) 0)
    (heA : e≤u-2*b) (heT : e≤2*n*b) :
    LogPowerRate (fun d => velocityNormalizedBudget d k n m N (lam d) Ap Ah Lp
      (r d) ((d:ℝ)^(-a)) (T d) ((d:ℝ)^(-b)) ((d:ℝ)^(-c)) C J D) e := by
  have he := ((hW.pow 2).const_mul 2).mul hA
  apply (he.mono (by push_cast; linarith)).add
    (((kernelAnalyticNormalizedBudget_rate n D b hT).const_mul 2).mono heT)
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling

def numericalLayerCount (J : ℝ) : ℕ := ⌈10*(J+2)⌉₊

lemma numericalLayerCount_bound (J : ℝ) : 10*(J+2)≤(numericalLayerCount J:ℝ) := Nat.le_ceil _

lemma exists_numerical_order {J t w : ℝ} (ht : 0<t) (hw : 0<w) :
    ∃n : ℕ, w*((n:ℝ)-3)>J+10 ∧ t*((n:ℝ)-3)>J+10 ∧ (n:ℝ)>4*(J+10) := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max (max (3+(J+10)/w) (3+(J+10)/t)) (4*(J+10)))
  have h₁ := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have h₂ := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have h₃ := lt_of_le_of_lt (le_max_right _ _) hn
  refine ⟨n,?_,?_,h₃⟩
  · have hh : (J+10)/w<(n:ℝ)-3 := by linarith
    have he := (div_lt_iff₀ hw).mp hh
    nlinarith
  · have hh : (J+10)/t<(n:ℝ)-3 := by linarith
    have he := (div_lt_iff₀ ht).mp hh
    nlinarith

theorem numerical_exponent_margins {J b t w : ℝ} {n N : ℕ}
    (hJ : 1≤J) (hb : 1/2≤b) (_ : 0<t) (htsmall : t<1/100)
    (hw : 0<w) (hwt : w<t)
    (hnw : J+10<w*((n:ℝ)-3)) (hnt : J+10<t*((n:ℝ)-3))
    (hnn : 4*(J+10)<(n:ℝ)) (hN : 10*(J+2)≤(N:ℝ)) :
    J+10≤((n:ℝ)+2)*w ∧ J+10≤((n:ℝ)+2)*(4*t-2*t) ∧ J+10≤N*b ∧
    2*(J+9)≤2*((J+10)-4*t) ∧ 2*(J+9)≤2*(4*t)*n-4*t*((n:ℝ)+1) ∧
    2*(J+8)≤2*(J+9)-2*w ∧ 2*(J+8)≤2*n*w ∧
    1/3≤b-w-4*t ∧ 0≤2*b-4*t ∧
    2*(J+8)≤((n:ℝ)+2)*(2*b-4*t) ∧ J+8≤(N:ℝ)/3 ∧
    2*(J+8)≤2*b+((n:ℝ)+1)*(2*b-4*t) := by
  have hn0 : (0:ℝ)≤n := Nat.cast_nonneg n
  have hN0 : (0:ℝ)≤N := Nat.cast_nonneg N
  have hNb : (N:ℝ)/2≤N*b := by nlinarith [mul_nonneg hN0 (sub_nonneg.mpr hb)]
  have hβ : 1/2≤2*b-4*t := by linarith
  have hnβ : ((n:ℝ)+2)/2≤((n:ℝ)+2)*(2*b-4*t) := by
    nlinarith [mul_nonneg (show 0≤(n:ℝ)+2 by positivity) (sub_nonneg.mpr hβ)]
  have hnβ' : ((n:ℝ)+1)/2≤((n:ℝ)+1)*(2*b-4*t) := by
    nlinarith [mul_nonneg (show 0≤(n:ℝ)+1 by positivity) (sub_nonneg.mpr hβ)]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> nlinarith

lemma numerical_t_small {K : ℕ} {t : ℝ} (hK : 2≤K) (ht : 0<t)
    (h : 40*((K:ℝ)+2)*t<1/4) : t<1/100 := by
  have hK' : (2:ℝ)≤K := by exact_mod_cast hK
  nlinarith
end LogConcaveSampling

end

end

end OAI
