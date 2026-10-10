import Mathlib
import OAI.Probability.LogConcave.Numerics.TwoendsContinuous
import OAI.Probability.LogConcave.Complexity.KernelActionNormalizedBudget

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators NNReal

def kernelAnalyticNormalizedBudget (n d : ℕ) (T h D : ℝ) : ℝ :=
  32*(1+D^2+(∑i,|zeroHermiteWeight (probabilityNodes (n+1)) 0 i|)^2)*
    (2*logMeshLength T*(Real.exp (Real.pi^2/4)*(TensorSum.terminalQ (n+1)).val.logCoefficient 0 2)*
      (1+Real.log ((d:ℝ)+1))^((TensorSum.terminalQ (n+1)).val.logDegree 0)*2^(n+1)*h^n)^2

lemma kernelAnalyticNormalizedBudget_nonneg (n d : ℕ) (T h D : ℝ) :
    0≤kernelAnalyticNormalizedBudget n d T h D := by
  unfold kernelAnalyticNormalizedBudget
  positivity

lemma kernelAnalyticBudget_normalized {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (lam : ℝ≥0) (r D : ℝ) {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0≤h) (n : ℕ) :
    kernelAnalyticBudget n d lam r T h D≤
      (((lam:ℝ)*r^2)*circuitD F x)^2*kernelAnalyticNormalizedBudget n d T h D := by
  have hp := terminalDerivativeBudget_polylog (n+1) d lam r
  have ht := terminalDerivativeBudget_nonneg (n+1) d lam r
  have hlen := (logMeshLength_pos hT0 hT1).le
  have hd := circuitD_dimension F x
  unfold kernelAnalyticBudget kernelAnalyticNormalizedBudget
  calc
    _ ≤ 32*(1+D^2+(∑i,|zeroHermiteWeight (probabilityNodes (n+1)) 0 i|)^2)*
      (2*logMeshLength T*((lam:ℝ)*r^2*
        (Real.exp (Real.pi^2/4)*(TensorSum.terminalQ (n+1)).val.logCoefficient 0 2)*
        (1+Real.log ((d:ℝ)+1))^((TensorSum.terminalQ (n+1)).val.logDegree 0))*2^(n+1)*h^n)^2*
        (circuitD F x)^2 := by gcongr
    _ = _ := by ring

def velocityNormalizedBudget (d k n m N : ℕ) (lam Ap Ah Lp : ℝ≥0)
    (r R T h ψ C J D : ℝ) : ℝ :=
  2*(∑v,|terminalQuadratureWeight T h n v|)^2*
    kernelActionNormalizedBudget d k (n+1) m N lam Ap Ah Lp r R h ψ C J+
      2*kernelAnalyticNormalizedBudget n d T h D

lemma velocityNormalizedBudget_nonneg (d k n m N : ℕ) (lam Ap Ah Lp : ℝ≥0)
    (r R T h ψ C J D : ℝ) (hR : 0≤R) :
    0≤velocityNormalizedBudget d k n m N lam Ap Ah Lp r R T h ψ C J D := by
  unfold velocityNormalizedBudget
  positivity [kernelActionNormalizedBudget_nonneg d k (n+1) m N lam Ap Ah Lp r R h ψ C J hR,
    kernelAnalyticNormalizedBudget_nonneg n d T h D]

theorem velocityRmsBudget_normalized {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) (Ap Ah Lp : ℝ≥0) {r R T h ψ s C J D : ℝ}
    (hr : 0<r) (hr1 : r≤1) (hR : 0<R) (hT0 : 0<T) (hT1 : T<1)
    (hh : 0<h) (hψ : 0<ψ) (hs : 0<s) (hC : 0≤C) (hJ : 0≤J)
    (hl : (lam:ℝ)*r^2≤1/2) (hL : (lam:ℝ)*r≤1) (k n m N : ℕ) :
    (r*s)⁻¹^2*(2*((∑v,|terminalQuadratureWeight T h n v|)*
      (∑v,|terminalQuadratureWeight T h n v| *
        kernelActionRmsBudget F x lam Ap Ah Lp r R (probabilityNodeTime T h (n+1) v) h ψ C J k (n+1) m N))+
      2*kernelAnalyticBudget n d lam r T h D)≤
      (((lam:ℝ)*r/s)*circuitD F x)^2*
        velocityNormalizedBudget d k n m N lam Ap Ah Lp r R T h ψ C J D := by
  let Q := ∑v,|terminalQuadratureWeight T h n v|
  let E := kernelActionNormalizedBudget d k (n+1) m N lam Ap Ah Lp r R h ψ C J
  let B := (((lam:ℝ)*r^2)*circuitD F x)^2
  have hq : 0≤Q := by dsimp [Q]; positivity
  have hp (v : ProbabilityNode T h (n+1)) :
      kernelActionRmsBudget F x lam Ap Ah Lp r R (probabilityNodeTime T h (n+1) v) h ψ C J k (n+1) m N≤B*E := by
    have hv := probabilityNodeTime_mem hT0 hT1 hh (by omega : 0<n+1) v
    exact kernelActionRmsBudget_normalized hF x Ap Ah Lp hr.le hr1 hR hh.le hψ hC hJ hl hL
      hv.1 (hv.2.trans_lt hT1) k (n+1) m N
  have hw := weighted_uniform_upper (fun v => |terminalQuadratureWeight T h n v|) _
    (fun v => abs_nonneg _) hp
  have ha := kernelAnalyticBudget_normalized F x lam r D hT0 hT1 hh.le n
  have hb := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw hq) (by norm_num : (0:ℝ)≤2))
      (mul_le_mul_of_nonneg_left ha (by norm_num : (0:ℝ)≤2)))
    (sq_nonneg ((r*s)⁻¹))
  apply hb.trans_eq
  dsimp [Q,E,B,velocityNormalizedBudget]
  field_simp
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators NNReal

lemma square_root_two_budget {A B : ℝ} (hA : 0≤A) (hB : 0≤B) (q : ℝ) (N : ℕ) :
    (2*Real.sqrt A+q^N*Real.sqrt B)^2≤8*A+2*q^(2*N)*B := by
  have hsA := Real.sq_sqrt hA
  have hsB := Real.sq_sqrt hB
  have he : q^(2*N)*B=(q^N*Real.sqrt B)^2 := by
    rw [show 2*N=N*2 by omega,pow_mul,mul_pow,hsB]
  nlinarith [sq_nonneg (2*Real.sqrt A-q^N*Real.sqrt B)]

def centerStateQuadratureEnvelope (n : ℕ) (α R : ℝ) : ℝ :=
  8*(singleCellBasisBudget n)^2*(α^2*(R⁻¹)^4)^(n+2)*centeringStateBudget (n+2)
def centerInitialEnvelope (α R : ℝ) : ℝ :=
  2*(α^2*(R⁻¹)^4)*centeringStateBudget 1

def centerStateEnvelope (n N : ℕ) (α R q E : ℝ) : ℝ :=
  8*(2*(centeringRowBudget n:ℝ)^2*α^2*E+2*centerStateQuadratureEnvelope n α R)+
    2*q^(2*N)*centerInitialEnvelope α R

def centerMeanEnvelope (n : ℕ) (α R Z : ℝ) : ℝ :=
  2*(centeringRowBudget n:ℝ)^2*(Real.pi^2/2)^2*α^2*Z+
    8*(singleCellBasisBudget n)^2*α^2*(α^2*(R⁻¹)^4)^(n+1)*centeringMeanBudget (n+1)

lemma centerStateQuadratureEnvelope_nonneg (n : ℕ) (α R : ℝ) :
    0≤centerStateQuadratureEnvelope n α R := by
  unfold centerStateQuadratureEnvelope
  positivity [centeringStateBudget_nonneg (n+2)]
lemma centerInitialEnvelope_nonneg (α R : ℝ) : 0≤centerInitialEnvelope α R := by
  unfold centerInitialEnvelope
  positivity [centeringStateBudget_nonneg 1]
lemma centerStateEnvelope_nonneg (n N : ℕ) (α R q E : ℝ) (hq : 0≤q) (hE : 0≤E) :
    0≤centerStateEnvelope n N α R q E := by
  unfold centerStateEnvelope
  positivity [centerStateQuadratureEnvelope_nonneg n α R,centerInitialEnvelope_nonneg α R]
lemma centerMeanEnvelope_nonneg (n : ℕ) (α R Z : ℝ) (hZ : 0≤Z) :
    0≤centerMeanEnvelope n α R Z := by
  unfold centerMeanEnvelope
  positivity [centeringMeanBudget_nonneg (n+1)]

lemma centeringStateQuadratureBudget_normalized {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (n : ℕ) (lam : ℝ≥0) (r R s : ℝ) :
    centeringStateQuadratureBudget n d lam r R s≤
      (circuitD F x)^2*centerStateQuadratureEnvelope n ((lam:ℝ)*r/s) R := by
  have hd := circuitD_dimension F x
  have hc := centeringStateBudget_nonneg (n+2)
  unfold centeringStateQuadratureBudget centerStateQuadratureEnvelope
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hd
    (show 0≤8*(singleCellBasisBudget n)^2*(((lam:ℝ)*r/s)^2*(R⁻¹)^4)^(n+2)*centeringStateBudget (n+2) by positivity)]

lemma centeringInitialBudget_normalized {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (lam : ℝ≥0) (r R s : ℝ) :
    centeringInitialBudget d lam r R s≤
      (circuitD F x)^2*centerInitialEnvelope ((lam:ℝ)*r/s) R := by
  have hd := circuitD_dimension F x
  have hc := centeringStateBudget_nonneg 1
  unfold centeringInitialBudget centerInitialEnvelope
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hd
    (show 0≤2*(((lam:ℝ)*r/s)^2*(R⁻¹)^4)*centeringStateBudget 1 by positivity)]

lemma centeringPicardBudget_normalized {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (n N : ℕ) (lam K : ℝ≥0) (r R s E : ℝ) (hE : 0≤E) :
    centeringPicardBudget n N d lam K r R s ((((lam:ℝ)*r/s)*circuitD F x)^2*E)≤
      (circuitD F x)^2*centerStateEnvelope n N ((lam:ℝ)*r/s) R (centeringRowBudget n*K:ℝ≥0) E := by
  have hQ := centeringStateQuadratureBudget_normalized F x n lam r R s
  have hI := centeringInitialBudget_normalized F x lam r R s
  unfold centeringPicardBudget
  apply (square_root_two_budget
    (by positivity [centeringStateQuadratureBudget_nonneg n d lam r R s])
    (by unfold centeringInitialBudget; positivity [centeringStateBudget_nonneg 1])
      (centeringRowBudget n*K:ℝ≥0) N).trans
  have hq : 0≤((centeringRowBudget n*K:ℝ≥0):ℝ)^(2*N) := by positivity
  have hQ' := mul_le_mul_of_nonneg_left hQ (by norm_num : (0:ℝ)≤16)
  have hI' := mul_le_mul_of_nonneg_left hI (show 0≤2*((centeringRowBudget n*K:ℝ≥0):ℝ)^(2*N) by positivity)
  unfold centerStateEnvelope
  nlinarith

lemma centeringMeanBudget_normalized {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (n : ℕ) (lam : ℝ≥0) (r R : ℝ) {s T Z : ℝ} (hs : 0<s) (hT0 : 0≤T) (hT1 : T≤1) (hZ : 0≤Z) :
    2*(centeringRowBudget n:ℝ)^2*((Real.pi^2/2)*T*((lam:ℝ)*r))^2*((circuitD F x)^2*Z)+
      2*centeringMeanQuadratureBudget n d lam r R s≤
    (s*circuitD F x)^2*centerMeanEnvelope n ((lam:ℝ)*r/s) R Z := by
  have hd := circuitD_dimension F x
  have hc := centeringMeanBudget_nonneg (n+1)
  have hT : T^2≤1 := by nlinarith
  have he₁ := mul_le_mul_of_nonneg_left hT
    (show 0≤2*(centeringRowBudget n:ℝ)^2*(Real.pi^2/2)^2*((lam:ℝ)*r)^2*(circuitD F x)^2*Z by positivity)
  have he₂ := mul_le_mul_of_nonneg_right hd
    (show 0≤8*(singleCellBasisBudget n)^2*((lam:ℝ)*r)^2*
      (((lam:ℝ)*r/s)^2*(R⁻¹)^4)^(n+1)*centeringMeanBudget (n+1) by positivity)
  have hid : (s*circuitD F x)^2*centerMeanEnvelope n ((lam:ℝ)*r/s) R Z=
      2*(centeringRowBudget n:ℝ)^2*(Real.pi^2/2)^2*((lam:ℝ)*r)^2*(circuitD F x)^2*Z+
        8*(singleCellBasisBudget n)^2*((lam:ℝ)*r)^2*
          (((lam:ℝ)*r/s)^2*(R⁻¹)^4)^(n+1)*centeringMeanBudget (n+1)*(circuitD F x)^2 := by
    unfold centerMeanEnvelope
    field_simp
  rw [hid]
  unfold centeringMeanQuadratureBudget
  nlinarith
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Filter Asymptotics
open scoped Topology

def dimensionLog (d : ℕ) : ℝ := 1+Real.log ((d:ℝ)+1)

lemma dimensionLog_nonneg (d : ℕ) : 0≤dimensionLog d := by
  have hh : 0≤Real.log ((d:ℝ)+1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) d])
  unfold dimensionLog
  linarith

lemma dimensionLog_isBigO_log : dimensionLog =O[atTop] (fun d : ℕ => Real.log (d:ℝ)) := by
  have ht : Tendsto (fun d : ℕ => (d:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : ∀ᶠ d : ℕ in atTop,1≤Real.log (d:ℝ) :=
    (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 1
  apply IsBigO.of_bound 3
  filter_upwards [eventually_ge_atTop (2:ℕ),hlog] with d hd hl
  have hd0 : (0:ℝ)<d := by exact_mod_cast (by omega : 0<d)
  have hd1 : (2:ℝ)≤d := by exact_mod_cast hd
  have ht : Real.log ((d:ℝ)+1)≤2*Real.log (d:ℝ) := by
    calc
      _ ≤ Real.log ((d:ℝ)^2) := Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [Real.log_pow]; norm_num
  rw [Real.norm_of_nonneg (dimensionLog_nonneg d),Real.norm_of_nonneg (by linarith : 0≤Real.log (d:ℝ))]
  unfold dimensionLog
  linarith

lemma dimensionLog_pow_isLittleO (k : ℕ) {s : ℝ} (hs : 0<s) :
    (fun d : ℕ => dimensionLog d^k) =o[atTop] (fun d : ℕ => (d:ℝ)^s) := by
  have hh := (isLittleO_log_rpow_rpow_atTop (k:ℝ) hs).comp_tendsto
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  simp only [Real.rpow_natCast,Function.comp_def] at hh
  exact (dimensionLog_isBigO_log.pow k).trans_isLittleO hh

theorem polylog_power_absorb (C : ℝ) (k : ℕ) {a b : ℝ} (hab : b<a) :
    ∀ᶠ d : ℕ in atTop, |C| *dimensionLog d^k*(d:ℝ)^(-a)≤(d:ℝ)^(-b) := by
  have hh := ((dimensionLog_pow_isLittleO k (sub_pos.mpr hab)).const_mul_left |C|).mul_isBigO
    (isBigO_refl (fun d : ℕ => (d:ℝ)^(-a)) atTop)
  have he : (fun d : ℕ => (d:ℝ)^(a-b)*(d:ℝ)^(-a)) =ᶠ[atTop]
      (fun d : ℕ => (d:ℝ)^(-b)) := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
    have hd0 : (0:ℝ)<d := by exact_mod_cast hd
    rw [←Real.rpow_add hd0]
    congr 1
    ring
  have hbnd := (hh.congr' Filter.EventuallyEq.rfl he).def (by norm_num : (0:ℝ)<1)
  filter_upwards [hbnd] with d hd
  simpa only [one_mul,Real.norm_of_nonneg (by positivity [dimensionLog_nonneg d] : 0≤|C| *dimensionLog d^k*(d:ℝ)^(-a)),
    Real.norm_of_nonneg (by positivity : 0≤(d:ℝ)^(-b))] using hd
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Filter Asymptotics
open scoped Topology

def LogPowerRate (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∃k : ℕ, f =O[atTop] (fun d => dimensionLog d^k*(d:ℝ)^(-a))

lemma dimensionLog_one_le (d : ℕ) : 1≤dimensionLog d := by
  unfold dimensionLog
  have h := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) d] : 1≤(d:ℝ)+1)
  linarith

namespace LogPowerRate

lemma congr {f g : ℕ → ℝ} {a : ℝ} (h : LogPowerRate f a) (he : f=ᶠ[atTop] g) : LogPowerRate g a := by
  obtain ⟨k,hk⟩ := h
  exact ⟨k,hk.congr' he Filter.EventuallyEq.rfl⟩

lemma mono {f : ℕ → ℝ} {a b : ℝ} (h : LogPowerRate f a) (hba : b≤a) : LogPowerRate f b := by
  obtain ⟨k,hk⟩ := h
  refine ⟨k,hk.trans (IsBigO.of_bound 1 ?_)⟩
  filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
  have hd1 : (1:ℝ)≤d := by exact_mod_cast hd
  have hd0 : (0:ℝ)<d := lt_of_lt_of_le zero_lt_one hd1
  simp only [one_mul,Real.norm_of_nonneg (by positivity [dimensionLog_nonneg d] :
    0≤dimensionLog d^k*(d:ℝ)^(-a)), Real.norm_of_nonneg (by positivity [dimensionLog_nonneg d] :
    0≤dimensionLog d^k*(d:ℝ)^(-b))]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)) (by positivity [dimensionLog_nonneg d])

lemma const (C : ℝ) : LogPowerRate (fun _ => C) 0 := by
  refine ⟨0,?_⟩
  simpa only [pow_zero,neg_zero,Real.rpow_zero,mul_one] using
    (isBigO_const_const C (by norm_num : (1:ℝ)≠0) atTop : (fun _ : ℕ => C)=O[atTop] (fun _ => (1:ℝ)))

lemma power (a : ℝ) : LogPowerRate (fun d => (d:ℝ)^(-a)) a := by
  refine ⟨0,?_⟩
  simpa only [pow_zero,one_mul] using (isBigO_refl (fun d : ℕ => (d:ℝ)^(-a)) atTop)

lemma log : LogPowerRate dimensionLog 0 := by
  refine ⟨1,?_⟩
  simpa only [pow_one,neg_zero,Real.rpow_zero,mul_one] using (isBigO_refl dimensionLog atTop)

lemma mul {f g : ℕ → ℝ} {a b : ℝ} (hf : LogPowerRate f a) (hg : LogPowerRate g b) :
    LogPowerRate (fun d => f d*g d) (a+b) := by
  obtain ⟨k,hk⟩ := hf
  obtain ⟨l,hl⟩ := hg
  refine ⟨k+l,(hk.mul hl).congr' Filter.EventuallyEq.rfl ?_⟩
  filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd
  rw [pow_add,neg_add,Real.rpow_add hd0]
  ring

lemma pow {f : ℕ → ℝ} {a : ℝ} (hf : LogPowerRate f a) (n : ℕ) :
    LogPowerRate (fun d => f d^n) (n*a) := by
  induction n with
  | zero => simpa using const 1
  | succ n ih =>
    have h := ih.mul hf
    simpa only [pow_succ,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using h

lemma const_mul {f : ℕ → ℝ} {a : ℝ} (hf : LogPowerRate f a) (C : ℝ) :
    LogPowerRate (fun d => C*f d) a := by
  simpa only [zero_add] using (const C).mul hf

lemma mul_const {f : ℕ → ℝ} {a : ℝ} (hf : LogPowerRate f a) (C : ℝ) :
    LogPowerRate (fun d => f d*C) a := by
  simpa only [add_zero] using hf.mul (const C)

lemma add {f g : ℕ → ℝ} {a : ℝ} (hf : LogPowerRate f a) (hg : LogPowerRate g a) :
    LogPowerRate (fun d => f d+g d) a := by
  obtain ⟨k,hk⟩ := hf
  obtain ⟨l,hl⟩ := hg
  have bound (i j : ℕ) : (fun d : ℕ => dimensionLog d^i*(d:ℝ)^(-a)) =O[atTop]
      (fun d => dimensionLog d^(i+j)*(d:ℝ)^(-a)) := by
    apply IsBigO.of_bound 1
    filter_upwards [] with d
    rw [one_mul,Real.norm_of_nonneg (by positivity [dimensionLog_nonneg d]),
      Real.norm_of_nonneg (by positivity [dimensionLog_nonneg d])]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (dimensionLog_one_le d) (by omega)) (by positivity)
  exact ⟨k+l,(hk.trans (bound k l)).add (hl.trans (by simpa only [Nat.add_comm] using bound l k))⟩

lemma of_le_abs {f g : ℕ → ℝ} {a : ℝ} (hg : LogPowerRate g a)
    (hfg : ∀ᶠ d in atTop, |f d|≤|g d|) : LogPowerRate f a := by
  obtain ⟨k,hk⟩ := hg
  exact ⟨k,(IsBigO.of_bound 1 (by simpa only [one_mul,Real.norm_eq_abs] using hfg)).trans hk⟩

lemma eventually_small {f : ℕ → ℝ} {a b : ℝ} (hf : LogPowerRate f a) (hba : b<a) :
    ∀ᶠ d in atTop, |f d|≤(d:ℝ)^(-b) := by
  obtain ⟨k,hk⟩ := hf
  obtain ⟨C,hC⟩ := hk.bound
  have hp := polylog_power_absorb C k hba
  filter_upwards [hC,hp] with d hd hp
  have hdn : 0≤dimensionLog d^k*(d:ℝ)^(-a) := by positivity [dimensionLog_nonneg d]
  rw [Real.norm_eq_abs,Real.norm_of_nonneg hdn] at hd
  calc
    _ ≤ C*(dimensionLog d^k*(d:ℝ)^(-a)) := hd
    _ ≤ |C| *(dimensionLog d^k*(d:ℝ)^(-a)) := mul_le_mul_of_nonneg_right (le_abs_self C) hdn
    _ ≤ _ := by simpa only [mul_assoc] using hp

end LogPowerRate
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Filter Asymptotics Set MeasureTheory Quadrature
open scoped Topology Classical BigOperators

namespace LogPowerRate
lemma abs {f : ℕ → ℝ} {a : ℝ} (hf : LogPowerRate f a) : LogPowerRate (fun d => |f d|) a := by
  exact of_le_abs hf (Eventually.of_forall (fun d => by simp))

lemma div_const {f : ℕ → ℝ} {a : ℝ} (hf : LogPowerRate f a) (C : ℝ) :
    LogPowerRate (fun d => f d/C) a := by
  simpa only [div_eq_mul_inv] using hf.mul_const C⁻¹

lemma of_le {f g : ℕ → ℝ} {a : ℝ} (hg : LogPowerRate g a)
    (hf : ∀ᶠ d : ℕ in atTop,0≤f d) (hfg : ∀ᶠ d : ℕ in atTop,f d≤g d) : LogPowerRate f a := by
  apply of_le_abs hg
  filter_upwards [hf,hfg] with d hd he
  rw [abs_of_nonneg hd,abs_of_nonneg (hd.trans he)]
  exact he

lemma inv_power (a : ℝ) : LogPowerRate (fun d => ((d:ℝ)^(-a))⁻¹) (-a) := by
  apply (power (-a)).congr
  filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
  have hd0 : (0:ℝ)≤d := Nat.cast_nonneg d
  rw [Real.rpow_neg hd0]

lemma log_nat : LogPowerRate (fun d : ℕ => Real.log (d:ℝ)) 0 := by
  apply of_le log
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
    exact Real.log_nonneg (by exact_mod_cast hd)
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
    have hp : (0:ℝ)<d := by exact_mod_cast hd
    have he := Real.log_le_log hp (by linarith : (d:ℝ)≤(d:ℝ)+1)
    unfold dimensionLog
    linarith

lemma log_power (a : ℝ) : LogPowerRate (fun d : ℕ => Real.log ((d:ℝ)^(-a))) 0 := by
  apply (log_nat.const_mul (-a)).congr
  filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
  rw [Real.log_rpow (by exact_mod_cast hd : (0:ℝ)<d)]
end LogPowerRate

lemma logMeshLength_le_scale {T R : ℝ} (hT0 : 0<T) (hT1 : T<1)
    (hR : 0<R) (hRT : R^2≤1-T^2) :
    logMeshLength T≤Real.log 2-2*Real.log R := by
  have hden : 0<1-T := by linarith
  have hRR : R^2/2≤1-T := by nlinarith
  have he := Real.log_le_log (by positivity : 0<R^2/2) hRR
  rw [Real.log_div (by positivity : R^2≠0) (by norm_num),Real.log_pow] at he
  unfold logMeshLength
  norm_num at he
  linarith

lemma logMeshLength_rate {T : ℕ → ℝ} (a : ℝ)
    (hT0 : ∀ᶠ d : ℕ in atTop,0<T d) (hT1 : ∀ᶠ d : ℕ in atTop,T d<1)
    (hRT : ∀ᶠ d : ℕ in atTop,((d:ℝ)^(-a))^2≤1-(T d)^2) :
    LogPowerRate (fun d => logMeshLength (T d)) 0 := by
  apply LogPowerRate.of_le ((LogPowerRate.const (Real.log 2)).add
    ((LogPowerRate.log_power a).const_mul (-2)))
  · filter_upwards [hT0,hT1] with d hd0 hd1
    exact (logMeshLength_pos hd0 hd1).le
  · filter_upwards [hT0,hT1,hRT,eventually_ge_atTop (1:ℕ)] with d hd0 hd1 hRT hd
    have hp : (0:ℝ)<d := by exact_mod_cast hd
    simpa only [sub_eq_add_neg,neg_mul] using
      logMeshLength_le_scale hd0 hd1 (Real.rpow_pos_of_pos hp (-a)) hRT

lemma terminalQuadratureWeight_rate (n : ℕ) (D : ℝ) (hD : 0≤D)
    (hDu : ∀t∈Icc (0:ℝ) 1,∑i,|basisDerivative (probabilityNodes (n+1)) i t|≤D)
    {T : ℕ → ℝ} (a b : ℝ)
    (hT0 : ∀ᶠ d : ℕ in atTop,0<T d) (hT1 : ∀ᶠ d : ℕ in atTop,T d<1)
    (hRT : ∀ᶠ d : ℕ in atTop,((d:ℝ)^(-a))^2≤1-(T d)^2)
    (hsmall : ∀ᶠ d : ℕ in atTop,(d:ℝ)^(-b)≤Real.log 2)
    (hlarge : ∀ᶠ d : ℕ in atTop,(d:ℝ)^(-b)≤logMeshLength (T d)) :
    LogPowerRate (fun d => ∑v,|terminalQuadratureWeight (T d) ((d:ℝ)^(-b)) n v|) (-b) := by
  have hlen := logMeshLength_rate a hT0 hT1 hRT
  have he := ((LogPowerRate.inv_power b).const_mul 4).mul
    ((LogPowerRate.const (∑i,|zeroHermiteWeight (probabilityNodes (n+1)) 0 i|)).add
      (((hlen.add (LogPowerRate.log_power b).abs).add (LogPowerRate.const (Real.log 4))).const_mul ((n+2)*D)))
  simp only [add_zero] at he
  apply LogPowerRate.of_le he
  · exact Eventually.of_forall (fun d => by positivity)
  · filter_upwards [hT0,hT1,hsmall,hlarge,eventually_ge_atTop (1:ℕ)] with d hd0 hd1 hs hl hd
    have hp : (0:ℝ)<d := by exact_mod_cast hd
    simpa only [div_eq_mul_inv] using terminalQuadratureWeight_sum hd0 hd1
      (Real.rpow_pos_of_pos hp (-b)) hs hl n D hD hDu
end LogConcaveSampling

end

end

end OAI
