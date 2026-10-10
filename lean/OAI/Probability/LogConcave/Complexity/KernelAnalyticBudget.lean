import Mathlib
import OAI.Probability.LogConcave.Numerics.OrdinaryDerivativeWeight
import OAI.Probability.LogConcave.Sampling.TerminalActionChainQuotient

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature RMSIntegral
open scoped Classical BigOperators NNReal

lemma terminalDerivativeBudget_polylog (n d : ℕ) (lam : ℝ≥0) (r : ℝ) :
    terminalDerivativeBudget n d lam r≤(lam:ℝ)*r^2*
      (Real.exp (Real.pi^2/4)*(TensorSum.terminalQ n).val.logCoefficient 0 2)*
      (1+Real.log ((d:ℝ)+1))^((TensorSum.terminalQ n).val.logDegree 0) := by
  have he := mul_le_mul_of_nonneg_left
    ((TensorSum.terminalQ n).val.momentBudget_polylog d 0 2)
    (show 0≤r*((lam:ℝ)*r)*Real.exp (Real.pi^2/4) by
      have hh : 0≤r*((lam:ℝ)*r) := by nlinarith [sq_nonneg r,lam.coe_nonneg]
      positivity)
  convert! he using 1
  ring

lemma logMeshCount_mul_step {T h : ℝ} (hT0 : 0<T) (hT1 : T<1)
    (hh : 0<h) (hL : h≤logMeshLength T) :
    (logMeshCount T h:ℝ)*h≤2*logMeshLength T := by
  have he := mul_lt_mul_of_pos_right (logMeshCount_bound hT0 hT1 hh) hh
  have hh0 := ne_of_gt hh
  field_simp at he
  nlinarith

def kernelAnalyticBudget (n d : ℕ) (lam : ℝ≥0) (r T h D : ℝ) : ℝ :=
  32*(1+D^2+(∑i,|zeroHermiteWeight (probabilityNodes (n+1)) 0 i|)^2)*
    (2*logMeshLength T*terminalDerivativeBudget (n+1) d lam r*2^(n+1)*h^n)^2*d

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T h : ℝ} (hr : 0<r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1)

include hlam in

theorem terminalQuadrature_kernel_rms (hd : 1≤d) (n : ℕ) (D : ℝ) (hD : 1≤D)
    (hDu : ∀t∈Icc (0:ℝ) 1,∑i,|basisDerivative (probabilityNodes (n+1)) i t|≤D)
    (hh : 0<h) (hs : h≤Real.log 2) (hL : h≤logMeshLength T) :
    let J := terminalActionChain hF x hr hl hT0 hT1
    let μ := (interpolationLaw F x r T).prod (stdGaussian (Point d))
    let err := fun z => (∑s,terminalQuadratureWeight T h n s •
      J 0 (probabilityNodeTime T h (n+1) s,z))-
        r • (centeringKernel hF x hr hl hT0.le hT1 z.1).adjoint z.2
    Integrable (fun z => ‖err z‖^2) μ ∧
      (∫z,‖err z‖^2 ∂μ)≤kernelAnalyticBudget n d lam r T h D := by
  dsimp only
  have he := terminalQuadrature_analytic_rms hF x hr hlam hl hT0 hT1 hd n D hD hDu hh hs hL
  dsimp only at he
  simp_rw [terminalActionChain_integral hF x hr hlam hl hT0 hT1,norm_sub_rev] at he
  refine ⟨he.1,he.2.trans ?_⟩
  have hN := logMeshCount_mul_step hT0 hT1 hh hL
  have hmul := mul_le_mul_of_nonneg_right hN
    (show 0≤terminalDerivativeBudget (n+1) d lam r*2^(n+1)*h^n from
      mul_nonneg (mul_nonneg (terminalDerivativeBudget_nonneg _ _ _ _) (by positivity)) (by positivity))
  have hsq := pow_le_pow_left₀
    (show 0≤(logMeshCount T h:ℝ)*h*(terminalDerivativeBudget (n+1) d lam r*2^(n+1)*h^n) by
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hh.le)
        (by positivity [terminalDerivativeBudget_nonneg (n+1) d lam r])) hmul 2
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq
      (show 0≤32*(1+D^2+(∑i,|zeroHermiteWeight (probabilityNodes (n+1)) 0 i|)^2) by positivity))
    (Nat.cast_nonneg (α:=ℝ) d)
  convert! hscaled using 1 <;> (try dsimp only [kernelAnalyticBudget]) <;> (try simp only [mul_pow,pow_succ]) <;> first | rfl | ring
end LogConcaveSampling

end

end

end OAI
