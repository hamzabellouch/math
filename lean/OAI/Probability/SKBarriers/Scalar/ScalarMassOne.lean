import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarEndpoint

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarStep_one_spin (v : ℝ) :
    scalarStep 1 v scalarSpinTerminal = fun z => scalarSpinTerminal z+v^2/2 := by
  funext z
  have he (y : ℝ) : Real.exp (scalarSpinTerminal (z+v*y)) =
      Real.exp z*Real.exp (v*y)+Real.exp (-z)*Real.exp (-v*y) := by
    rw [scalarSpinTerminal,Real.exp_log (mul_pos (by norm_num) (Real.cosh_pos _)),Real.cosh_eq]
    rw [Real.exp_add,show -(z+v*y) = -z+(-v)*y by ring,Real.exp_add]
    ring
  have hm (a : ℝ) : (∫ y : ℝ, Real.exp (a*y) ∂gaussianReal 0 1) = Real.exp (a^2/2) := by
    simpa only [mgf,zero_mul,NNReal.coe_one,one_mul,zero_add] using
      congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) a
  simp only [scalarStep,gaussianStep,one_ne_zero,ite_false,positiveGaussianLogStep,one_mul,div_one]
  simp_rw [he]
  rw [integral_add ((integrable_exp_mul_gaussianReal v).const_mul (Real.exp z))
      ((integrable_exp_mul_gaussianReal (-v)).const_mul (Real.exp (-z))),
    integral_const_mul,integral_const_mul,hm v,hm (-v),neg_sq]
  have H : Real.exp z*Real.exp (v^2/2)+Real.exp (-z)*Real.exp (v^2/2) =
      (2*Real.cosh z)*Real.exp (v^2/2) := by rw [Real.cosh_eq]; ring
  rw [H,Real.log_mul (ne_of_gt (mul_pos (by norm_num) (Real.cosh_pos z))) (Real.exp_ne_zero _),Real.log_exp]
  rfl

theorem scalarStep_regular {f : ℝ → ℝ} (hf : BoundedDerivs f) (m v : ℝ) :
    BoundedDerivs (scalarStep m v f) := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ+v • ContinuousLinearMap.snd ℝ ℝ ℝ
  exact (hf.compCLM L).gaussianStep m

theorem scalarStep_add_const {f : ℝ → ℝ} (hf : BoundedDerivs f) (m v c : ℝ) :
    scalarStep m v (fun z => f z+c) = fun z => scalarStep m v f z+c := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ+v • ContinuousLinearMap.snd ℝ ℝ ℝ
  exact gaussianStep_add_prefix (hf.compCLM L) (fun _ => c) m

theorem scalarHierarchy_add_const (n : ℕ) (m v : Fin n → ℝ) (f : ℝ → ℝ)
    (hf : BoundedDerivs f) (c : ℝ) :
    scalarHierarchy n m v (fun z => f z+c) = fun z => scalarHierarchy n m v f z+c := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [scalarHierarchy,scalarStep_add_const hf]
    exact ih _ _ _ (scalarStep_regular hf _ _)

theorem scalar_quantile_terminal_shift (k : ℕ) (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q (Fin.last k) ≤ 1) :
    scalarHierarchy (k+1) (quantileMass k)
      (fun b => β*Real.sqrt (cumulativeGapMap k Q b))
      (scalarStep 1 (β*Real.sqrt (1-Q (Fin.last k))) scalarSpinTerminal) 0 =
      scalarHierarchy (k+1) (quantileMass k)
        (fun b => β*Real.sqrt (cumulativeGapMap k Q b)) scalarSpinTerminal 0+
      (β^2/2)*(1-Q (Fin.last k)) := by
  have hf : BoundedDerivs scalarSpinTerminal := scalarHierarchy_spin_regular 0 Fin.elim0 Fin.elim0
  rw [scalarStep_one_spin,scalarHierarchy_add_const _ _ _ _ hf]
  rw [mul_pow,Real.sq_sqrt (sub_nonneg.mpr hQ)]
  ring
end SK.Analytic

end
end

end

end OAI
