import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightSourceDeriv
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightSupportZero

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic
open scoped FourierTransform SchwartzMap

def historyDerivativeCount (l : ℕ) : ℝ := (2:ℝ)^(l+1)-1

@[simp] theorem historyDerivativeCount_zero : historyDerivativeCount 0 = 1 := by
  norm_num [historyDerivativeCount]

theorem historyDerivativeCount_succ (l : ℕ) :
    historyDerivativeCount (l+1) = 1+2*historyDerivativeCount l := by
  unfold historyDerivativeCount
  rw [pow_succ (2:ℝ) (l+1)]
  ring

theorem historyDerivativeCount_nonneg (l : ℕ) : 0 ≤ historyDerivativeCount l := by
  induction l with
  | zero => simp only [historyDerivativeCount_zero]; norm_num
  | succ l ih => rw [historyDerivativeCount_succ]; positivity

theorem leafFourierBound_one_le : 1 ≤ leafFourierBound := by
  unfold leafFourierBound
  have h := apply_nonneg (SchwartzMap.seminorm ℝ 0 0) (𝓕 SchwartzCutoff.psi)
  linarith

theorem norm_deriv_cell_mul_conj_le (c : ℝ → ℝ) (f g : ℝ → ℂ)
    (hc : DifferentiableAt ℝ c 0) (hf : DifferentiableAt ℝ f 0) (hg : DifferentiableAt ℝ g 0)
    (A D C : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hc0 : |c 0| ≤ 1) (hcd : |deriv c 0| ≤ D)
    (hf0 : ‖f 0‖ ≤ A) (hg0 : ‖g 0‖ ≤ A)
    (hfd : ‖deriv f 0‖ ≤ A*C*D) (hgd : ‖deriv g 0‖ ≤ A*C*D) :
    ‖deriv (fun t => (c t:ℂ)*(f t*star (g t))) 0‖ ≤ A^2*(1+2*C)*D := by
  rw [(hc.hasDerivAt.ofReal_comp.fun_mul (hf.hasDerivAt.fun_mul hg.hasDerivAt.star)).deriv]
  calc
    _ ≤ ‖((deriv c 0:ℝ):ℂ)*(f 0*star (g 0))‖ +
        ‖(c 0:ℂ)*(deriv f 0*star (g 0)+f 0*star (deriv g 0))‖ := norm_add_le _ _
    _ ≤ |deriv c 0| *(‖f 0‖*‖g 0‖)+|c 0| *(‖deriv f 0‖*‖g 0‖+‖f 0‖*‖deriv g 0‖) := by
      simp only [norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (by simpa only [norm_mul,norm_star] using norm_add_le (deriv f 0*star (g 0)) (f 0*star (deriv g 0))) (abs_nonneg _))
    _ ≤ D*(A*A)+1*((A*C*D)*A+A*(A*C*D)) := by
      apply add_le_add
      · exact mul_le_mul hcd (mul_le_mul hf0 hg0 (norm_nonneg _) hA) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hD
      · exact mul_le_mul hc0 (add_le_add
          (mul_le_mul hfd hg0 (norm_nonneg _) (mul_nonneg (mul_nonneg hA hC) hD))
          (mul_le_mul hf0 hgd (norm_nonneg _) hA))
          (add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _))) zero_le_one
    _ = _ := by ring

namespace HistorySymbolicEncoding
open Construction Characters.RationalHistory HistorySymbolicState
variable {ι : Type*}

def TreeDerivativeBudget (outside : List ℕ) (x : ι → ℝ) (K B : ℝ) :
    {l : ℕ} → (h : History l) → TreeExpr ι h → Prop
  | _, .leaf a, e => (e.periodExpr outside).RelativeControl x K ∧
      (e.periodExpr outside).logBudget K ≤ B ∧ (a.small.length:ℝ) ≤ B
  | _, .node _ _ _ _ _ left right, e =>
      (treeRoot left e.2.1).plus.RelativeControl x K ∧
      (treeRoot left e.2.1).plus.logBudget K ≤ B ∧
      TreeDerivativeBudget outside x K B left e.2.1 ∧
      TreeDerivativeBudget outside x K B right e.2.2

def sourceDerivativeRate (B Dφ Dc : ℝ) : ℝ :=
  B*(leafProfileBound (𝓕 SchwartzCutoff.psi)+2*Dφ+Dc)

theorem sourceDerivativeRate_nonneg {B Dφ Dc : ℝ}
    (hB : 0 ≤ B) (hφ : 0 ≤ Dφ) (hc : 0 ≤ Dc) : 0 ≤ sourceDerivativeRate B Dφ Dc :=
  mul_nonneg hB (add_nonneg (add_nonneg (leafProfileBound_pos _).le (mul_nonneg (by norm_num) hφ)) hc)

theorem leaf_source_derivative_rate (k : ℕ) (Δ E B Dφ Dc P n : ℝ)
    (hB : 0 ≤ B) (hφ : 0 ≤ Dφ) (hc : 0 ≤ Dc)
    (_hP : 0 ≤ P) (hPB : P ≤ B) (_hn : 0 ≤ n) (hnB : n ≤ B) :
    Real.exp ((-Δ+(E+12+4*(k:ℝ)))/2) *
      (leafProfileBound (𝓕 SchwartzCutoff.psi)*P+leafFourierBound*(2*Dφ*n)) ≤
      sourceLeafAmplitude k Δ E * sourceDerivativeRate B Dφ Dc := by
  have hC := leafFourierBound_one_le
  have hprof := (leafProfileBound_pos (𝓕 SchwartzCutoff.psi)).le
  have hfirst : leafProfileBound (𝓕 SchwartzCutoff.psi)*P ≤
      leafFourierBound*leafProfileBound (𝓕 SchwartzCutoff.psi)*B := by
    calc
      _ ≤ leafProfileBound (𝓕 SchwartzCutoff.psi)*B := mul_le_mul_of_nonneg_left hPB hprof
      _ ≤ _ := by nlinarith [mul_nonneg hprof hB]
  have hsecond : leafFourierBound*(2*Dφ*n) ≤ leafFourierBound*(2*Dφ*B) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnB (mul_nonneg (by norm_num) hφ)) leafFourierBound_pos.le
  have hextra : 0 ≤ leafFourierBound*B*Dc := mul_nonneg (mul_nonneg leafFourierBound_pos.le hB) hc
  unfold sourceLeafAmplitude sourceDerivativeRate
  nlinarith [Real.exp_pos ((-Δ+(E+12+4*(k:ℝ)))/2),
    mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (Real.exp_pos ((-Δ+(E+12+4*(k:ℝ)))/2)).le]

end HistorySymbolicEncoding
end Ostmann.Arithmetic

end

end OAI
