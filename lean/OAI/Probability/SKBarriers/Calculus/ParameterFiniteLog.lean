import Mathlib
import OAI.Probability.SKBarriers.Calculus.ParameterAlgebra

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
section ParameterFiniteLog
variable {P E S : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype S] [Nonempty S]

omit [NormedSpace ℝ P] [NormedSpace ℝ E] in
theorem param_inv_finite_exp_growth (f : S → P × E → ℝ)
    (hf : ∀ s, ParamLinearGrowth (f s)) :
    ParamExpGrowth (fun z => (∑ s, Real.exp (f s z))⁻¹) := by
  classical
  let s₀ : S := Classical.arbitrary S
  apply ((hf s₀).exp_mul (-1)).of_norm_le zero_le_one
  intro z
  have hp : 0 < ∑ s, Real.exp (f s z) := Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have hs : Real.exp (f s₀ z) ≤ ∑ s, Real.exp (f s z) :=
    Finset.single_le_sum (fun s _ => (Real.exp_pos (f s z)).le) (Finset.mem_univ s₀)
  rw [one_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (inv_pos.2 hp),abs_of_pos (Real.exp_pos _),
    neg_one_mul,Real.exp_neg]
  exact (inv_le_inv₀ hp (Real.exp_pos _)).2 hs

omit [NormedSpace ℝ P] [NormedSpace ℝ E] in
theorem param_log_finite_exp_linear (f : S → P × E → ℝ)
    (hf : ∀ s, ParamLinearGrowth (f s)) :
    ParamLinearGrowth (fun z => Real.log (∑ s, Real.exp (f s z))) := by
  classical
  intro R
  choose C hC hb using fun s => hf s R
  let D := ∑ s, C s
  let N : ℝ := Fintype.card S
  have hD : 0 ≤ D := Finset.sum_nonneg (fun s _ => hC s)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos (α := S)
  refine ⟨D+|Real.log N|,by positivity,?_⟩
  intro p e hp
  let A := D*(1+‖e‖)
  let Z := ∑ s, Real.exp (f s (p,e))
  have hz : 0 < Z := Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have hh s : |f s (p,e)| ≤ A := by
    apply (hb s p e hp).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact Finset.single_le_sum (fun t _ => hC t) (Finset.mem_univ s)
  have hu' : Z ≤ N*Real.exp A := by
    calc
      Z ≤ ∑ _ : S, Real.exp A := Finset.sum_le_sum (fun s _ =>
        Real.exp_le_exp.2 ((le_abs_self _).trans (hh s)))
      _ = N*Real.exp A := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,N]
  let s₀ : S := Classical.arbitrary S
  have hl' : Real.exp (-A) ≤ Z := by
    calc
      _ ≤ Real.exp (f s₀ (p,e)) := Real.exp_le_exp.2 (abs_le.1 (hh s₀)).1
      _ ≤ Z := Finset.single_le_sum (fun s _ => (Real.exp_pos (f s (p,e))).le) (Finset.mem_univ s₀)
  have hu := Real.log_le_log hz hu'
  have hl := Real.log_le_log (Real.exp_pos _) hl'
  rw [Real.log_mul hN.ne' (Real.exp_pos _).ne',Real.log_exp] at hu
  rw [Real.log_exp] at hl
  change |Real.log Z| ≤ (D+|Real.log N|)*(1+‖e‖)
  apply abs_le.2
  have hextra := mul_nonneg (abs_nonneg (Real.log N)) (norm_nonneg e)
  dsimp [A] at hu hl
  constructor
  · linarith [abs_nonneg (Real.log N)]
  · linarith [le_abs_self (Real.log N),abs_nonneg (Real.log N)]

theorem paramRegular_log_finite_exp (f : S → P × E → ℝ) (hf : ∀ s, ParamRegular (f s)) :
    ParamRegular (fun z => Real.log (∑ s, Real.exp (f s z))) := by
  classical
  let Z := fun z : P × E => ∑ s, Real.exp (f s z)
  have hZ : ParamSmooth Z := ParamSmooth.sum Finset.univ _ (fun s _ => (hf s).expSmooth)
  have hp (z : P × E) : Z z ≠ 0 :=
    (Finset.sum_pos (fun s (_ : s ∈ Finset.univ) => Real.exp_pos (f s z)) Finset.univ_nonempty).ne'
  have hi : ParamExpGrowth (fun z => (Z z)⁻¹) := param_inv_finite_exp_growth f (fun s => (hf s).2.1)
  exact ⟨hZ.1.log hp,param_log_finite_exp_linear f (fun s => (hf s).2.1),
    param_fderiv_log_growth Z id (hZ.1.differentiable (by norm_num)) hp hi hZ.2.2.1,
    param_second_log_growth Z id hZ.1 hp hi hZ.2.2.1 hZ.2.2.2⟩
end ParameterFiniteLog
end SK.Analytic

end
end

end

end OAI
