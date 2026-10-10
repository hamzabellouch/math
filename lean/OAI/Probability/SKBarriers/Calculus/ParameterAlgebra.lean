import Mathlib
import OAI.Probability.SKBarriers.Calculus.ParameterDerivatives
import OAI.Probability.SKBarriers.Calculus.ParameterSmooth

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
theorem ParamExpGrowth.weakAdd {P E F : Type} [NormedAddCommGroup P]
    [NormedAddCommGroup E] [Norm F] [Add F] {f g : P × E → F}
    (hf : ParamExpGrowth f) (hg : ParamExpGrowth g)
    (hadd : ∀ z, ‖f z+g z‖ ≤ ‖f z‖+‖g z‖) : ParamExpGrowth (fun z => f z+g z) := by
  intro R
  obtain ⟨C,M,hC,hM,hf⟩ := hf R
  obtain ⟨D,L,hD,hL,hg⟩ := hg R
  refine ⟨C+D,max M L,add_nonneg hC hD,(le_max_left M L).trans' hM,?_⟩
  intro p e hp
  calc
    _ ≤ ‖f (p,e)‖+‖g (p,e)‖ := hadd (p,e)
    _ ≤ C*Real.exp (M*‖e‖)+D*Real.exp (L*‖e‖) := add_le_add (hf p e hp) (hg p e hp)
    _ ≤ C*Real.exp (max M L*‖e‖)+D*Real.exp (max M L*‖e‖) := by
      gcongr <;> first | exact le_max_left _ _ | exact le_max_right _ _
    _ = _ := by ring

section ParameterAlgebra
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def ParamSmooth (f : P × E → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ ParamExpGrowth f ∧ ParamExpGrowth (fderiv ℝ f) ∧
    ParamExpGrowth (fderiv ℝ (fderiv ℝ f))

theorem ParamSmooth.add {f g : P × E → ℝ} (hf : ParamSmooth f) (hg : ParamSmooth g) :
    ParamSmooth (fun z => f z+g z) := by
  have he : fderiv ℝ (fun z => f z+g z) = fun z => fderiv ℝ f z+fderiv ℝ g z := by
    funext z
    exact ((hf.1.differentiable (by norm_num) z).hasFDerivAt.fun_add
      (hg.1.differentiable (by norm_num) z).hasFDerivAt).fderiv
  have he₂ : fderiv ℝ (fderiv ℝ (fun z => f z+g z)) =
      fun z => fderiv ℝ (fderiv ℝ f) z+fderiv ℝ (fderiv ℝ g) z := by
    rw [he]
    funext z
    exact (((hf.1.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z).hasFDerivAt.fun_add
      ((hg.1.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z).hasFDerivAt).fderiv
  refine ⟨hf.1.add hg.1,hf.2.1.add hg.2.1,?_,?_⟩
  · rw [he]
    exact hf.2.2.1.add hg.2.2.1
  · rw [he₂]
    exact hf.2.2.2.weakAdd hg.2.2.2 (fun _ => ContinuousLinearMap.opNorm_add_le _ _)

theorem paramSmooth_const (c : ℝ) : ParamSmooth (fun _ : P × E => c) := by
  refine ⟨contDiff_const,?_,?_,?_⟩
  · exact ParamExpGrowth.of_bounded (norm_nonneg c) (fun _ => le_rfl)
  · exact ParamExpGrowth.of_bounded (C := 0) le_rfl (by intro z; simp)
  · have he : fderiv ℝ (fun _ : P × E => c) = fun _ => (0 : P × E →L[ℝ] ℝ) := by
      funext z
      simp
    rw [he]
    intro R
    refine ⟨0,0,le_rfl,le_rfl,?_⟩
    intro p e _
    simp only [fderiv_const_apply,ContinuousLinearMap.opNorm_zero,zero_mul,le_refl]

theorem ParamSmooth.sum {ι : Type} (s : Finset ι) (f : ι → P × E → ℝ)
    (hf : ∀ i ∈ s, ParamSmooth (f i)) : ParamSmooth (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (paramSmooth_const (P := P) (E := E) 0)
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using (hf a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem ParamRegular.toSmooth {f : P × E → ℝ} (hf : ParamRegular f) : ParamSmooth f :=
  ⟨hf.1,hf.2.1.expGrowth,hf.2.2⟩

theorem ParamRegular.expSmooth {f : P × E → ℝ} (hf : ParamRegular f) :
    ParamSmooth (fun z => Real.exp (f z)) := by
  have hg : ParamExpGrowth (fun z => Real.exp (f z)) := by
    simpa only [one_mul] using hf.2.1.exp_mul 1
  exact ⟨hf.1.exp,hg,
    param_fderiv_exp_growth f id (hf.1.differentiable (by norm_num)) hg hf.2.2.1,
    param_second_exp_growth f id hf.1 hg hf.2.2.1 hf.2.2.2⟩

omit [NormedSpace ℝ P] [NormedSpace ℝ E] in
theorem ParamLinearGrowth.add {f g : P × E → ℝ} (hf : ParamLinearGrowth f)
    (hg : ParamLinearGrowth g) : ParamLinearGrowth (fun z => f z+g z) := by
  intro R
  obtain ⟨C,hC,hf⟩ := hf R
  obtain ⟨D,hD,hg⟩ := hg R
  refine ⟨C+D,add_nonneg hC hD,?_⟩
  intro p e hp
  exact (abs_add_le _ _).trans ((add_le_add (hf p e hp) (hg p e hp)).trans_eq (add_mul _ _ _).symm)

theorem ParamRegular.add {f g : P × E → ℝ} (hf : ParamRegular f) (hg : ParamRegular g) :
    ParamRegular (fun z => f z+g z) := by
  have H := hf.toSmooth.add hg.toSmooth
  exact ⟨H.1,hf.2.1.add hg.2.1,H.2.2⟩

theorem paramRegular_const (c : ℝ) : ParamRegular (fun _ : P × E => c) := by
  have H := paramSmooth_const (P := P) (E := E) c
  refine ⟨H.1,?_,H.2.2⟩
  intro R
  refine ⟨|c|,abs_nonneg c,?_⟩
  intro p e _
  nlinarith [abs_nonneg c,norm_nonneg e]
end ParameterAlgebra
end SK.Analytic

end
end

end

end OAI
