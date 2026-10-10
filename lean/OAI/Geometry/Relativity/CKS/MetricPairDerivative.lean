import OAI.Geometry.Relativity.CKS.TailEnergy

namespace OAI

noncomputable section
open scoped Topology
namespace CKSSchwarzschild

lemma metric_pair_derivative_general
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (g : V → V →L[ℝ] V →L[ℝ] ℝ) {f A B : W → V} {y : W}
    (hg : DifferentiableAt ℝ g (f y)) (hf : DifferentiableAt ℝ f y)
    (hA : DifferentiableAt ℝ A y) (hB : DifferentiableAt ℝ B y) (a : W) :
    fderiv ℝ (fun z => g (f z) (A z) (B z)) y a =
      fderiv ℝ (fun x => g x (A y) (B y)) (f y) (fderiv ℝ f y a) +
      g (f y) (fderiv ℝ A y a) (B y) + g (f y) (A y) (fderiv ℝ B y a) := by
  have hgf : DifferentiableAt ℝ (fun z => g (f z)) y := DifferentiableAt.comp (g := g) y hg hf
  have hgA : DifferentiableAt ℝ (fun z => g (f z) (A z)) y := hgf.clm_apply hA
  have hcA : DifferentiableAt ℝ (fun x => g x (A y)) (f y) := hg.clm_apply (differentiableAt_const _)
  rw [fderiv_clm_apply hgA hB, fderiv_clm_apply hgf hA,
    fderiv_clm_apply hcA (differentiableAt_const _),
    fderiv_clm_apply hg (differentiableAt_const _),
    fderiv_fun_comp (g := g) y hg hf]
  simp only [add_apply,ContinuousLinearMap.comp_apply,zero_apply,
    ContinuousLinearMap.flip_apply,map_zero,zero_add,fderiv_const_apply]
  ring
end CKSSchwarzschild

end

end OAI
