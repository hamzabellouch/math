import Mathlib
import OAI.Analysis.Conductivity.Variational.PhysicalEndLocalLipschitz

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped NNReal

lemma sourceRadial_lipschitz : ∃ K,LipschitzWith K sourceRadial := by
  have h0 := ((ContinuousLinearMap.toSpanSingleton ℝ (sourceLength⁻¹ : ℝ)).lipschitzWith.comp
    (localLipschitz_abs.comp (LipschitzWith.eval (α := fun _ : Fin 3 => ℝ) (0:Fin 3))))
  have h1 := localLipschitz_abs.comp (LipschitzWith.eval (α := fun _ : Fin 3 => ℝ) (1:Fin 3))
  have H := h0.max h1
  refine ⟨max (‖ContinuousLinearMap.toSpanSingleton ℝ sourceLength⁻¹‖₊*(1*1)) (1*1),?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [sourceRadial,div_eq_mul_inv,ContinuousLinearMap.toSpanSingleton_apply,Function.comp_apply,smul_eq_mul] using H.dist_le_mul x y

lemma sourceCollarTime_lipschitz : ∃ K,LipschitzWith K sourceCollarTime := by
  obtain ⟨K,hK⟩ := sourceRadial_lipschitz
  have h0 := localLipschitz_abs.comp ((ContinuousLinearMap.toSpanSingleton ℝ (sourceRadialWidth⁻¹ : ℝ)).lipschitzWith.comp
    (hK.sub (LipschitzWith.const sourceRadialCenter)))
  have h1 := localLipschitz_abs.comp (LipschitzWith.eval (α := fun _ : Fin 3 => ℝ) (2:Fin 3))
  have H := (LipschitzWith.const (1:ℝ)).sub (h0.max h1)
  refine ⟨0+max (1*(‖ContinuousLinearMap.toSpanSingleton ℝ sourceRadialWidth⁻¹‖₊*(K+0))) (1*1),?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,sourceCollarTime,sourceCrossCoordinates,div_eq_mul_inv,ContinuousLinearMap.toSpanSingleton_apply,Function.comp_apply,smul_eq_mul] using H.dist_le_mul x y

lemma attachedEndTime_lipschitz (a b : ℝ) :
    ∃ K,LipschitzWith K (fun y => a*(sourceCollarTime y-b)) := by
  obtain ⟨K,hK⟩ := sourceCollarTime_lipschitz
  have H := (ContinuousLinearMap.toSpanSingleton ℝ a).lipschitzWith.comp (hK.sub (LipschitzWith.const b))
  refine ⟨‖ContinuousLinearMap.toSpanSingleton ℝ a‖₊*(K+0),?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [ContinuousLinearMap.toSpanSingleton_apply,Function.comp_apply,smul_eq_mul,mul_comm] using H.dist_le_mul x y

end ScalarConductivity

end

end OAI
