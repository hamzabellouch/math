import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianZeroMass

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic
section RegularAlgebra
variable {E D : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem BoundedDerivs.add {f g : E → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g) :
    BoundedDerivs (fun x => f x+g x) := by
  obtain ⟨hf,C,D,hC,hD,hf₁,hf₂⟩ := hf
  obtain ⟨hg,A,B,hA,hB,hg₁,hg₂⟩ := hg
  have hd := hf.differentiable (by norm_num)
  have he := hg.differentiable (by norm_num)
  have heq : fderiv ℝ (fun x => f x+g x) = fun x => fderiv ℝ f x+fderiv ℝ g x := by
    funext x
    exact ((hd x).hasFDerivAt.add (he x).hasFDerivAt).fderiv
  have hdd := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hee := (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  refine ⟨hf.add hg,C+A,D+B,add_nonneg hC hA,add_nonneg hD hB,?_,?_⟩
  · intro x
    rw [heq]
    exact (ContinuousLinearMap.opNorm_add_le _ _).trans (add_le_add (hf₁ x) (hg₁ x))
  · intro x
    rw [heq, ((hdd x).hasFDerivAt.fun_add (hee x).hasFDerivAt).fderiv]
    exact (ContinuousLinearMap.opNorm_add_le _ _).trans (add_le_add (hf₂ x) (hg₂ x))

theorem BoundedDerivs.compCLM {f : E → ℝ} (hf : BoundedDerivs f) (L : D →L[ℝ] E) :
    BoundedDerivs (fun x => f (L x)) := by
  obtain ⟨hf,C,A,hC,hA,hf₁,hf₂⟩ := hf
  let P : (E →L[ℝ] ℝ) →L[ℝ] D →L[ℝ] ℝ := (ContinuousLinearMap.compL ℝ D E ℝ).flip L
  have hP (B : E →L[ℝ] ℝ) : P B = B.comp L := rfl
  have hPn : ‖P‖ ≤ ‖L‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro B
    rw [hP]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (mul_comm _ _)
  have hd := hf.differentiable (by norm_num)
  have hdd := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have heq : fderiv ℝ (fun x => f (L x)) = fun x => P (fderiv ℝ f (L x)) := by
    funext x
    exact ((hd (L x)).hasFDerivAt.comp x L.hasFDerivAt).fderiv
  refine ⟨hf.comp L.contDiff,C*‖L‖,A*‖L‖*‖L‖,
    mul_nonneg hC (norm_nonneg _),mul_nonneg (mul_nonneg hA (norm_nonneg _)) (norm_nonneg _),?_,?_⟩
  · intro x
    rw [heq]
    change ‖P (fderiv ℝ f (L x))‖ ≤ C*‖L‖
    rw [hP]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hf₁ _) (norm_nonneg _))
  · intro x
    have hsec : HasFDerivAt (fun x => P (fderiv ℝ f (L x)))
        (P.comp ((fderiv ℝ (fderiv ℝ f) (L x)).comp L)) x := by
      simpa only [Function.comp_def] using
        P.hasFDerivAt.comp x ((hdd (L x)).hasFDerivAt.comp x L.hasFDerivAt)
    rw [heq, hsec.fderiv]
    calc
      _ ≤ ‖P‖*‖(fderiv ℝ (fderiv ℝ f) (L x)).comp L‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖L‖*(A*‖L‖) := by
        gcongr
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_right (hf₂ _) (norm_nonneg _))
      _ = _ := by ring

theorem RegularConvex.add {f g : E → ℝ} (hf : RegularConvex f) (hg : RegularConvex g) :
    RegularConvex (fun x => f x+g x) := ⟨hf.1.add hg.1, hf.2.add hg.2⟩

theorem RegularConvex.const_mul {f : E → ℝ} (hf : RegularConvex f) {m : ℝ} (hm : 0 ≤ m) :
    RegularConvex (fun x => m*f x) := by
  refine ⟨hf.1.const_mul m, ?_⟩
  simpa only [smul_eq_mul] using hf.2.smul hm

theorem RegularConvex.compCLM {f : E → ℝ} (hf : RegularConvex f) (L : D →L[ℝ] E) :
    RegularConvex (fun x => f (L x)) := by
  refine ⟨hf.1.compCLM L, ?_⟩
  exact hf.2.comp_linearMap L.toLinearMap

end RegularAlgebra
end SK.Analytic

end
end
end
end
end
end

end OAI
