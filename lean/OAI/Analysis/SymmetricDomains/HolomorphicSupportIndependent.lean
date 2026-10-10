import Mathlib
import OAI.Analysis.SymmetricDomains.FiniteUnion

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set
open scoped Classical

theorem complex_independent_of_generic_real_conormals
    {E ι : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E]
    [IsScalarTower ℝ ℂ E] [Fintype ι]
    (S : Set E) (hS : Submodule.span ℂ S = ⊤)
    (l : ι → E →ₗ[ℂ] ℂ)
    (hz : ∀ i, ∀ x ∈ S, (l i x).re = 0)
    (hi : LinearIndependent ℝ
      (fun i => Complex.reCLM.toLinearMap.comp ((l i).restrictScalars ℝ))) :
    LinearIndependent ℂ l := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  let B : E →ₗ[ℂ] ℂ := ∑ i, (c i).im • l i
  have hBS : S ⊆ LinearMap.ker B := by
    intro x hx
    have hr : (B x).re = 0 := by
      simp [B,LinearMap.sum_apply,LinearMap.smul_apply,hz _ x hx]
    have hh := congrArg (fun f : E →ₗ[ℂ] ℂ => (f x).re) hc
    have him : (B x).im = 0 := by
      simp only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,Complex.re_sum,
        Complex.mul_re,hz _ x hx,mul_zero,zero_sub,Finset.sum_neg_distrib,
        LinearMap.zero_apply,Complex.zero_re,neg_eq_zero] at hh
      simpa [B,LinearMap.sum_apply,LinearMap.smul_apply,Complex.smul_im] using hh
    exact Complex.ext hr him
  have hB : B = 0 := by
    apply LinearMap.ker_eq_top.mp
    apply top_unique
    rw [← hS]
    exact Submodule.span_le.mpr hBS
  have hbi : ∑ i, (c i).im •
      (Complex.reCLM.toLinearMap.comp ((l i).restrictScalars ℝ)) = 0 := by
    ext x
    have hh := congrArg (fun f : E →ₗ[ℂ] ℂ => (f x).re) hB
    simpa [B,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,
      Complex.smul_re] using hh
  have hci := Fintype.linearIndependent_iff.mp hi (fun i => (c i).im) hbi
  have hbr : ∑ i, (c i).re •
      (Complex.reCLM.toLinearMap.comp ((l i).restrictScalars ℝ)) = 0 := by
    ext x
    have hh := congrArg (fun f : E →ₗ[ℂ] ℂ => (f x).re) hc
    simpa [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,
      Complex.mul_re,hci] using hh
  have hcr := Fintype.linearIndependent_iff.mp hi (fun i => (c i).re) hbr
  intro i
  exact Complex.ext (hcr i) (hci i)
end

open Set Filter Topology
open scoped Classical

theorem log_norm_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (h : E → ℂ) {x : E} (ha : AnalyticAt ℂ (fun z => Complex.log (h z)) x) :
    fderiv ℝ (fun z => Real.log ‖h z‖) x =
      Complex.reCLM.comp ((fderiv ℂ (fun z => Complex.log (h z)) x).restrictScalars ℝ) := by
  have hr := Complex.reCLM.hasFDerivAt.comp x (ha.differentiableAt.hasFDerivAt.restrictScalars ℝ)
  change HasFDerivAt (fun z => (Complex.log (h z)).re) _ x at hr
  have he : (fun z => (Complex.log (h z)).re) = (fun z => Real.log ‖h z‖) :=
    funext (fun _ => Complex.log_re _)
  rw [he] at hr
  exact hr.fderiv

theorem holomorphic_support_independent {m d k : ℕ}
    (M : (Fin d → ℝ) →L[ℝ] Affine m)
    (hM : Submodule.span ℂ (range M) = ⊤)
    (h : Fin k → Affine m → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (fun z => Complex.log (h i z)) 0)
    (hi : LinearIndependent ℝ (fun i => (fderiv ℝ (fun z => Real.log ‖h i z‖) 0).toLinearMap))
    (hz : ∀ i, (fderiv ℝ (fun z => Real.log ‖h i z‖) 0).comp M = 0) :
    LinearIndependent ℂ (fun i => (fderiv ℂ (fun z => Complex.log (h i z)) 0).toLinearMap) := by
  apply complex_independent_of_generic_real_conormals (range M) hM
  · intro i y hy
    obtain ⟨v,rfl⟩ := hy
    have he := congrArg (fun f : (Fin d → ℝ) →L[ℝ] ℝ => f v) (hz i)
    rw [log_norm_fderiv _ (ha i)] at he
    exact he
  · have he (i) : Complex.reCLM.toLinearMap.comp
        (((fderiv ℂ (fun z => Complex.log (h i z)) 0).toLinearMap).restrictScalars ℝ) =
        (fderiv ℝ (fun z => Real.log ‖h i z‖) 0).toLinearMap := by
      rw [log_norm_fderiv _ (ha i)]
      rfl
    simpa only [he] using hi
end Release061

end

end OAI
