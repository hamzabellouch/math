import Mathlib
import OAI.Analysis.SymmetricDomains.IndependentChartConormals

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
open Set Filter Topology MeasureTheory
open scoped Classical
namespace ActualCriticalChart
variable {d m N : ℕ} {P : MvPolynomial (Fin N) ℂ} {q : (Fin d → ℝ) → Affine N}

theorem entire_supports (c : ActualCriticalChart P q) {x : Fin d → ℝ}
    (hx : x ∈ c.base) (hq : DifferentiableAt ℝ q x) (hP : MvPolynomial.eval (q x) P ≠ 0)
    {K : Set (Affine N)} (hpos : volume (Prod.mk x ⁻¹' c.maxLocus K) ≠ 0)
    (F : Affine m → Affine N) (hF0 : F 0 = q x) (hF : AnalyticAt ℂ F 0)
    (hFi : Function.Injective (fderiv ℂ F 0))
    (M : (Fin d → ℝ) →L[ℝ] Affine m)
    (hM : ((fderiv ℂ F 0).restrictScalars ℝ).comp M = fderiv ℝ q x) :
    ∃ h : Fin (Module.finrank ℝ (LinearMap.range M.toLinearMap).dualAnnihilator) →
        Affine N → ℂ,
      (∀ i, AnalyticOnNhd ℂ (h i) univ) ∧
      (∀ i, h i (q x) = 1) ∧
      (∀ i, ∀ z ∈ K, ‖h i z‖ ≤ Real.exp (-(dist z (q x))^2)) ∧
      (∀ i, AnalyticAt ℂ (fun z => Complex.log (h i (F z))) 0) ∧
      LinearIndependent ℝ (fun i => (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).toLinearMap) ∧
      ∀ i, (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).comp M = 0 := by
  let L := (fderiv ℂ F 0).restrictScalars ℝ
  obtain ⟨v,hv,hi⟩ := c.independent_chart_conormals hx hq hP L hFi M hM hpos
  let h (i : Fin (Module.finrank ℝ (LinearMap.range M.toLinearMap).dualAnnihilator)) :=
    parameterPeak P (c.param (x,v i)) (q x)
  have hd (i) : (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).toLinearMap =
      (c.ambientCovector x (v i)).comp L.toLinearMap := by
    have hh := (parameterPeak_log_norm_hasFDerivAt P (c.param (x,v i)) hP)
    have hh' : HasFDerivAt (fun z => Real.log ‖h i z‖)
        (fderiv ℝ (parameterLogBase P) (q x) +
          Complex.reCLM.comp ((c.param (x,v i)).restrictScalars ℝ)) (F 0) := by simpa only [hF0,h] using hh
    have he := (hh'.comp 0 (hF.differentiableAt.hasFDerivAt.restrictScalars ℝ)).fderiv
    change (fderiv ℝ ((fun z => Real.log ‖h i z‖) ∘ F) 0).toLinearMap = _
    rw [he]
    ext z
    rfl
  refine ⟨h,?_,?_,?_,?_,?_,?_⟩
  · intro i; exact parameterPeak_analytic _ _ _
  · intro i; exact parameterPeak_self _ _ hP
  · intro i
    exact parameterPeak_bound P (c.param (x,v i)) hP (hv i).2.2
  · intro i
    have hr := ((parameterPeak_log_differential P (c.param (x,v i)) hP).1)
    have hr' : AnalyticAt ℂ (fun z => Complex.log (h i z)) (F 0) := by simpa only [hF0,h] using hr
    exact hr'.comp hF
  · simpa only [hd] using hi
  · intro i
    have hdM : (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).toLinearMap.comp M.toLinearMap = 0 := by
      rw [hd,LinearMap.comp_assoc]
      have he : L.toLinearMap.comp M.toLinearMap = (fderiv ℝ q x).toLinearMap :=
        congrArg ContinuousLinearMap.toLinearMap hM
      rw [he]
      exact c.ambientCovector_comp hx hq hP (v i)
    ext z
    exact congrArg (fun f => f z) hdM
end ActualCriticalChart
end Release061

end

end OAI
