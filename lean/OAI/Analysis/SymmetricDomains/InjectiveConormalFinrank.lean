import Mathlib
import OAI.Analysis.SymmetricDomains.NashCellGeometricRank
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
open Set Filter Topology
open scoped Classical

theorem chart_tangent_identities {d m N : ℕ}
    (F : Affine m → Affine N) (G : Affine N → Affine m)
    (q : (Fin d → ℝ) → Affine N) {x : Fin d → ℝ}
    (hF0 : F 0 = q x) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (q x))
    (hq : DifferentiableAt ℝ q x)
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id)
    (hFG : (F ∘ G ∘ q) =ᶠ[𝓝 x] q) :
    G (q x) = 0 ∧
    (fderiv ℂ G (q x)).comp (fderiv ℂ F 0) = ContinuousLinearMap.id ℂ _ ∧
    ((fderiv ℂ F 0).restrictScalars ℝ).comp (fderiv ℝ (G ∘ q) x) = fderiv ℝ q x ∧
    Function.Injective (fderiv ℂ F 0) := by
  have hG0 : G (q x) = 0 := by
    simpa only [Function.comp_apply,hF0,Function.id_def] using hGF.eq_of_nhds
  have hg : AnalyticAt ℂ G (F 0) := hF0 ▸ hG
  have hid := (hg.differentiableAt.hasFDerivAt.comp 0 hF.differentiableAt.hasFDerivAt).congr_of_eventuallyEq hGF.symm
  have hi : (fderiv ℂ G (q x)).comp (fderiv ℂ F 0) = ContinuousLinearMap.id ℂ _ := by
    simpa only [hF0] using hid.unique (hasFDerivAt_id (0 : Affine m))
  refine ⟨hG0,hi,?_,?_⟩
  · have hr : DifferentiableAt ℝ (G ∘ q) x := hG.differentiableAt.restrictScalars ℝ |>.comp x hq
    have hf : AnalyticAt ℂ F ((G ∘ q) x) := by simpa only [Function.comp_apply,hG0] using hF
    have hh := (hf.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp x hr.hasFDerivAt
    have he := hh.congr_of_eventuallyEq hFG.symm
    simpa only [Function.comp_apply,hG0] using he.fderiv.symm
  · intro a b hab
    have hh := congrArg (fderiv ℂ G (q x)) hab
    simpa only [← ContinuousLinearMap.comp_apply,hi,ContinuousLinearMap.id_apply] using hh

theorem chart_parametric_generic {d m N : ℕ}
    (F : Affine m → Affine N) (G : Affine N → Affine m)
    (q : (Fin d → ℝ) → Affine N) {x : Fin d → ℝ}
    (hF0 : F 0 = q x) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (q x))
    (hq : DifferentiableAt ℝ q x) (hqi : Function.Injective (fderiv ℝ q x))
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id)
    (hFG : (F ∘ G ∘ q) =ᶠ[𝓝 x] q)
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1))) :
    Function.Injective (fderiv ℝ (G ∘ q) x) ∧
    Submodule.span ℂ (range (fderiv ℝ (G ∘ q) x)) = ⊤ := by
  obtain ⟨hG0,hi,hd,hFi⟩ := chart_tangent_identities F G q hF0 hF hG hq hGF hFG
  have hspan := real_parametric_span_eq_chart_of_rank_ge F G q hF0 hF hG hq hGF hFG hr
  have hder : fderiv ℝ (G ∘ q) x = ((fderiv ℂ G (q x)).restrictScalars ℝ).comp (fderiv ℝ q x) :=
    ((hG.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp x hq.hasFDerivAt).fderiv
  refine ⟨?_,?_⟩
  · intro a b hab
    apply hqi
    rw [← hd]
    exact congrArg ((fderiv ℂ F 0).restrictScalars ℝ) hab
  · let W := Submodule.span ℂ (range (fderiv ℝ (G ∘ q) x))
    have hle : Submodule.span ℂ (range (fderiv ℝ q x)) ≤
        W.comap (fderiv ℂ G (q x)).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨v,rfl⟩
      change fderiv ℂ G (q x) (fderiv ℝ q x v) ∈ W
      have he : fderiv ℂ G (q x) (fderiv ℝ q x v) = fderiv ℝ (G ∘ q) x v := by
        rw [hder]; rfl
      rw [he]
      exact Submodule.subset_span (mem_range_self v)
    apply top_unique
    intro v _
    have hv : fderiv ℂ F 0 v ∈ Submodule.span ℂ (range (fderiv ℝ q x)) := by
      rw [hspan]; exact ⟨v,rfl⟩
    have hh := hle hv
    change fderiv ℂ G (q x) (fderiv ℂ F 0 v) ∈ W at hh
    simpa only [← ContinuousLinearMap.comp_apply,hi,ContinuousLinearMap.id_apply] using hh

theorem injective_conormal_finrank {d m : ℕ}
    (M : (Fin d → ℝ) →L[ℝ] Affine m) (hM : Function.Injective M) :
    d + Module.finrank ℝ (LinearMap.range M.toLinearMap).dualAnnihilator = 2*m := by
  have hr : Module.finrank ℝ (LinearMap.range M.toLinearMap) = d := by
    simpa using LinearMap.finrank_range_of_inj (f := M.toLinearMap) hM
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range M.toLinearMap)
  simpa [hr,Affine,Module.finrank_pi_fintype,Nat.mul_comm] using h
end Release061

end

end OAI
