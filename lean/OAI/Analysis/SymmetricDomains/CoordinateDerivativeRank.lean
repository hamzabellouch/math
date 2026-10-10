import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio

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

theorem complex_span_real_linear_range {d N : ℕ}
    (L : (Fin d → ℝ) →ₗ[ℝ] (Fin N → ℂ)) :
    Submodule.span ℂ (range L) =
      Submodule.span ℂ (range (fun i => L (Pi.single i 1))) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x,rfl⟩
    have hx : x = ∑ i : Fin d, x i • Pi.single i (1 : ℝ) := by
      ext j
      simp [Pi.single_apply]
    rw [hx,map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    change ((x i : ℂ) • L (Pi.single i 1)) ∈ _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i))
  · apply Submodule.span_mono
    rintro _ ⟨i,rfl⟩
    exact mem_range_self _

theorem matrix_rank_eq_complex_tangent_dimension {d N : ℕ}
    (L : (Fin d → ℝ) →ₗ[ℝ] (Fin N → ℂ)) :
    Matrix.rank (fun j i => L (Pi.single i 1) j) =
      Module.finrank ℂ (Submodule.span ℂ (range L)) := by
  rw [complex_span_real_linear_range L]
  exact Matrix.rank_eq_finrank_span_cols _

theorem complex_tangent_eq_of_rank_ge {d N m : ℕ}
    (L : (Fin d → ℝ) →ₗ[ℝ] (Fin N → ℂ))
    (T : Submodule ℂ (Fin N → ℂ)) (hT : Module.finrank ℂ T = m)
    (hLT : ∀ x, L x ∈ T)
    (hr : m ≤ Matrix.rank (fun j i => L (Pi.single i 1) j)) :
    Submodule.span ℂ (range L) = T := by
  have hle : Submodule.span ℂ (range L) ≤ T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x,rfl⟩
    exact hLT x
  apply Submodule.eq_of_le_of_finrank_eq hle
  apply Nat.le_antisymm (Submodule.finrank_mono hle)
  simpa only [matrix_rank_eq_complex_tangent_dimension,hT] using hr

theorem chart_tangent_finrank {m N : ℕ}
    (F : (Fin m → ℂ) → (Fin N → ℂ))
    (G : (Fin N → ℂ) → (Fin m → ℂ)) {a : Fin m → ℂ}
    (hF : AnalyticAt ℂ F a) (hG : AnalyticAt ℂ G (F a))
    (hGF : (G ∘ F) =ᶠ[𝓝 a] id) :
    Module.finrank ℂ (LinearMap.range (fderiv ℂ F a).toLinearMap) = m := by
  have hcomp := hG.differentiableAt.hasFDerivAt.comp a hF.differentiableAt.hasFDerivAt
  have hid := hcomp.congr_of_eventuallyEq hGF.symm
  have hi : (fderiv ℂ G (F a)).comp (fderiv ℂ F a) = ContinuousLinearMap.id ℂ _ :=
    hid.unique (hasFDerivAt_id a)
  have hinj : Function.Injective (fderiv ℂ F a) := by
    intro x y hxy
    have hh := congrArg (fderiv ℂ G (F a)) hxy
    simpa only [← ContinuousLinearMap.comp_apply,hi,ContinuousLinearMap.id_apply] using hh
  simpa using LinearMap.finrank_range_of_inj (f := (fderiv ℂ F a).toLinearMap) hinj

theorem real_derivative_mem_chart_tangent {d m N : ℕ}
    (F : (Fin m → ℂ) → (Fin N → ℂ))
    (G : (Fin N → ℂ) → (Fin m → ℂ))
    (q : (Fin d → ℝ) → (Fin N → ℂ)) {x : Fin d → ℝ}
    (hF : AnalyticAt ℂ F (G (q x))) (hG : AnalyticAt ℂ G (q x))
    (hq : DifferentiableAt ℝ q x)
    (hFG : (F ∘ G ∘ q) =ᶠ[𝓝 x] q) (v : Fin d → ℝ) :
    fderiv ℝ q x v ∈ LinearMap.range (fderiv ℂ F (G (q x))).toLinearMap := by
  have hGc := hG.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hFc := hF.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hc := hFc.comp x (hGc.comp x hq.hasFDerivAt)
  have he := hc.congr_of_eventuallyEq hFG.symm
  have hd := he.fderiv
  refine ⟨fderiv ℂ G (q x) (fderiv ℝ q x v),?_⟩
  exact (congrArg (fun L : (Fin d → ℝ) →L[ℝ] (Fin N → ℂ) => L v) hd).symm

theorem coordinate_derivative_rank {d N : ℕ}
    (q : (Fin d → ℝ) → (Fin N → ℂ)) {x : Fin d → ℝ}
    (hq : DifferentiableAt ℝ q x) :
    Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1)) =
      Module.finrank ℂ (Submodule.span ℂ (range (fderiv ℝ q x))) := by
  have he (j : Fin N) : fderiv ℝ (fun y => q y j) x =
      (ContinuousLinearMap.proj j).comp (fderiv ℝ q x) := by
    exact ((ContinuousLinearMap.proj j).hasFDerivAt.comp x hq.hasFDerivAt).fderiv
  simp_rw [he,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply]
  exact matrix_rank_eq_complex_tangent_dimension (fderiv ℝ q x).toLinearMap

end Release061

end

end OAI
