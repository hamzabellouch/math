import Mathlib
import OAI.Analysis.SymmetricDomains.NashCellIntrinsicRank
import OAI.Analysis.SymmetricDomains.CoordinateDerivativeRank

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
open Set Filter Topology

theorem real_parametric_span_eq_chart_of_rank_ge {d m N : ℕ}
    (F : (Fin m → ℂ) → (Fin N → ℂ))
    (G : (Fin N → ℂ) → (Fin m → ℂ))
    (q : (Fin d → ℝ) → (Fin N → ℂ)) {x : Fin d → ℝ}
    (hF0 : F 0 = q x) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (q x))
    (hq : DifferentiableAt ℝ q x)
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Fin m → ℂ)] id)
    (hFG : (F ∘ G ∘ q) =ᶠ[𝓝 x] q)
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1))) :
    Submodule.span ℂ (range (fderiv ℝ q x)) =
      LinearMap.range (fderiv ℂ F 0).toLinearMap := by
  have hG0 : G (q x) = 0 := by
    simpa only [Function.comp_apply,hF0,Function.id_def] using hGF.eq_of_nhds
  apply complex_tangent_eq_of_rank_ge (fderiv ℝ q x).toLinearMap
    (LinearMap.range (fderiv ℂ F 0).toLinearMap)
  · exact chart_tangent_finrank F G hF (hF0 ▸ hG) hGF
  · intro v
    have hv := real_derivative_mem_chart_tangent F G q (hG0 ▸ hF) hG hq hFG v
    change fderiv ℝ q x v ∈ _
    simpa only [hG0] using hv
  · rw [matrix_rank_eq_complex_tangent_dimension]
    rwa [coordinate_derivative_rank q hq] at hr

end

open Set Filter Topology MeasureTheory

theorem nash_cell_geometric_rank_dichotomy {d m N : ℕ}
    (V : Set (Fin N → ℂ))
    (B : Set (Fin d → ℝ)) (hBo : IsOpen B) (hB : IsPreconnected B) (h0 : 0 ∈ B)
    (q : (Fin d → ℝ) → Fin N → ℂ) (hq : AnalyticOnNhd ℝ q B)
    (hqV : ∀ x ∈ B, q x ∈ V)
    (hre : ∀ j, PolynomialSignSet (id : (Option (Fin d) → ℝ) → (Option (Fin d) → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = (q (fun i => x (some i)) j).re})
    (him : ∀ j, PolynomialSignSet (id : (Option (Fin d) → ℝ) → (Option (Fin d) → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = (q (fun i => x (some i)) j).im})
    (F : (Fin d → ℝ) → (Fin m → ℂ) → (Fin N → ℂ))
    (G : (Fin d → ℝ) → (Fin N → ℂ) → (Fin m → ℂ))
    (hF0 : ∀ x ∈ B, F x 0 = q x)
    (hF : ∀ x ∈ B, AnalyticAt ℂ (F x) 0)
    (hG : ∀ x ∈ B, AnalyticAt ℂ (G x) (q x))
    (hGF : ∀ x ∈ B, (G x ∘ F x) =ᶠ[𝓝 (0 : Fin m → ℂ)] id)
    (hFG : ∀ x ∈ B, (F x ∘ G x ∘ q) =ᶠ[𝓝 x] q)
    (hFV : ∀ x ∈ B, ∀ᶠ z in 𝓝 (0 : Fin m → ℂ), F x z ∈ V) :
    (∃ P : MvPolynomial (Fin N) ℂ, (∃ y ∈ V, MvPolynomial.eval y P ≠ 0) ∧
      ∀ x ∈ B, MvPolynomial.eval (q x) P = 0) ∨
    volume {x | x ∈ B ∧ Submodule.span ℂ (range (fderiv ℝ q x)) ≠
      LinearMap.range (fderiv ℂ (F x) 0).toLinearMap} = 0 := by
  classical
  rcases nash_cell_intrinsic_rank_dichotomy V (F 0) (G 0)
    (hF 0 h0) (by simpa only [hF0 0 h0] using hG 0 h0)
    (hGF 0 h0) (hFV 0 h0) B hBo hB h0 q hq hqV hre him with hP | hn
  · exact Or.inl hP
  · right
    apply measure_mono_null (t := {x | x ∈ B ∧
      Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1)) < m}) _ hn
    intro x hx
    refine ⟨hx.1,?_⟩
    by_contra hr
    apply hx.2
    exact real_parametric_span_eq_chart_of_rank_ge (F x) (G x) q
      (hF0 x hx.1) (hF x hx.1) (hG x hx.1) (hq x hx.1).differentiableAt
      (hGF x hx.1) (hFG x hx.1) (Nat.le_of_not_gt hr)

end Release061

end

end OAI
