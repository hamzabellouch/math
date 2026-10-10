import Mathlib
import OAI.Analysis.SymmetricDomains.ComplexTangentRankAlternative
import OAI.Analysis.SymmetricDomains.NashCellLowRank
import OAI.Analysis.SymmetricDomains.ChartDimensionLeCoordinate

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem analytic_matrix_rank_ae_ge [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {m n : ℕ} {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U)
    {A : E → Matrix (Fin m) (Fin n) ℂ}
    (hA : ∀ i j, AnalyticOnNhd ℝ (fun x => A x i j) U)
    {p : E} (hp : p ∈ U) : μ {x | x ∈ U ∧ (A x).rank < (A p).rank} = 0 := by
  obtain ⟨ρ,σ,hminor⟩ := matrix_rank_nonzero_minor (A p)
  have ha : AnalyticOnNhd ℝ (fun x => ((A x).submatrix ρ σ).det) U := by
    intro x hx
    exact analyticAt_matrix_det (fun i j => hA (ρ i) (σ j) x hx)
  have hn := analytic_zero_null μ hU hc ha hp hminor
  apply measure_mono_null (t := {x | x ∈ U ∧ ((A x).submatrix ρ σ).det = 0}) _ hn
  intro x hx
  refine ⟨hx.1,?_⟩
  by_contra hne
  have hr : (A p).rank ≤ (A x).rank := by
    have hr := Matrix.rank_submatrix_le (A x) ρ σ
    rw [Matrix.rank_of_det_ne_zero hne] at hr
    simpa using hr
  exact (not_lt_of_ge hr) hx.2

theorem nash_cell_intrinsic_rank_dichotomy {d m N : ℕ}
    (V : Set (Fin N → ℂ))
    (F : (Fin m → ℂ) → (Fin N → ℂ)) (G : (Fin N → ℂ) → (Fin m → ℂ))
    (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (F 0))
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Fin m → ℂ)] id)
    (hFV : ∀ᶠ z in 𝓝 (0 : Fin m → ℂ), F z ∈ V)
    (B : Set (Fin d → ℝ)) (hBo : IsOpen B) (hB : IsPreconnected B) (h0 : 0 ∈ B)
    (q : (Fin d → ℝ) → Fin N → ℂ) (hq : AnalyticOnNhd ℝ q B)
    (hqV : ∀ x ∈ B, q x ∈ V)
    (hre : ∀ j, PolynomialSignSet (id : (Option (Fin d) → ℝ) → (Option (Fin d) → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = (q (fun i => x (some i)) j).re})
    (him : ∀ j, PolynomialSignSet (id : (Option (Fin d) → ℝ) → (Option (Fin d) → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = (q (fun i => x (some i)) j).im}) :
    (∃ P : MvPolynomial (Fin N) ℂ, (∃ y ∈ V, MvPolynomial.eval y P ≠ 0) ∧
      ∀ x ∈ B, MvPolynomial.eval (q x) P = 0) ∨
    volume {x | x ∈ B ∧
      Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1)) < m} = 0 := by
  classical
  let A : (Fin d → ℝ) → Matrix (Fin N) (Fin d) ℂ :=
    fun x j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1)
  by_cases hlow : ∀ x ∈ B, (A x).rank < m
  · left
    apply nash_cell_low_rank_proper_relation V B hBo hB h0 q hq hqV hre him
    intro x hx
    have hm := chart_dimension_le_coordinate_trdeg V F G hF hG hGF hFV
    have hr : ((A x).rank : Cardinal) < (m : Cardinal) := by exact_mod_cast hlow x hx
    exact hr.trans_le hm
  · right
    push Not at hlow
    obtain ⟨p,hp,hrank⟩ := hlow
    have hA : ∀ j i, AnalyticOnNhd ℝ (fun x => A x j i) B := by
      intro j i x hx
      have hj : AnalyticAt ℝ (fun y => q y j) x :=
        ((ContinuousLinearMap.proj j : (Fin N → ℂ) →L[ℝ] ℂ).analyticAt _).comp (hq x hx)
      exact ((ContinuousLinearMap.apply ℝ ℂ (Pi.single i 1)).analyticAt _).comp hj.fderiv
    have hn := analytic_matrix_rank_ae_ge volume hBo hB hA hp
    apply measure_mono_null (t := {x | x ∈ B ∧ (A x).rank < (A p).rank}) _ hn
    intro x hx
    exact ⟨hx.1,lt_of_lt_of_le hx.2 hrank⟩

end Release061

end

end OAI
