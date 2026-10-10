import Mathlib
import OAI.Analysis.SymmetricDomains.AnalyticZeroNull

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
namespace Release061
open Set MeasureTheory Module
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem analyticAt_matrix_det {n : ℕ} {A : E → Matrix (Fin n) (Fin n) ℂ} {x : E}
    (ha : ∀ i j, AnalyticAt ℝ (fun y => A y i j) x) :
    AnalyticAt ℝ (fun y => (A y).det) x := by
  classical
  simp only [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ _
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => ha (σ i) i)

theorem analytic_tangent_minor {n : ℕ} {U : Set E} {q : E → Fin n → ℂ}
    (hq : AnalyticOnNhd ℝ q U) (v : Fin n → E) :
    AnalyticOnNhd ℝ (fun x => Matrix.det (fun i j => fderiv ℝ q x (v j) i)) U := by
  intro x hx
  apply analyticAt_matrix_det
  intro i j
  exact ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℝ] ℂ).analyticAt _).comp
    (((ContinuousLinearMap.apply ℝ (Fin n → ℂ) (v j)).analyticAt _).comp (hq x hx).fderiv)

theorem complex_tangent_span_ae [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {n : ℕ} {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U)
    {q : E → Fin n → ℂ} (hq : AnalyticOnNhd ℝ q U)
    (v : Fin n → E) {p : E} (hp : p ∈ U)
    (hne : Matrix.det (fun i j => fderiv ℝ q p (v j) i) ≠ 0) :
    μ {x | x ∈ U ∧ Submodule.span ℂ (Set.range (fderiv ℝ q x)) ≠ ⊤} = 0 := by
  have hn := analytic_zero_null μ hU hc (analytic_tangent_minor hq v) hp hne
  apply measure_mono_null (t := {x | x ∈ U ∧
    Matrix.det (fun i j => fderiv ℝ q x (v j) i) = 0}) _ hn
  intro x hx
  refine ⟨hx.1,?_⟩
  by_contra hm
  have hli : LinearIndependent ℂ (fun j => fderiv ℝ q x (v j)) :=
    Matrix.linearIndependent_cols_of_det_ne_zero hm
  have hall := hli.span_eq_top_of_card_eq_finrank' (by simp)
  apply hx.2
  exact top_unique (hall ▸ Submodule.span_mono (Set.range_comp_subset_range v (fderiv ℝ q x)))

theorem exists_nonzero_tangent_minor {n : ℕ} {L : E →ₗ[ℝ] (Fin n → ℂ)}
    (hL : Submodule.span ℂ (Set.range L) = ⊤) :
    ∃ v : Fin n → E, Matrix.det (fun i j => L (v j) i) ≠ 0 := by
  classical
  let b := Basis.ofSpan (s := Set.range L)
    (show ⊤ ≤ Submodule.span ℂ (Set.range L) by rw [hL])
  let b' := b.reindex (b.indexEquiv (Pi.basisFun ℂ (Fin n)))
  have hb : ∀ i, ∃ v, L v = b' i := by
    intro i
    apply Basis.ofSpan_subset (show ⊤ ≤ Submodule.span ℂ (Set.range L) by rw [hL])
    refine ⟨(b.indexEquiv (Pi.basisFun ℂ (Fin n))).symm i,?_⟩
    change b _ = b.reindex _ i
    simp only [Basis.reindex_apply]
  choose v hv using hb
  refine ⟨v,?_⟩
  have hli : LinearIndependent ℂ (fun j => L (v j)) := by
    simpa only [show (fun j => L (v j)) = b' from funext hv] using b'.linearIndependent
  exact Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.Nonsingular.of_linearIndependent_col hli)

theorem complex_tangent_rank_alternative [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {n : ℕ} {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U)
    {q : E → Fin n → ℂ} (hq : AnalyticOnNhd ℝ q U) :
    (∀ p ∈ U, Submodule.span ℂ (Set.range (fderiv ℝ q p)) ≠ ⊤) ∨
      μ {x | x ∈ U ∧ Submodule.span ℂ (Set.range (fderiv ℝ q x)) ≠ ⊤} = 0 := by
  classical
  by_cases h : ∀ p ∈ U, Submodule.span ℂ (Set.range (fderiv ℝ q p)) ≠ ⊤
  · exact Or.inl h
  · push Not at h
    obtain ⟨p,hp,hfull⟩ := h
    obtain ⟨v,hv⟩ := exists_nonzero_tangent_minor hfull
    exact Or.inr (complex_tangent_span_ae μ hU hc hq v hp hv)

end Release061

end

end OAI
