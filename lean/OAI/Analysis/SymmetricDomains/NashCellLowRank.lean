import Mathlib
import OAI.Analysis.SymmetricDomains.PolynomialRelationPropagates
import OAI.Analysis.SymmetricDomains.NashParametrizationExtension
import OAI.Analysis.SymmetricDomains.ComplexificationRankLeReal

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

theorem nash_cell_low_rank_proper_relation {n N : ℕ}
    (V : Set (Fin N → ℂ))
    (B : Set (Fin n → ℝ)) (hBo : IsOpen B) (hB : IsPreconnected B) (h0 : 0 ∈ B)
    (q : (Fin n → ℝ) → Fin N → ℂ) (hq : AnalyticOnNhd ℝ q B)
    (hqV : ∀ x ∈ B, q x ∈ V)
    (hre : ∀ j, PolynomialSignSet (id : (Option (Fin n) → ℝ) → (Option (Fin n) → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = (q (fun i => x (some i)) j).re})
    (him : ∀ j, PolynomialSignSet (id : (Option (Fin n) → ℝ) → (Option (Fin n) → ℝ))
      {x | (fun i => x (some i)) ∈ B ∧ x none = (q (fun i => x (some i)) j).im})
    (hrank : ∀ x ∈ B,
      (Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1)) : Cardinal) <
      Algebra.trdeg ℂ (MvPolynomial (Fin N) ℂ ⧸ MvPolynomial.vanishingIdeal ℂ V)) :
    ∃ P : MvPolynomial (Fin N) ℂ, (∃ y ∈ V, MvPolynomial.eval y P ≠ 0) ∧
      ∀ x ∈ B, MvPolynomial.eval (q x) P = 0 := by
  classical
  obtain ⟨f,hf,hext,halg⟩ := nash_parametrization_extension B (hBo.mem_nhds h0)
    q (hq 0 h0) hre him
  obtain ⟨x,hx,hr⟩ := complexification_rank_le_real_rank f hf q hext B (hBo.mem_nhds h0)
  let A : Matrix (Fin N) (Fin n) (MeromorphicGermField (Fin n → ℂ)) :=
    fun j i => meromorphicPartial i (meromorphicGermOf (f j) (hf j))
  have hr' : (A.rank : Cardinal) ≤
      (Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1)) : Cardinal) := by
    exact_mod_cast hr
  have hgrank : (A.rank : Cardinal) = Algebra.trdeg ℂ
      (IntermediateField.adjoin ℂ (range (fun j => meromorphicGermOf (f j) (hf j)))) := by
    rw [Matrix.rank_eq_finrank_span_row,Module.finrank_eq_rank]
    exact analytic_nash_rank f hf halg
  have hlt := hr'.trans_lt (hrank x hx)
  rw [hgrank] at hlt
  have hIq : ∀ P ∈ MvPolynomial.vanishingIdeal ℂ V,
      MvPolynomial.aeval (fun j => meromorphicGermOf (f j) (hf j)) P = 0 := by
    intro P hP
    apply (meromorphicGerm_aeval_eq_zero_iff f hf P).mpr
    apply analytic_germ_zero_of_real_slice
      (((AnalyticOnNhd.eval_mvPolynomial P) _ (mem_univ _)).comp (analyticAt_pi_iff.mpr hf))
    filter_upwards [hext,hBo.mem_nhds h0] with y hy hyB
    change MvPolynomial.eval (fun j => f j (fun i => (y i : ℂ))) P = 0
    rw [hy]
    exact MvPolynomial.mem_vanishingIdeal_iff.mp hP _ (hqV y hyB)
  obtain ⟨P,hP,hzero⟩ := new_polynomial_relation_of_trdeg_lt
    (MvPolynomial.vanishingIdeal ℂ V) (fun j => meromorphicGermOf (f j) (hf j)) hIq hlt
  refine ⟨P,?_,?_⟩
  · simpa only [MvPolynomial.mem_vanishingIdeal_iff,not_forall,exists_prop,
      MvPolynomial.aeval_eq_eval] using hP
  · apply polynomial_relation_propagates hB q hq P h0
    have he : Tendsto (Flatten.realEmbedding n) (𝓝 0) (𝓝 0) := by
      have he := (Flatten.realEmbedding n).continuous.continuousAt (x := 0)
      rw [ContinuousAt,map_zero] at he
      exact he
    have hz := he ((meromorphicGerm_aeval_eq_zero_iff f hf P).mp hzero)
    filter_upwards [hz,hext] with y hy hy'
    change MvPolynomial.eval (fun j => f j (fun i => (y i : ℂ))) P = 0 at hy
    rwa [hy'] at hy

end Release061

end

end OAI
