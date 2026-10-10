import Mathlib
import OAI.Analysis.SymmetricDomains.AnalyticExtensionSemialgebraicAlgebraic
import OAI.Analysis.SymmetricDomains.MeromorphicGermDetZero

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
open Set Filter Topology Matrix Module

theorem matrix_rank_nonzero_minor {K : Type*} [Field K] {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) K) :
    ∃ (ρ : Fin A.rank → Fin n) (σ : Fin A.rank → Fin d),
      Matrix.det (fun i j => A (ρ i) (σ j)) ≠ 0 := by
  classical
  let S := Submodule.span K (range A)
  let a : Fin n → S := fun i => ⟨A i,Submodule.subset_span (mem_range_self i)⟩
  have ha : Submodule.span K (range a) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff S _).mpr rfl
  let b := Basis.ofSpan (s := range a) (show ⊤ ≤ Submodule.span K (range a) by rw [ha])
  have hdim : Module.finrank K S = A.rank := (Matrix.rank_eq_finrank_span_row A).symm
  let b' := b.reindex (b.indexEquiv (Module.finBasisOfFinrankEq K S hdim))
  have hb : ∀ i, ∃ j, a j = b' i := by
    intro i
    apply Basis.ofSpan_subset (show ⊤ ≤ Submodule.span K (range a) by rw [ha])
    refine ⟨(b.indexEquiv (Module.finBasisOfFinrankEq K S hdim)).symm i,?_⟩
    change b _ = b.reindex _ i
    simp only [Basis.reindex_apply]
  choose ρ hρ using hb
  have hli : LinearIndependent K (fun i => A (ρ i)) := by
    have hli := b'.linearIndependent.map' S.subtype (LinearMap.ker_eq_bot.mpr S.injective_subtype)
    have heq : (S.subtype ∘ b') = fun i => A (ρ i) := by
      funext i
      rw [Function.comp_apply,← hρ i]
      rfl
    simpa only [heq] using hli
  obtain ⟨σ,hσ⟩ := independent_rows_nonzero_minor (fun i j => A (ρ i) j) hli
  exact ⟨ρ,σ,hσ⟩

theorem analyticAt_complex_matrix_det {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {n : ℕ} {A : E → Matrix (Fin n) (Fin n) ℂ} {x : E}
    (hA : ∀ i j, AnalyticAt ℂ (fun z => A z i j) x) :
    AnalyticAt ℂ (fun z => (A z).det) x := by
  classical
  simp only [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ _
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => hA (σ i) i)

theorem analytic_germ_matrix_rank_le_real_rank {n N d : ℕ}
    (f : Fin N → Fin d → (Fin n → ℂ) → ℂ)
    (hf : ∀ i j, AnalyticAt ℂ (f i j) 0)
    (B : Set (Fin n → ℝ)) (hB : B ∈ 𝓝 0) :
    ∃ x ∈ B, Matrix.rank (fun i j => meromorphicGermOf (f i j) (hf i j)) ≤
      Matrix.rank (fun i j => f i j (fun k => (x k : ℂ))) := by
  classical
  let A : Matrix (Fin N) (Fin d) (MeromorphicGermField (Fin n → ℂ)) :=
    fun i j => meromorphicGermOf (f i j) (hf i j)
  obtain ⟨ρ,σ,hminor⟩ := matrix_rank_nonzero_minor A
  by_contra hn
  push Not at hn
  apply hminor
  apply (meromorphicGerm_det_eq_zero_iff
    (fun i j => f (ρ i) (σ j)) (fun i j => hf (ρ i) (σ j))).mpr
  apply analytic_germ_zero_of_real_slice
    (analyticAt_complex_matrix_det (fun i j => hf (ρ i) (σ j)))
  filter_upwards [hB] with x hx
  by_contra hne
  have hl := Matrix.rank_submatrix_le
    (A := (fun i j => f i j (fun k => (x k : ℂ)) : Matrix (Fin N) (Fin d) ℂ)) ρ σ
  have hr := Matrix.rank_of_det_ne_zero hne
  rw [Fintype.card_fin] at hr
  change Matrix.rank (fun i j => f (ρ i) (σ j) (fun k => (x k : ℂ))) ≤ _ at hl
  rw [hr] at hl
  exact (not_le_of_gt (hn x hx)) hl

end Release061

end

end OAI
