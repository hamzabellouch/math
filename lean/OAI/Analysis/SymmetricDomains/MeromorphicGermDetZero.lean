import Mathlib
import OAI.Analysis.SymmetricDomains.AnalyticNashRank

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

theorem independent_rows_nonzero_minor {K : Type*} [Field K] {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) K) (hA : LinearIndependent K A) :
    ∃ σ : Fin n → Fin d, Matrix.det (fun i j => A i (σ j)) ≠ 0 := by
  classical
  have hspan : Submodule.span K (range A.col) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_cols,Matrix.rank_eq_finrank_span_row]
    change Module.finrank K (Submodule.span K (range A)) = _
    rw [finrank_span_eq_card hA,Module.finrank_pi,Fintype.card_fin]
  let b := Basis.ofSpan (s := range A.col) (show ⊤ ≤ Submodule.span K (range A.col) by rw [hspan])
  let b' := b.reindex (b.indexEquiv (Pi.basisFun K (Fin n)))
  have hb : ∀ i, ∃ j, A.col j = b' i := by
    intro i
    apply Basis.ofSpan_subset (show ⊤ ≤ Submodule.span K (range A.col) by rw [hspan])
    refine ⟨(b.indexEquiv (Pi.basisFun K (Fin n))).symm i,?_⟩
    change b _ = b.reindex _ i
    simp only [Basis.reindex_apply]
  choose σ hσ using hb
  refine ⟨σ,?_⟩
  apply Matrix.nonsingular_iff_det_ne_zero.mp
  apply Matrix.Nonsingular.of_linearIndependent_col
  have heq : (fun j i => A i (σ j)) = b' := funext hσ
  change LinearIndependent K (fun j i => A i (σ j))
  rw [heq]
  exact b'.linearIndependent

theorem meromorphicGerm_det_eq_zero_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {n : ℕ}
    (f : Fin n → Fin n → E → ℂ) (hf : ∀ i j, AnalyticAt ℂ (f i j) 0) :
    Matrix.det (fun i j => meromorphicGermOf (f i j) (hf i j)) = 0 ↔
      (fun z => Matrix.det (fun i j => f i j z)) =ᶠ[𝓝 (0 : E)] 0 := by
  let A : Matrix (Fin n) (Fin n) (AnalyticGerm E) := fun i j => analyticGermOf E (f i j) (hf i j)
  have hfield : Matrix.det (fun i j => meromorphicGermOf (f i j) (hf i j)) =
      algebraMap (AnalyticGerm E) (MeromorphicGermField E) A.det := by
    exact ((algebraMap (AnalyticGerm E) (MeromorphicGermField E)).map_det A).symm
  rw [hfield,map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  have hgerm : (A.det).val = ((fun z => Matrix.det (fun i j => f i j z)) : Filter.Germ (𝓝 (0:E)) ℂ) := by
    let H := Filter.Germ.coeRingHom (𝓝 (0:E)) (R := ℂ)
    have h := (analyticGermRing E).subtype.map_det A
    calc
      (A.det).val = ((analyticGermRing E).subtype.mapMatrix A).det := h
      _ = (H.mapMatrix f).det := rfl
      _ = H (Matrix.det f) := (H.map_det f).symm
      _ = _ := congrArg H (funext (fun z => (Pi.evalRingHom (fun _ : E => ℂ) z).map_det f))
  constructor
  · intro h
    apply Filter.Germ.coe_eq.mp
    rw [← hgerm,h]
    rfl
  · intro h
    apply Subtype.ext
    rw [hgerm]
    exact Filter.Germ.coe_eq.mpr h

end Release061

end

end OAI
