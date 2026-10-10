import Mathlib
import OAI.Analysis.SymmetricDomains.SemialgebraicBoundaryFiniteNash

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

noncomputable def complexGraphRealEquiv (r k : ℕ) :
    (Affine r × Affine k) ≃L[ℝ] ((Fin ((r+r)+k) → ℝ) × (Fin k → ℝ)) :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := fun p =>
      ((fun j => Sum.elim (complexRealEquiv r p.1) (fun i => (p.2 i).re)
          (finSumFinEquiv.symm j)), fun i => (p.2 i).im)
    invFun := fun p =>
      ((complexRealEquiv r).symm (fun j => p.1 (finSumFinEquiv (.inl j))),
        fun j => ⟨p.1 (finSumFinEquiv (.inr j)),p.2 j⟩)
    left_inv := by
      intro p
      apply Prod.ext
      · simpa only [Equiv.symm_apply_apply,Sum.elim_inl] using
          (complexRealEquiv r).symm_apply_apply p.1
      · funext j
        apply Complex.ext
        · simp only [Equiv.symm_apply_apply,Sum.elim_inr]
        · rfl
    right_inv := by
      intro p
      apply Prod.ext
      · funext j
        obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
        cases j with
        | inl j => simp only [Equiv.symm_apply_apply,Sum.elim_inl,
            (complexRealEquiv r).apply_symm_apply]
        | inr j => simp only [Equiv.symm_apply_apply,Sum.elim_inr]
      · rfl
    map_add' := by
      intro p q
      apply Prod.ext
      · funext j
        obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
        cases j <;> simp [map_add]
      · rfl
    map_smul' := by
      intro a p
      apply Prod.ext
      · funext j
        obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
        cases j <;> simp [map_smul]
      · funext j
        exact Complex.smul_im a (p.2 j) }

lemma complexGraphRealEquiv_snd {r k : ℕ} (p : Affine r × Affine k) :
    (complexGraphRealEquiv r k p).2 = fun i => (p.2 i).im := rfl

theorem generic_normal_graph_projection_injective {r k d : ℕ}
    (M : (Fin d → ℝ) →L[ℝ] (Affine r × Affine k))
    (hM : Function.Injective M) (h0 : ∀ v i, ((M v).2 i).im = 0) :
    Function.Injective ((ContinuousLinearMap.fst ℝ (Fin ((r+r)+k) → ℝ) (Fin k → ℝ)).comp
      ((complexGraphRealEquiv r k).toContinuousLinearMap.comp M)) := by
  intro a b hab
  apply hM
  apply (complexGraphRealEquiv r k).injective
  apply Prod.ext hab
  change (complexGraphRealEquiv r k (M a)).2 = (complexGraphRealEquiv r k (M b)).2
  simp only [complexGraphRealEquiv_snd,h0]
end Release061

end

end OAI
