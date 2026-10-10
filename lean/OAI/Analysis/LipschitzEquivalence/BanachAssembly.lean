import OAI.Analysis.LipschitzEquivalence.SlotBudget

namespace OAI

universe uE uX uY

noncomputable section

namespace LipschitzCounterexample
open Filter in
instance : TopologicalSpace.SeparableSpace RealL2 := by
  let S : Set RealL2 := ⋃ i : ℕ, Set.range (lp.single (E := fun _ : ℕ => ℝ) 2 i)
  have hs : TopologicalSpace.IsSeparable S :=
    TopologicalSpace.IsSeparable.iUnion (fun i =>
      TopologicalSpace.isSeparable_range (lp.isometry_single i).continuous)
  have hd : Dense (Submodule.span ℝ S : Set RealL2) := by
    intro s
    apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by simp) s).tendsto_sum_nat
    apply Eventually.of_forall
    intro n
    apply subset_closure
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.subset_span
    exact Set.mem_iUnion.2 ⟨i, ⟨s i, rfl⟩⟩
  exact hd.isSeparable_iff.mp hs.span

namespace Criterion
open WeakSequences
open scoped NNReal

theorem contains_of_isometry_equiv {E : Type uE} {X : Type uX} {Y : Type uY} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (j : E →ₗᵢ[ℝ] X) (e : X ≃L[ℝ] Y) : ContainsLinearCopy E Y := by
  refine ⟨e.toContinuousLinearMap.comp j.toContinuousLinearMap, 1/(‖e.symm.toContinuousLinearMap‖+1),
    by positivity, ?_⟩
  intro z
  have he := e.symm.toContinuousLinearMap.le_opNorm (e (j z))
  change ‖e.symm (e (j z))‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e (j z)‖ at he
  simp only [e.symm_apply_apply, j.norm_map] at he
  change 1/(‖e.symm.toContinuousLinearMap‖+1)*‖z‖ ≤ ‖e (j z)‖
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ (by positivity : 0 < ‖e.symm.toContinuousLinearMap‖+1)).2
  nlinarith [norm_nonneg (e (j z))]

theorem assemble {U : Type} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U]
    (q : Free U RealL2 →L[ℝ] U)
    (h : Domain U RealL2 ≃ U)
    (hlin : ∀ x : Domain U RealL2, q (FreeSpace.point x) = h x - x.fst)
    (h0 : h 0 = 0)
    (hh : LipschitzWith (26/25) h) (hi : LipschitzWith (25/24) h.symm)
    (hq : ‖q‖ ≤ 51/25)
    (hA : WeakSequentiallyComplete (Free U RealL2))
    (hcc : CompletelyContinuous q) : MainClaim := by
  let X : SeparableRealBanach := { Carrier := WeightedGraph.Space (Q1 q) }
  let Y : SeparableRealBanach := { Carrier := WeightedGraph.Space q }
  let Ψ : X.Carrier ≃ Y.Carrier := graphEquiv q h hlin h0 hh hi
  have hno : ¬ ContainsLinearCopy C0L2 Y.Carrier := by
    rintro ⟨S, a, ha, hS⟩
    exact GraphObstruction.graph_no_c0L2 q hA hcc S a ha hS
  refine ⟨X, Y, Ψ, ?_, ?_, ⟨c0Embed q⟩, hno⟩
  · have hb : max (1 + max ‖q‖₊ 1) (26/25) ≤ (76/25 : ℝ≥0) := by
      have hmax : max ‖q‖ 1 ≤ (51/25 : ℝ) := max_le hq (by norm_num)
      have hr : max (1 + max ‖q‖ 1) (26/25) ≤ (76/25 : ℝ) :=
        max_le (by linarith) (by norm_num)
      exact_mod_cast hr
    have ha : max (1+2*‖q‖₊*(25/24)) (25/24) ≤ (21/4 : ℝ≥0) := by
      have hr : max (1+2*‖q‖*(25/24)) (25/24) ≤ (21/4 : ℝ) :=
        max_le (by linarith) (by norm_num)
      exact_mod_cast hr
    have hf := (lipschitz_graphEquiv q h hlin h0 hh hi).weaken hb
    have hg := (lipschitz_graphEquiv_symm q h hlin h0 hh hi).weaken ha
    intro s t
    have hf' := hf.norm_sub_le s t
    have hg' := hg.norm_sub_le (Ψ s) (Ψ t)
    change ‖Ψ.symm (Ψ s)-Ψ.symm (Ψ t)‖ ≤ (21/4 : ℝ≥0) * ‖Ψ s-Ψ t‖ at hg'
    simp only [Equiv.symm_apply_apply] at hg'
    change ‖Ψ s-Ψ t‖ ≤ (76/25 : ℝ≥0) * ‖s-t‖ at hf'
    norm_num only [NNReal.coe_div, NNReal.coe_ofNat] at hf' hg'
    constructor
    · linarith
    · exact hf'
  · refine ⟨fun e => hno (contains_of_isometry_equiv (c0Embed q) e)⟩

end Criterion
end LipschitzCounterexample

end

end OAI
