import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.NormIteratedFDerivCompLinear

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal
namespace YauCounterexamples
lemma finite_sum_tsupport_subset {E I : Type*} [TopologicalSpace E]
    {V : Set E} (s : Finset I) (f : I → E → ℝ)
    (hf : ∀ i ∈ s, tsupport (f i) ⊆ V) :
    tsupport (fun x => ∑ i ∈ s, f i x) ⊆ V := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (tsupport_add _ _).trans (union_subset (hf a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))))

lemma finiteWaveSuperposition_tsupport {E I : Type*} [TopologicalSpace E] [Fintype I]
    {O : Set E} {U : I → Fin 3 → E → ℂ}
    (hU : ∀ i ℓ, tsupport (U i ℓ) ⊆ O) (γ : I → Fin 3 → ℂ) :
    tsupport (finiteWaveSuperposition (fun _ => (0 : ℝ)) U γ) ⊆ O := by
  classical
  have he : finiteWaveSuperposition (fun _ => (0 : ℝ)) U γ =
      fun x => ∑ i, ∑ ℓ, (γ i ℓ*U i ℓ x).re := by
    funext x; exact zero_add _
  rw [he]
  apply finite_sum_tsupport_subset
  intro i _
  apply finite_sum_tsupport_subset
  intro ℓ _
  exact (tsupport_comp_subset (g := Complex.re) rfl (fun x => γ i ℓ*U i ℓ x)).trans
    (tsupport_mul_subset_right.trans (hU i ℓ))
end YauCounterexamples
end

end OAI
