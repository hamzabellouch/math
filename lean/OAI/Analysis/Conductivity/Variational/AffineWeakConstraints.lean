import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set

lemma constraint_of_mem_weak_closure
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S T : Set V} (hT : IsClosed T) (hc : Convex ℝ T) (hST : S ⊆ T)
    {z : V} (hz : toWeakSpace ℝ V z ∈ closure (toWeakSpace ℝ V '' S)) : z ∈ T := by
  have hz' := closure_mono (image_mono hST) hz
  rw [← hc.toWeakSpace_closure ℝ,hT.closure_eq] at hz'
  obtain ⟨x,hx,hxz⟩ := hz'
  exact (toWeakSpace ℝ V).injective hxz ▸ hx

lemma submodule_constraint_of_mem_weak_closure
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (M : Submodule ℝ W) (hM : IsClosed (M : Set W))
    (L : V →L[ℝ] W) (w : W) {S : Set V}
    (hS : ∀ z ∈ S, L z-w ∈ M) {z : V}
    (hz : toWeakSpace ℝ V z ∈ closure (toWeakSpace ℝ V '' S)) : L z-w ∈ M := by
  apply constraint_of_mem_weak_closure
    (T := {z : V | L z-w ∈ M}) _ _ hS hz
  · exact hM.preimage (L.continuous.sub continuous_const)
  · convert ((M.convex.translate_preimage_left (-w)).linear_preimage L.toLinearMap) using 1
    ext x
    simp only [mem_ofPred_eq,mem_preimage,ContinuousLinearMap.coe_coe,sub_eq_add_neg,SetLike.mem_coe]

end ScalarConductivity

end
end

end OAI
