import OAI.Combinatorics.InfiniteMatroid.CorollaryModel
import OAI.Combinatorics.InfiniteMatroid.Matroid
import OAI.Combinatorics.InfiniteMatroid.DoubleRay

namespace OAI

namespace InfiniteMatroidCounterexample
open Set Matroid

lemma BasisSystem.isUniform {α : Type*} (S : BasisSystem α) : IsUniform S.matroid := by
  intro X hX
  obtain ⟨I, hI⟩ := S.matroid.exists_isBasis X
  by_cases hb : S.matroid.IsBase I
  · exact Or.inr (hb.spanning_of_superset hI.subset hX)
  · left
    have hXI : X ⊆ I := fun e he ↦ hI.mem_of_insert_indep he
      (S.insert_indep_of_not_base hI.indep hb e)
    exact (Subset.antisymm hXI hI.subset) ▸ hI.indep

lemma mapEquiv_trans {α β γ : Type*} (M : Matroid α) (e : α ≃ β) (f : β ≃ γ) :
    (M.mapEquiv e).mapEquiv f = M.mapEquiv (e.trans f) := by
  apply Matroid.ext_indep
  · simp only [Matroid.mapEquiv_ground_eq, image_image, Equiv.trans_apply]
    rfl
  · intro I _
    simp only [Matroid.mapEquiv_indep_iff, image_image]
    rfl

lemma rayMatroid_isPartitional {α : Type} (Q : Matroid (α × Bool))
    (hQ : IsUniform Q) (p : Bool) : IsPartitional (rayMatroid Q p) := by
  refine ⟨Vertex p, fun _ ↦ α × Bool, fun _ ↦ Q,
    (Equiv.sigmaEquivProd (Vertex p) (α × Bool)).trans (componentEquiv α p),
    fun _ ↦ hQ, ?_⟩
  exact mapEquiv_trans _ _ _

end InfiniteMatroidCounterexample

end OAI
