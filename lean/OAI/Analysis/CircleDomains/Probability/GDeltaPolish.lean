import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.GDelta.Basic

namespace OAI

/-! A G-delta subset of a Polish space is Polish. It embeds as the closed
set of compatible tuples in the product of its open supersets. -/
open Set Function Topology
noncomputable section
namespace CircleDomainRigidity

lemma polishSpace_of_isGDelta {X : Type*} [TopologicalSpace X] [PolishSpace X]
    {s : Set X} (hs : IsGδ s) : PolishSpace s := by
  obtain ⟨U, hU, rfl⟩ := hs.eq_iInter_nat
  let : ∀ n, PolishSpace (U n) := fun n => (hU n).polishSpace
  let e : (⋂ n, U n) → X × (∀ n, U n) :=
    fun x => (x.val, fun n => ⟨x.val, mem_iInter.mp x.property n⟩)
  have hec : Continuous e := by fun_prop
  have he : IsEmbedding e :=
    .of_comp hec continuous_fst (show IsEmbedding (Prod.fst ∘ e) from .subtypeVal)
  have hr : range e = {p : X × (∀ n, U n) | ∀ n, p.1 = (p.2 n).val} := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact fun _ => rfl
    · intro hp
      refine ⟨⟨p.1, mem_iInter.mpr (fun n => ?_)⟩, ?_⟩
      · rw [hp n]
        exact (p.2 n).property
      · apply Prod.ext
        · rfl
        · funext n
          exact Subtype.ext (hp n)
  have hc : IsClosed (range e) := by
    rw [hr, ofPred_forall]
    exact isClosed_iInter (fun n => isClosed_eq continuous_fst
      ((continuous_apply n).comp continuous_snd |>.subtype_val))
  exact (show IsClosedEmbedding e from ⟨he, hc⟩).polishSpace

end CircleDomainRigidity

end

end OAI
