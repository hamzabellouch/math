import Mathlib
import OAI.Geometry.SplitTangent.FoliationLeaves

namespace OAI

/-! Leaf Topology. -/

noncomputable section
open Set Filter Topology
universe u v w
namespace PlaqueSystem
variable {ι : Type v} {X : Type u} [TopologicalSpace X]
  {A B : ι → Type w} [∀i,TopologicalSpace (A i)] [∀i,TopologicalSpace (B i)]
  (P : PlaqueSystem X A B)

lemma related_connected_subset {x y : X} (h : P.Related x y) :
    ∃Z, Z⊆P.leaf x ∧ x∈Z ∧ y∈Z ∧ IsPreconnected Z := by
  obtain ⟨i,b,U,hU,hT,a,ha,c,hc,hx,hy⟩ := h
  let f : A i → X := fun t => (P.chart i).symm (t,b)
  have hf : ContinuousOn f U := (P.chart i).symm.continuousOn.comp
    ((continuous_id.prodMk continuous_const).continuousOn) (fun t ht => hT t ht)
  refine ⟨f '' U,?_,⟨a,ha,hx⟩,⟨c,hc,hy⟩,hU.image f hf⟩
  rintro z ⟨d,hd,rfl⟩
  apply Relation.ReflTransGen.single
  exact ⟨i,b,U,hU,hT,a,ha,d,hd,hx,rfl⟩

lemma reachable_connected_subset {x y : X} (h : P.Reachable x y) :
    ∃Z, Z⊆P.leaf x ∧ x∈Z ∧ y∈Z ∧ IsPreconnected Z := by
  induction h with
  | refl => exact ⟨{x},by intro z hz; subst z; exact Relation.ReflTransGen.refl,by simp,by simp,isPreconnected_singleton⟩
  | @tail y z hyz h ih =>
    obtain ⟨U,hU,hx,hy,hUc⟩ := ih
    obtain ⟨V,hV,hy',hz,hVc⟩ := P.related_connected_subset h
    refine ⟨U∪V,?_,Or.inl hx,Or.inr hz,hUc.union y hy hy' hVc⟩
    intro w hw
    rcases hw with hw | hw
    · exact hU hw
    · exact Relation.ReflTransGen.trans hyz (hV hw)

lemma leaf_isConnected (x : X) : IsConnected (P.leaf x) := by
  refine ⟨⟨x,Relation.ReflTransGen.refl⟩,isPreconnected_of_forall x ?_⟩
  intro y hy
  exact P.reachable_connected_subset hy

lemma leaf_eq_of_mem {x y : X} (h : y∈P.leaf x) : P.leaf y=P.leaf x := by
  ext z
  exact ⟨fun hz => Relation.ReflTransGen.trans h hz,
    fun hz => Relation.ReflTransGen.trans (Reachable.symm P h) hz⟩

end PlaqueSystem

end

end OAI
