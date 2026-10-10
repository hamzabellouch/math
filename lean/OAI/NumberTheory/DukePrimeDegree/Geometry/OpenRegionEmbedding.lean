import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixBoxes

namespace OAI

/-! # An injective coordinate image for a local homeomorphism -/

open Set
namespace DukePrimeDegree

lemma openEmbedding_on_coordinate_image {A B X : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]
    (e : A → B) (f : B → X) (V : Set A)
    (he : Topology.IsOpenEmbedding e) (hf : IsLocalHomeomorph f) (hV : IsOpen V)
    (hcomp : Topology.IsOpenEmbedding (V.domRestrict (f ∘ e))) :
    Topology.IsOpenEmbedding ((e '' V).domRestrict f) := by
  have hU : IsOpen (e '' V) := he.isOpenMap V hV
  apply Topology.isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
  refine ⟨hf.continuous.comp continuous_subtype_val,?_,hf.isOpenMap.comp hU.isOpenEmbedding_subtypeVal.isOpenMap⟩
  intro x y hxy
  obtain ⟨v,hv,hvx⟩ := x.prop
  obtain ⟨w,hw,hwy⟩ := y.prop
  have hvw : (⟨v,hv⟩ : V) = ⟨w,hw⟩ := hcomp.injective (by
    change f (e v) = f (e w)
    rw [hvx,hwy]
    exact hxy)
  exact Subtype.ext (hvx.symm.trans ((congrArg e (congrArg Subtype.val hvw)).trans hwy))

end DukePrimeDegree

end OAI
