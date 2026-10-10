import Mathlib
import OAI.Geometry.SplitTangent.Basic

namespace OAI

/-! Open Manifold. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold
universe u
namespace SplitTangent
namespace OpenManifold
variable {d : ℕ} (U : Set (Fin d → ℂ)) (hU : IsOpen U) (hne : U.Nonempty)

abbrev Carrier := ULift.{u} U
include hne in
theorem nonempty : Nonempty (Carrier.{u} U) := ⟨⟨⟨hne.choose,hne.choose_spec⟩⟩⟩
def val (x : Carrier.{u} U) : Fin d → ℂ := x.down.val
include hU in
lemma isOpenEmbedding_val : IsOpenEmbedding (val (U := U) : Carrier.{u} U → _) :=
  hU.isOpenEmbedding_subtypeVal.comp Homeomorph.ulift.isOpenEmbedding

def manifold : ComplexManifold.{u} where
  dim := d
  Carrier := Carrier.{u} U
  charts := by
    letI := nonempty U hne
    exact (isOpenEmbedding_val U hU).singletonChartedSpace
  secondCountable := Homeomorph.ulift.isInducing.secondCountableTopology
  holomorphicAtlas := by
    let := nonempty U hne
    exact (isOpenEmbedding_val U hU).isManifold_singleton

lemma val_holomorphic : ContMDiff (ModelWithCorners (manifold.{u} U hU hne))
    𝓘(ℂ, Fin d → ℂ) ω (fun x : (manifold.{u} U hU hne).Carrier => val U x) := by
  let := nonempty U hne
  exact contMDiff_isOpenEmbedding (isOpenEmbedding_val U hU)

lemma val_mem (x : (manifold.{u} U hU hne).Carrier) : val (U := U) x∈U := x.down.property

lemma range_val : Set.range (val (U := U) : (manifold.{u} U hU hne).Carrier → _)=U := by
  ext x
  exact ⟨fun ⟨y,hy⟩ => hy ▸ y.down.property, fun hx => ⟨⟨⟨x,hx⟩⟩,rfl⟩⟩

lemma val_mfderiv_bijective (x : (manifold.{u} U hU hne).Carrier) :
    Function.Bijective (mfderiv (ModelWithCorners (manifold.{u} U hU hne))
      𝓘(ℂ, Fin d → ℂ) (fun y : (manifold.{u} U hU hne).Carrier => val U y) x) := by
  have H := (mdifferentiable_chart (I := ModelWithCorners (manifold.{u} U hU hne)) x).mfderiv_bijective
    (mem_chart_source (Model (manifold.{u} U hU hne)) x)
  exact H

end OpenManifold
end SplitTangent

end

end OAI
