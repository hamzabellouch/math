import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic

namespace OAI

/-! Leaf Rank. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent
namespace AlignedProductChart
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup B] [NormedSpace ℂ B]

def firstLinearMap (P : AlignedProductChart S A B) (y : X.Carrier) : S.first y →ₗ[ℂ] A :=
  (ContinuousLinearMap.fst ℂ A B).toLinearMap.comp
    ((mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart y).toLinearMap.comp (S.first y).subtype)

lemma firstLinearMap_bijective (P : AlignedProductChart S A B) {y : X.Carrier}
    (hy : y∈P.chart.source) : Function.Bijective (P.firstLinearMap y) := by
  have hz : ∀ v : S.first y,
      (mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart y v.val).2=0 := by
    intro v
    have hm := Submodule.mem_map_of_mem (f :=
      (mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart y).toLinearMap) v.property
    rw [P.first y hy] at hm
    exact hm
  constructor
  · intro v w he
    apply Subtype.ext
    apply P.mdifferentiable.mfderiv_injective hy
    exact Prod.ext he ((hz v).trans (hz w).symm)
  · intro a
    have ha : (a,0)∈Submodule.map
        (mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart y).toLinearMap (S.first y) := by
      rw [P.first y hy]
      rfl
    obtain ⟨v,hv,he⟩ := ha
    exact ⟨⟨v,hv⟩,congrArg Prod.fst he⟩

lemma first_finrank (P : AlignedProductChart S A B) {y : X.Carrier}
    (hy : y∈P.chart.source) : Module.finrank ℂ (S.first y)=Module.finrank ℂ A :=
  (LinearEquiv.ofBijective (P.firstLinearMap y) (P.firstLinearMap_bijective hy)).finrank_eq

end AlignedProductChart
namespace LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} (L : LeafJetAtlas S)

include L in
lemma first_rank_locally_constant : IsLocallyConstant (fun x => Module.finrank ℂ (S.first x)) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  filter_upwards [(L.chart x).chart.open_source.mem_nhds (L.mem_source x)] with y hy
  exact ((L.chart x).first_finrank hy).trans ((L.chart x).first_finrank (L.mem_source x)).symm

include L in
lemma first_rank_eq [PreconnectedSpace X.Carrier] (x y : X.Carrier) :
    Module.finrank ℂ (S.first x)=Module.finrank ℂ (S.first y) :=
  L.first_rank_locally_constant.apply_eq_of_preconnectedSpace x y

end LeafJetAtlas
end SplitTangent

end

end OAI
