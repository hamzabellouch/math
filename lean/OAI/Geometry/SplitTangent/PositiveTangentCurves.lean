import Mathlib
import OAI.Geometry.SplitTangent.BoxTransportBase
import OAI.Geometry.SplitTangent.BracketIntegrability
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.BoxFirstTransport
import OAI.Geometry.SplitTangent.TangentRationalChains
import OAI.Geometry.SplitTangent.RationalVariation

namespace OAI

/-! Positive Tangent Curves. -/

noncomputable section
open Set Filter Topology Bundle
open scoped ContDiff Manifold
universe u
namespace SplitTangent

 

def PointedGenerated {X : ComplexManifold.{u}} (g : RationalCurve X)
    (D : ∀x : X.Carrier, Submodule ℂ (Tangent X x)) : Prop :=
  ∀ v : Tangent X (g.finite 1), v∈D (g.finite 1) →
    ∃σ : CurveTangentSection g,
      (∀z, σ.finite z∈D (g.finite z)) ∧
      (∀z, σ.infinity z∈D (g.infinity z)) ∧
      σ.finite 0=0 ∧ σ.finite 1=v

namespace TangentBox
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {g : RationalCurve X}
  (B : TangentBox S g)

lemma firstFactor_tangentTo (b : ℂ) : (B.firstFactor b).TangentTo S.first := by
  exact B.horizontal_tangent false b

 

theorem firstFactor_pointedGenerated
    (hg : PointedGenerated g S.first) : PointedGenerated (B.firstFactor 1) S.first := by
  intro v hv
  have hv' : v∈S.first (g.finite 1) := by
    change v∈S.first (B.chart false false (1,1)) at hv
    erw [B.finite_diagonal 1] at hv
    exact hv
  obtain ⟨σ,σf,σi,σ0,σ1⟩ := hg v hv'
  let τ := ((B.firstMap 1).mapSection σ).project S
  refine ⟨τ,fun z => CurveTangentSection.project_mem_first_finite S _ z,
    fun z => CurveTangentSection.project_mem_first_infinity S _ z,?_,?_⟩
  · change S.projector _ ((B.firstMap 1).finite 0 (σ.finite 0))=0
    rw [σ0,map_zero,map_zero]
  · change S.projector _ ((B.firstMap 1).finite 1 (σ.finite 1))=v
    rw [σ1,B.firstMap_normalized]
    have hfix := (S.mem_first_iff (g.finite 1) v).mp hv'
    erw [B.firstFactor_diagonal,hfix,hfix]

end TangentBox

namespace RationalFamily
variable {X T : ComplexManifold.{u}} (G : RationalFamily X T)

theorem pointedGenerated_of_submersive (S : TangentSplitting X) (τ : T.Carrier)
    (hτ : Function.Surjective (mfderiv (ModelWithCorners T)
      ((ModelWithCorners X).prod (ModelWithCorners X)) (G.twoPointEvaluation 0 1) τ)) :
    PointedGenerated (G.curve τ) S.first :=
  fun v hv => G.exists_first_section_zero_value S hτ v hv

end RationalFamily

namespace TangentSplitting

 

theorem exists_positive_tangent_curve {X : ComplexManifold.{u}}
    [CompactSpace X.Carrier] (S : TangentSplitting X) (e : ProjectiveEmbedding X)
    (hRC : RationallyConnected e) (hdim : 0<X.dim) :
    ∃h : RationalCurve X, h.TangentTo S.first ∧ PointedGenerated h S.first := by
  obtain ⟨T,hT,G,hG⟩ := hRC.exists_submersive_family e hdim
  let := hT
  let τ : T.Carrier := Classical.arbitrary _
  obtain ⟨B⟩ := S.exists_projective_tangent_box e (G.curve τ)
  exact ⟨B.firstFactor 1,B.firstFactor_tangentTo 1,
    B.firstFactor_pointedGenerated (G.pointedGenerated_of_submersive S τ (hG τ))⟩

 

theorem exists_positive_tangent_curves {X : ComplexManifold.{u}}
    [CompactSpace X.Carrier] (S : TangentSplitting X) (e : ProjectiveEmbedding X)
    (hRC : RationallyConnected e) (hdim : 0<X.dim) :
    (∃h : RationalCurve X, h.TangentTo S.first ∧ PointedGenerated h S.first) ∧
    (∃h : RationalCurve X, h.TangentTo S.second ∧ PointedGenerated h S.second) := by
  refine ⟨S.exists_positive_tangent_curve e hRC hdim,?_⟩
  simpa only [S.swap_first] using S.swap.exists_positive_tangent_curve e hRC hdim

end TangentSplitting
end SplitTangent

end

end OAI
