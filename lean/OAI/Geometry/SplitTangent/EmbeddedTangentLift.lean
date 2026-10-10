import Mathlib
import OAI.Geometry.SplitTangent.EmbeddedHolomorphicAtlas
import OAI.Geometry.SplitTangent.HolomorphicTangentMapAt
import OAI.Geometry.SplitTangent.Basic

namespace OAI

/-! Embedded Tangent Lift. -/

noncomputable section
open Set Filter Topology Bundle IsManifold
open scoped Manifold ContDiff
universe u
namespace SplitTangent.EmbeddedHolomorphicAtlas
variable {X : ComplexManifold.{u}} {r : ℕ} {Z : Set X.Carrier}
  (L : EmbeddedHolomorphicAtlas X r Z)

 
def retract (y : Z) : X.Carrier → Z := (L.chart y).symm ∘ L.forward y

lemma retract_eq {y z : Z} (hz : z∈(L.chart y).source) : L.retract y z.val=z := by
  dsimp only [retract,Function.comp_apply]
  rw [L.forward_eq y z hz]
  exact (L.chart y).left_inv hz

lemma retract_holomorphic {y z : Z} (hz : z∈(L.chart y).source) :
    letI := L.chartedSpace
    ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,Fin r → ℂ) ω (L.retract y) z.val := by
  let := L.chartedSpace
  let := L.isManifold
  have hy : L.chart y∈maximalAtlas 𝓘(ℂ,Fin r → ℂ) ω Z :=
    IsManifold.chart_mem_maximalAtlas y
  have hh := contMDiffAt_symm_of_mem_maximalAtlas hy ((L.chart y).map_source hz)
  have hF := L.forward_holomorphic y z hz
  rw [←L.forward_eq y z hz] at hh
  exact hh.comp z.val hF

lemma retract_comp_inclusion {y z : Z} (hz : z∈(L.chart y).source) :
    (L.retract y ∘ (Subtype.val : Z → X.Carrier)) =ᶠ[𝓝 z] id := by
  filter_upwards [(L.chart y).open_source.mem_nhds hz] with w hw
  exact L.retract_eq hw

lemma retract_mfderiv_leftInverse {y z : Z} (hz : z∈(L.chart y).source) :
    letI := L.chartedSpace
    (mfderiv (ModelWithCorners X) 𝓘(ℂ,Fin r → ℂ) (L.retract y) z.val).comp
      (mfderiv 𝓘(ℂ,Fin r → ℂ) (ModelWithCorners X) (Subtype.val : Z → X.Carrier) z)=
        ContinuousLinearMap.id ℂ (Fin r → ℂ) := by
  let := L.chartedSpace
  let := L.isManifold
  rw [←mfderiv_comp z ((L.retract_holomorphic hz).mdifferentiableAt (by simp))
    ((L.inclusion_holomorphic z).mdifferentiableAt (by simp)),
    (L.retract_comp_inclusion hz).mfderiv_eq,mfderiv_id]
  rfl

 
def tangentLift (y : Z) : Tangent X y.val →L[ℂ] (Fin r → ℂ) :=
  mfderiv (ModelWithCorners X) 𝓘(ℂ,Fin r → ℂ) (L.forward y) y.val

lemma tangentLift_leftInverse (y : Z) : letI := L.chartedSpace
    (L.tangentLift y).comp
      (mfderiv 𝓘(ℂ,Fin r → ℂ) (ModelWithCorners X) (Subtype.val : Z → X.Carrier) y)=
        ContinuousLinearMap.id ℂ (Fin r → ℂ) := by
  let := L.chartedSpace
  let := L.isManifold
  have he : (L.forward y ∘ (Subtype.val : Z → X.Carrier)) =ᶠ[𝓝 y]
      (extChartAt 𝓘(ℂ,Fin r → ℂ) y) := by
    filter_upwards [(L.chart y).open_source.mem_nhds (L.mem_source y)] with z hz
    exact L.forward_eq y z hz
  erw [tangentLift,←mfderiv_comp y
    ((L.forward_holomorphic y y (L.mem_source y)).mdifferentiableAt (by simp))
    ((L.inclusion_holomorphic y).mdifferentiableAt (by simp)),
    he.mfderiv_eq,mfderiv_extChartAt_self]
  rfl

lemma tangentLift_eq_retract {y z : Z} (hz : z∈(L.chart y).source)
    (v : Tangent X z.val) : letI := L.chartedSpace
    v∈LinearMap.range (mfderiv 𝓘(ℂ,Fin r → ℂ) (ModelWithCorners X)
      (Subtype.val : Z → X.Carrier) z).toLinearMap →
    L.tangentLift z v=mfderiv (ModelWithCorners X) 𝓘(ℂ,Fin r → ℂ) (L.retract y) z.val v := by
  let := L.chartedSpace
  rintro ⟨w,rfl⟩
  have h₁ := DFunLike.congr_fun (L.tangentLift_leftInverse z) w
  have h₂ := DFunLike.congr_fun (L.retract_mfderiv_leftInverse hz) w
  exact h₁.trans h₂.symm

lemma tangentLift_holomorphic {g : ℂ → Z} {σ : ∀t,Tangent X (g t).val}
    (hσ : ContMDiff 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun t => (⟨(g t).val,σ t⟩ : TangentBundle (ModelWithCorners X) X.Carrier))) :
    letI := L.chartedSpace
    letI := L.isManifold
    (∀t,σ t∈LinearMap.range (mfderiv 𝓘(ℂ,Fin r → ℂ) (ModelWithCorners X)
      (Subtype.val : Z → X.Carrier) (g t)).toLinearMap) →
    ContMDiff 𝓘(ℂ,ℂ) (𝓘(ℂ,Fin r → ℂ).prod 𝓘(ℂ,Fin r → ℂ)) ω
      (fun t => (⟨g t,L.tangentLift (g t) (σ t)⟩ : TangentBundle 𝓘(ℂ,Fin r → ℂ) Z)) := by
  let := L.chartedSpace
  let := L.isManifold
  intro hR
  have hc : Continuous g := by
    have hb := ((contMDiff_proj (IB := ModelWithCorners X) (n := ω)
      (TangentSpace (ModelWithCorners X))).comp hσ).continuous
    exact hb.subtype_mk (fun t => (g t).property)
  intro t
  have hh := (holomorphicAt_tangentMap (Y := L.manifold)
    (L.retract_holomorphic (L.mem_source (g t))) (σ t)).comp t (hσ t)
  apply hh.congr_of_eventuallyEq
  filter_upwards [hc.continuousAt.preimage_mem_nhds
    ((L.chart (g t)).open_source.mem_nhds (L.mem_source (g t)))] with w hw
  exact Bundle.TotalSpace.ext (L.retract_eq hw).symm
    (heq_of_eq (L.tangentLift_eq_retract hw (σ w) (hR w)))

end SplitTangent.EmbeddedHolomorphicAtlas

end

end OAI
