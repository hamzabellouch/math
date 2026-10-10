import Mathlib
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.SmoothLeafManifold
import OAI.Geometry.SplitTangent.SmoothLeafQuotient
import OAI.Geometry.SplitTangent.QuotientSubmersions

namespace OAI

/-! Smooth Leaf Projection. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  [CompactSpace X.Carrier] [ConnectedSpace X.Carrier]
  {L : LeafJetAtlas S} (M : LeafJetAtlas S.swap) {e : ProjectiveEmbedding X}
  {hRC : RationallyConnected e} {hdim : 0<X.dim}
namespace QuotientChartData
variable {i : X.Carrier} (D : L.QuotientChartData e hRC hdim i) (x₀ : X.Carrier)

lemma normalized_comp_quotient_mfderiv {x : X.Carrier}
    (hx : L.leafQuotient e hRC hdim x∈(D.normalized M x₀).source) :
    mfderiv (ModelWithCorners X) 𝓘(ℂ,Fin (Module.finrank ℂ (S.second x₀)) → ℂ)
      (D.normalized M x₀ ∘ L.leafQuotient e hRC hdim) x=
    (D.quotientRankEquiv M x₀).toContinuousLinearMap.comp
      (mfderiv (ModelWithCorners X) 𝓘(ℂ,S.SecondModel i)
        (D.chart ∘ L.leafQuotient e hRC hdim) x) := by
  change mfderiv _ _ ((D.quotientRankEquiv M x₀).toContinuousLinearMap ∘
    (D.chart ∘ L.leafQuotient e hRC hdim)) x=_
  have hc := mfderiv_comp x (D.quotientRankEquiv M x₀).toContinuousLinearMap.mdifferentiableAt
    ((D.chart_comp_quotient_contMDiffAt hx.1).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv,ContinuousLinearMap.fderiv] at hc
  exact hc

lemma normalized_comp_quotient_submersion {x : X.Carrier}
    (hx : L.leafQuotient e hRC hdim x∈(D.normalized M x₀).source) :
    Function.Surjective (mfderiv (ModelWithCorners X)
      𝓘(ℂ,Fin (Module.finrank ℂ (S.second x₀)) → ℂ)
      (D.normalized M x₀ ∘ L.leafQuotient e hRC hdim) x) := by
  rw [D.normalized_comp_quotient_mfderiv M x₀ hx]
  exact (D.quotientRankEquiv M x₀).surjective.comp (D.chart_comp_quotient_submersion hx.1).2

lemma normalized_comp_quotient_kernel {x : X.Carrier}
    (hx : L.leafQuotient e hRC hdim x∈(D.normalized M x₀).source) :
    LinearMap.ker (mfderiv (ModelWithCorners X)
      𝓘(ℂ,Fin (Module.finrank ℂ (S.second x₀)) → ℂ)
      (D.normalized M x₀ ∘ L.leafQuotient e hRC hdim) x).toLinearMap=S.first x := by
  rw [D.normalized_comp_quotient_mfderiv M x₀ hx]
  trans LinearMap.ker (mfderiv (ModelWithCorners X) 𝓘(ℂ,S.SecondModel i)
    (D.chart ∘ L.leafQuotient e hRC hdim) x).toLinearMap
  · ext v
    change (D.quotientRankEquiv M x₀) _=0 ↔ _=0
    exact (D.quotientRankEquiv M x₀).map_eq_zero_iff
  · exact D.chart_comp_quotient_kernel M hx.1
end QuotientChartData

namespace SmoothLeafManifold
variable (x₀ : X.Carrier)
  (hAll : ∀x,L.leafQuotient e hRC hdim x∈L.smoothLeafLocus e hRC hdim)

def projection (x : X.Carrier) : (manifold (L := L) (e := e) (hRC := hRC) (hdim := hdim) M x₀).Carrier :=
  ⟨L.leafQuotient e hRC hdim x,hAll x⟩

lemma projection_continuous : Continuous (projection M x₀ hAll) :=
  (L.continuous_leafQuotient e hRC hdim).subtype_mk _

lemma projection_surjective : Function.Surjective (projection M x₀ hAll) := by
  intro q
  obtain ⟨x,hx⟩ := L.surjective_leafQuotient e hRC hdim q.val
  exact ⟨x,Subtype.ext hx⟩

lemma projection_holomorphic :
    ContMDiff (ModelWithCorners X)
      (ModelWithCorners (manifold (L := L) (e := e) (hRC := hRC) (hdim := hdim) M x₀)) ω
      (projection M x₀ hAll) := by
  intro x
  rw [contMDiffAt_iff_target]
  refine ⟨(projection_continuous M x₀ hAll).continuousAt,?_⟩
  let q := projection M x₀ hAll x
  change ContMDiffAt (ModelWithCorners X)
    𝓘(ℂ,Fin (Module.finrank ℂ (S.second x₀)) → ℂ) ω
    ((selectedChart q).2.normalized M x₀ ∘ L.leafQuotient e hRC hdim) x
  apply (selectedChart q).2.normalized_comp_quotient_contMDiffAt
  rw [QuotientChartData.normalized_source]
  exact selectedChart_mem q

lemma projection_mfderiv (x : X.Carrier) :
    mfderiv (ModelWithCorners X)
      (ModelWithCorners (manifold (L := L) (e := e) (hRC := hRC) (hdim := hdim) M x₀))
      (projection M x₀ hAll) x=
    mfderiv (ModelWithCorners X) 𝓘(ℂ,Fin (Module.finrank ℂ (S.second x₀)) → ℂ)
      ((selectedChart (projection M x₀ hAll x)).2.normalized M x₀ ∘ L.leafQuotient e hRC hdim) x := by
  let Y := manifold (L := L) (e := e) (hRC := hRC) (hdim := hdim) M x₀
  let q := projection M x₀ hAll x
  have hd := mfderiv_comp x (mdifferentiableAt_extChartAt (I := ModelWithCorners Y)
    (mem_chart_source (Model Y) q))
    ((projection_holomorphic M x₀ hAll x).mdifferentiableAt (by simp))
  rw [mfderiv_extChartAt_self] at hd
  dsimp only [q] at hd
  erw [ContinuousLinearMap.id_comp] at hd
  exact hd.symm

lemma projection_submersion (x : X.Carrier) :
    Function.Surjective (mfderiv (ModelWithCorners X)
      (ModelWithCorners (manifold (L := L) (e := e) (hRC := hRC) (hdim := hdim) M x₀))
      (projection M x₀ hAll) x) := by
  rw [projection_mfderiv]
  apply QuotientChartData.normalized_comp_quotient_submersion
  rw [QuotientChartData.normalized_source]
  exact selectedChart_mem (projection M x₀ hAll x)

lemma projection_kernel (x : X.Carrier) :
    LinearMap.ker (mfderiv (ModelWithCorners X)
      (ModelWithCorners (manifold (L := L) (e := e) (hRC := hRC) (hdim := hdim) M x₀))
      (projection M x₀ hAll) x).toLinearMap=S.first x := by
  rw [projection_mfderiv]
  apply QuotientChartData.normalized_comp_quotient_kernel
  rw [QuotientChartData.normalized_source]
  exact selectedChart_mem (projection M x₀ hAll x)

end SmoothLeafManifold
end SplitTangent.LeafJetAtlas

end

end OAI
