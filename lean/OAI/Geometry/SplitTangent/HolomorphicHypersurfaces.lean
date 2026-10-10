import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.LeafPlaques
import OAI.Geometry.SplitTangent.Basic

namespace OAI

/-! Holomorphic Hypersurfaces. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent

 
def LocallyHolomorphicZeroSet (X : ComplexManifold.{u}) (Z : Set X.Carrier) : Prop :=
  ∀x,∃U : Set X.Carrier,IsOpen U ∧ x∈U ∧ ∃f : X.Carrier → ℂ,
    ContMDiffOn (ModelWithCorners X) 𝓘(ℂ,ℂ) ω f U ∧ ∀y∈U,y∈Z ↔ f y=0

namespace AlignedProductChart
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  {A B : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

omit [CompleteSpace A] [CompleteSpace B] in
lemma locally_analytic_plaque_zeroSet (P : AlignedProductChart S A B)
    {Z : Set X.Carrier} (hZ : LocallyHolomorphicZeroSet X Z) (b : B)
    (U : Set A) (hU : ∀a∈U,(a,b)∈P.chart.target) :
    AnalyticGermContinuation.LocallyAnalyticZeroSet
      {a | P.chart.symm (a,b)∈Z} U := by
  intro a ha
  obtain ⟨V,hVo,hx,f,hf,he⟩ := hZ (P.chart.symm (a,b))
  have hpair : ContinuousAt (fun t : A => (t,b)) a := continuousAt_id.prodMk continuousAt_const
  have hs : ContinuousAt (fun t : A => P.chart.symm (t,b)) a :=
    (P.inverse_holomorphicAt (hU a ha)).continuousAt.comp
      (f := fun t : A => (t,b)) (x := a) hpair
  have hn : ∀ᶠ t in 𝓝 a,(t,b)∈P.chart.target ∧ P.chart.symm (t,b)∈V :=
    Filter.Eventually.and
      (hpair.preimage_mem_nhds (P.chart.open_target.mem_nhds (hU a ha)))
      (hs.preimage_mem_nhds (hVo.mem_nhds hx))
  obtain ⟨r,hr,hrS⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r,hr,fun t => f (P.chart.symm (t,b)),?_,fun t ht => he _ (hrS ht).2⟩
  intro t ht
  have hf' := hf.contMDiffAt (hVo.mem_nhds (hrS ht).2)
  have hc : AnalyticAt ℂ (f ∘ P.chart.symm) (t,b) :=
    (hf'.comp (t,b) (P.inverse_holomorphicAt (hrS ht).1)).contDiffAt.analyticAt
  exact hc.comp (f := fun a : A => (a,b)) (x := t) (analyticAt_id.prod analyticAt_const)

end AlignedProductChart

namespace LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} (L : LeafJetAtlas S)

lemma germIn_of_related {Z : Set X.Carrier} (hZ : LocallyHolomorphicZeroSet X Z)
    {y z : X.Carrier} (hy : L.GermIn Z y) (hrel : L.plaques.Related y z) :
    L.GermIn Z z := by
  obtain ⟨i,b,U,hUc,hT,a₀,ha₀,a₁,ha₁,h₀,h₁⟩ := hrel
  let P := L.chart i
  have hyS : y∈P.chart.source := h₀ ▸ P.chart.map_target (hT a₀ ha₀)
  have hzS : z∈P.chart.source := h₁ ▸ P.chart.map_target (hT a₁ ha₁)
  have hyC : P.chart y=(a₀,b) := by rw [←h₀]; exact P.chart.right_inv (hT a₀ ha₀)
  have hzC : P.chart z=(a₁,b) := by rw [←h₁]; exact P.chart.right_inv (hT a₁ ha₁)
  have hyP := (L.germIn_iff P hyS).mp hy
  have hyG : {a | P.chart.symm (a,b)∈Z}∈𝓝 a₀ := by
    change ∀ᶠ a in 𝓝 a₀,P.chart.symm (a,b)∈Z
    simpa only [AlignedProductChart.GermIn,hyC] using hyP
  have hzG := AnalyticGermContinuation.propagate hUc
    (P.locally_analytic_plaque_zeroSet hZ b U hT) ha₀ ha₁ hyG
  apply (L.germIn_iff P hzS).mpr
  change ∀ᶠ a in 𝓝 a₁,P.chart.symm (a,b)∈Z at hzG
  simpa only [AlignedProductChart.GermIn,hzC] using hzG

lemma germIn_of_reachable {Z : Set X.Carrier} (hZ : LocallyHolomorphicZeroSet X Z)
    {y z : X.Carrier} (hy : L.GermIn Z y) (hrel : L.plaques.Reachable y z) :
    L.GermIn Z z := by
  induction hrel with
  | refl => exact hy
  | tail _ h ih => exact L.germIn_of_related hZ ih h

 

theorem closure_leaf_subset {Z : Set X.Carrier} (hZ : LocallyHolomorphicZeroSet X Z)
    (hclosed : IsClosed Z) {y : X.Carrier} (hy : L.GermIn Z y) :
    closure (L.leaf y) ⊆ Z := by
  apply closure_minimal _ hclosed
  intro z hz
  exact L.germIn_mem (L.germIn_of_reachable hZ hy hz)

end LeafJetAtlas
end SplitTangent

end

end OAI
