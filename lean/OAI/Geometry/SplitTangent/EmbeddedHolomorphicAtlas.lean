import Mathlib
import OAI.Geometry.SplitTangent.Basic

namespace OAI

/-! Embedded Holomorphic Atlas. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent

namespace ProjectiveEmbedding

 

def pullback {X Y : ComplexManifold.{u}} (e : ProjectiveEmbedding X)
    (i : Y.Carrier → X.Carrier)
    (hi : ContMDiff (ModelWithCorners Y) (ModelWithCorners X) ω i)
    (hinj : Function.Injective i)
    (himm : ∀ y, Function.Injective
      (mfderiv (ModelWithCorners Y) (ModelWithCorners X) i y)) :
    ProjectiveEmbedding Y where
  N := e.N
  map := e.map ∘ i
  injective := e.injective.comp hinj
  open_patch j := (e.open_patch j).preimage hi.continuous
  holomorphic j := (e.holomorphic j).comp hi.contMDiffOn (fun _ h => h)
  immersion y j hy := by
    change Function.Injective
      (mfderiv (ModelWithCorners Y) 𝓘(ℂ, Fin (e.N + 1) → ℂ)
        ((fun x => projectiveCoordinates j (e.map x)) ∘ i) y)
    rw [mfderiv_comp y
      (((e.holomorphic j).contMDiffAt ((e.open_patch j).mem_nhds hy)).mdifferentiableAt
        (by simp)) ((hi y).mdifferentiableAt (by simp))]
    exact (e.immersion (i y) j hy).comp (himm y)

end ProjectiveEmbedding

structure EmbeddedHolomorphicAtlas (X : ComplexManifold.{u}) (r : ℕ) (Z : Set X.Carrier) where
  chart : Z → OpenPartialHomeomorph Z (Fin r → ℂ)
  mem_source : ∀y,y∈(chart y).source
  forward : Z → X.Carrier → Fin r → ℂ
  inverse : Z → (Fin r → ℂ) → X.Carrier
  forward_eq : ∀y z,z∈(chart y).source → forward y z.val=chart y z
  inverse_eq : ∀y a,a∈(chart y).target → inverse y a=((chart y).symm a).val
  forward_holomorphic : ∀y z,z∈(chart y).source →
    ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,Fin r → ℂ) ω (forward y) z.val
  inverse_holomorphic : ∀y a,a∈(chart y).target →
    ContMDiffAt 𝓘(ℂ,Fin r → ℂ) (ModelWithCorners X) ω (inverse y) a

namespace EmbeddedHolomorphicAtlas
variable {X : ComplexManifold.{u}} {r : ℕ} {Z : Set X.Carrier}
  (L : EmbeddedHolomorphicAtlas X r Z)

lemma transition_holomorphic (y z : Z) {a : Fin r → ℂ}
    (ha : a∈((L.chart y).symm.trans (L.chart z)).source) :
    ContDiffAt ℂ ω ((L.chart z) ∘ (L.chart y).symm) a := by
  have h₁ := L.inverse_holomorphic y a ha.1
  have h₂ := L.forward_holomorphic z ((L.chart y).symm a) ha.2
  rw [←L.inverse_eq y a ha.1] at h₂
  have hh := (h₂.comp a h₁).contDiffAt
  apply hh.congr_of_eventuallyEq
  have hs := ((L.chart y).symm.trans (L.chart z)).open_source.mem_nhds ha
  filter_upwards [hs] with b hb
  change L.chart z ((L.chart y).symm b)=L.forward z (L.inverse y b)
  rw [L.inverse_eq y b hb.1]
  exact (L.forward_eq z ((L.chart y).symm b) hb.2).symm

@[instance_reducible] def chartedSpace : ChartedSpace (Fin r → ℂ) Z where
  atlas := range L.chart
  chartAt := L.chart
  mem_chart_source := L.mem_source
  chart_mem_atlas y := ⟨y,rfl⟩

lemma isManifold : letI := L.chartedSpace; IsManifold 𝓘(ℂ,Fin r → ℂ) ω Z := by
  let := L.chartedSpace
  apply isManifold_of_contDiffOn
  rintro c d ⟨y,rfl⟩ ⟨z,rfl⟩ a ha
  have ha' : a∈((L.chart y).symm.trans (L.chart z)).source := ha.1
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.comp_id,Function.id_comp,OpenPartialHomeomorph.coe_trans] using
    (L.transition_holomorphic y z ha').contDiffWithinAt

 
def manifold : ComplexManifold.{u} where
  dim := r
  Carrier := Z
  charts := L.chartedSpace
  holomorphicAtlas := L.isManifold

lemma inclusion_holomorphic : letI := L.chartedSpace;
    ContMDiff 𝓘(ℂ,Fin r → ℂ) (ModelWithCorners X) ω
       (Subtype.val : Z → X.Carrier) := by
  let := L.chartedSpace
  intro y
  rw [contMDiffAt_iff_source]
  have hh := L.inverse_holomorphic y (L.chart y y) ((L.chart y).map_source (L.mem_source y))
  have he : (Subtype.val ∘ (extChartAt 𝓘(ℂ,Fin r → ℂ) y).symm)
      =ᶠ[𝓝 (L.chart y y)] L.inverse y := by
    filter_upwards [(L.chart y).open_target.mem_nhds ((L.chart y).map_source (L.mem_source y))] with a ha
    exact (L.inverse_eq y a ha).symm
  have hg := hh.congr_of_eventuallyEq he
  have hp : extChartAt 𝓘(ℂ,Fin r → ℂ) y y=L.chart y y := rfl
  rw [hp]
  simpa only [modelWithCornersSelf_coe,Set.range_id,contMDiffWithinAt_univ] using hg

lemma inclusion_mfderiv_injective : letI := L.chartedSpace;
    ∀y : Z,Function.Injective
       (mfderiv 𝓘(ℂ,Fin r → ℂ) (ModelWithCorners X) (Subtype.val : Z → X.Carrier) y) := by
  let := L.chartedSpace
  let := L.isManifold
  intro y
  have hF := L.forward_holomorphic y y (L.mem_source y)
  have hI := L.inclusion_holomorphic y
  have he : (L.forward y ∘ (Subtype.val : Z → X.Carrier))
      =ᶠ[𝓝 y] (extChartAt 𝓘(ℂ,Fin r → ℂ) y) := by
    filter_upwards [(L.chart y).open_source.mem_nhds (L.mem_source y)] with z hz
    exact L.forward_eq y z hz
  have hd := mfderiv_comp y (hF.mdifferentiableAt (by simp)) (hI.mdifferentiableAt (by simp))
  rw [he.mfderiv_eq,mfderiv_extChartAt_self] at hd
  intro v w hvw
  have hh := congrArg (mfderiv (ModelWithCorners X) 𝓘(ℂ,Fin r → ℂ) (L.forward y) y.val) hvw
  change ((mfderiv (ModelWithCorners X) 𝓘(ℂ,Fin r → ℂ) (L.forward y) y.val).comp
    (mfderiv 𝓘(ℂ,Fin r → ℂ) (ModelWithCorners X) (Subtype.val : Z → X.Carrier) y)) v =
    ((mfderiv (ModelWithCorners X) 𝓘(ℂ,Fin r → ℂ) (L.forward y) y.val).comp
    (mfderiv 𝓘(ℂ,Fin r → ℂ) (ModelWithCorners X) (Subtype.val : Z → X.Carrier) y)) w at hh
  rw [←hd] at hh
  exact hh

 

def projectiveEmbedding (e : ProjectiveEmbedding X) : ProjectiveEmbedding L.manifold := by
  letI := L.chartedSpace
  exact e.pullback (Subtype.val : L.manifold.Carrier → X.Carrier)
    L.inclusion_holomorphic Subtype.val_injective L.inclusion_mfderiv_injective

lemma holomorphic_lift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → X.Carrier} (hf : ContMDiff 𝓘(ℂ,E) (ModelWithCorners X) ω f)
    (hZ : ∀x,f x∈Z) : letI := L.chartedSpace;
    ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,Fin r → ℂ) ω (fun x => (⟨f x,hZ x⟩ : Z)) := by
  let := L.chartedSpace
  let h : E → Z := fun x => ⟨f x,hZ x⟩
  have hc : Continuous h := hf.continuous.subtype_mk hZ
  intro x
  rw [contMDiffAt_iff_target]
  refine ⟨hc.continuousAt,?_⟩
  have hh := (L.forward_holomorphic (h x) (h x) (L.mem_source (h x))).comp x (hf x)
  apply hh.congr_of_eventuallyEq
  filter_upwards [hc.continuousAt.preimage_mem_nhds
    ((L.chart (h x)).open_source.mem_nhds (L.mem_source (h x)))] with y hy
  exact (L.forward_eq (h x) (h y) hy).symm

end EmbeddedHolomorphicAtlas
end SplitTangent

end

end OAI
