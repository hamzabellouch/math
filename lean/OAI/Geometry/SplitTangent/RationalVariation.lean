import Mathlib
import OAI.Geometry.SplitTangent.RationalFamilies
import OAI.Geometry.SplitTangent.RationalFamilyCover
import OAI.Geometry.SplitTangent.BracketIntegrability
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.OpenManifold

namespace OAI

/-! Rational Variation. -/

noncomputable section
open Set Filter Topology IsManifold
open scoped ContDiff Manifold
universe u
namespace SplitTangent
open AnalyticZeroCover RationalParameters

 

theorem RationallyConnected.exists_submersive_familyAlternative {X : ComplexManifold.{u}}
    [CompactSpace X.Carrier] (e : ProjectiveEmbedding X) (hRC : RationallyConnected e)
    (hdim : 0<X.dim) :
    ∃T : ComplexManifold.{u}, Nonempty T.Carrier ∧
      ∃G : RationalFamily X T, ∀τ, Function.Surjective
        (mfderiv (ModelWithCorners T) ((ModelWithCorners X).prod (ModelWithCorners X))
          (G.twoPointEvaluation 0 1) τ) := by
  classical
  let : ChartedSpace (Model X × Model X) (X.Carrier × X.Carrier) :=
    prodChartedSpace (Model X) X.Carrier (Model X) X.Carrier
  let : IsManifold 𝓘(ℂ,Model X × Model X) ω (X.Carrier × X.Carrier) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod X.Carrier X.Carrier
  obtain ⟨xy,hxy⟩ := hRC.choose_spec.2.1
  let x₀ := xy.1
  obtain ⟨C,hC,hCP,V,hV,hVn,hcov⟩ := hRC.countable_family_cover e x₀
  let : ∀d, Countable (C d) := fun d => (hC d).to_subtype
  let A := Σd, C d
  let d (a : A) := a.2.val.dim
  let U (a : A) : Set (Space (d a)) := a.2.val.domain
  let f (a : A) := pairEvaluation e x₀ a.2.val
  have hU (a : A) : IsOpen (U a) := a.2.val.isOpen_domain
  have hf (a : A) (x) (hx : x∈U a) :
      ContMDiffAt 𝓘(ℂ,Space (d a)) 𝓘(ℂ,Model X × Model X) ω (f a) x := by
    rw [modelWithCornersSelf_prod]
    exact pairEvaluation_holomorphicAt e x₀ a.2.val (hCP a.1 a.2.val a.2.property) hx
  have hcover : V ⊆ ⋃a,f a '' U a := by
    intro v hv
    obtain ⟨n,hn⟩ := mem_iUnion.mp (hcov hv)
    obtain ⟨P,hP,x,hx,hfx⟩ := mem_iUnion₂.mp hn
    exact mem_iUnion.mpr ⟨⟨n,⟨P,hP⟩⟩,x,hx,hfx⟩
  have hdim' : 0<Module.finrank ℂ (Model X × Model X) := by
    simp only [Module.finrank_prod,Model,Module.finrank_fin_fun]
    omega
  obtain ⟨y,a,x,hx,hfx,hs⟩ := exists_chart_submersion_of_cover d U f hU hf
    hV hVn hcover hdim'
  let c := chartAt (Model X × Model X) y
  have hc : c ∈ maximalAtlas 𝓘(ℂ,Model X × Model X) ω _ :=
    IsManifold.chart_mem_maximalAtlas y
  have hcoord : AnalyticAt ℂ (c ∘ f a) x :=
    ((contMDiffAt_of_mem_maximalAtlas hc hfx).comp x (hf a x hx)).contDiffAt.analyticAt
  have hn : ∀ᶠz in 𝓝 x, z∈U a ∧ f a z∈c.source ∧
      Function.Surjective (fderiv ℂ (c ∘ f a) z) :=
    Filter.Eventually.and ((hU a).mem_nhds hx) (Filter.Eventually.and
      ((hf a x hx).continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hfx))
      (eventually_surjective_fderiv hcoord hs))
  obtain ⟨W,hWsub,hW,hxW⟩ := mem_nhds_iff.mp hn
  have hWn : W.Nonempty := ⟨x,hxW⟩
  have hWP : W⊆U a := fun z hz => (hWsub hz).1
  let T := OpenManifold.manifold.{u} W hW hWn
  let G := family e x₀ a.2.val (hCP a.1 a.2.val a.2.property) hW hWn hWP
  refine ⟨T,OpenManifold.nonempty W hWn,G,?_⟩
  intro τ
  let z := OpenManifold.val W τ
  have hz : z∈W := τ.down.property
  have hzf : ContMDiffAt 𝓘(ℂ,Space (d a)) 𝓘(ℂ,Model X × Model X) ω (f a) z :=
    hf a z (hWP hz)
  have hsurj : Function.Surjective
      (mfderiv 𝓘(ℂ,Space (d a)) 𝓘(ℂ,Model X × Model X) (f a) z) :=
    surjective_mfderiv_of_chart hzf y (hWsub hz).2.1 (hWsub hz).2.2
  have hv := (OpenManifold.val_mfderiv_bijective W hW hWn τ).2
  have hchain := mfderiv_comp τ (hzf.mdifferentiableAt (by decide))
    ((OpenManifold.val_holomorphic W hW hWn τ).mdifferentiableAt (by decide))
  rw [← modelWithCornersSelf_prod]
  change Function.Surjective (mfderiv (ModelWithCorners (OpenManifold.manifold.{u} W hW hWn))
    𝓘(ℂ,Model X × Model X)
    ((f a) ∘ (fun τ : (OpenManifold.manifold.{u} W hW hWn).Carrier => OpenManifold.val W τ)) τ)
  rw [hchain]
  exact hsurj.comp hv

 

theorem TangentSplitting.integrable_of_rationallyConnected {X : ComplexManifold.{u}}
    [CompactSpace X.Carrier] [ConnectedSpace X.Carrier] (e : ProjectiveEmbedding X)
    (hRC : RationallyConnected e) (hdim : 2≤X.dim) (S : TangentSplitting X) :
    Integrable X S.first ∧ Integrable X S.second := by
  obtain ⟨T,hT,G,hs⟩ := hRC.exists_submersive_familyAlternative e (by omega)
  let := hT
  exact G.integrable_both_of_submersive e S hs

end SplitTangent

namespace SplitTangent
open AnalyticZeroCover RationalParameters

 

theorem RationallyConnected.exists_submersive_family {X : ComplexManifold.{u}}
    [CompactSpace X.Carrier] (e : ProjectiveEmbedding X) (hRC : RationallyConnected e)
    (hdim : 0<X.dim) :
    ∃T : ComplexManifold.{u}, Nonempty T.Carrier ∧
      ∃G : RationalFamily X T, ∀τ, Function.Surjective
        (mfderiv (ModelWithCorners T) ((ModelWithCorners X).prod (ModelWithCorners X))
          (G.twoPointEvaluation 0 1) τ) := by
  classical
  let : ChartedSpace (Model X × Model X) (X.Carrier × X.Carrier) :=
    prodChartedSpace (Model X) X.Carrier (Model X) X.Carrier
  let : IsManifold 𝓘(ℂ,Model X × Model X) ω (X.Carrier × X.Carrier) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod X.Carrier X.Carrier
  obtain ⟨xy,hxy⟩ := hRC.choose_spec.2.1
  let x₀ := xy.1
  obtain ⟨C,hC,hCP,V,hV,hVn,hcov⟩ := hRC.countable_family_cover e x₀
  let : ∀d, Countable (C d) := fun d => (hC d).to_subtype
  let A := Σd, C d
  let d (a : A) := a.2.val.dim
  let U (a : A) : Set (Space (d a)) := a.2.val.domain
  let f (a : A) := pairEvaluation e x₀ a.2.val
  have hU (a : A) : IsOpen (U a) := a.2.val.isOpen_domain
  have hf (a : A) (x) (hx : x∈U a) :
      ContMDiffAt 𝓘(ℂ,Space (d a)) 𝓘(ℂ,Model X × Model X) ω (f a) x := by
    rw [modelWithCornersSelf_prod]
    exact pairEvaluation_holomorphicAt e x₀ a.2.val (hCP a.1 a.2.val a.2.property) hx
  have hcover : V ⊆ ⋃a,f a '' U a := by
    intro v hv
    obtain ⟨n,hn⟩ := mem_iUnion.mp (hcov hv)
    obtain ⟨P,hP,x,hx,hfx⟩ := mem_iUnion₂.mp hn
    exact mem_iUnion.mpr ⟨⟨n,⟨P,hP⟩⟩,x,hx,hfx⟩
  have hdim' : 0<Module.finrank ℂ (Model X × Model X) := by
    simp only [Module.finrank_prod,Model,Module.finrank_fin_fun]
    omega
  obtain ⟨y,a,x,hx,hfx,hs⟩ := exists_chart_submersion_of_cover d U f hU hf
    hV hVn hcover hdim'
  let c := chartAt (Model X × Model X) y
  have hc : c ∈ maximalAtlas 𝓘(ℂ,Model X × Model X) ω _ :=
    IsManifold.chart_mem_maximalAtlas y
  have hcoord : AnalyticAt ℂ (c ∘ f a) x :=
    ((contMDiffAt_of_mem_maximalAtlas hc hfx).comp x (hf a x hx)).contDiffAt.analyticAt
  have hn : ∀ᶠz in 𝓝 x, z∈U a ∧ f a z∈c.source ∧
      Function.Surjective (fderiv ℂ (c ∘ f a) z) :=
    Filter.Eventually.and ((hU a).mem_nhds hx) (Filter.Eventually.and
      ((hf a x hx).continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hfx))
      (eventually_surjective_fderiv hcoord hs))
  obtain ⟨W,hWsub,hW,hxW⟩ := _root_.mem_nhds_iff.mp hn
  have hWn : W.Nonempty := ⟨x,hxW⟩
  have hWP : W⊆U a := fun z hz => (hWsub hz).1
  let T := OpenManifold.manifold.{u} W hW hWn
  let G := family e x₀ a.2.val (hCP a.1 a.2.val a.2.property) hW hWn hWP
  refine ⟨T,OpenManifold.nonempty W hWn,G,?_⟩
  intro τ
  let z := OpenManifold.val W τ
  have hz : z∈W := τ.down.property
  have hzf : ContMDiffAt 𝓘(ℂ,Space (d a)) 𝓘(ℂ,Model X × Model X) ω (f a) z :=
    hf a z (hWP hz)
  have hsurj : Function.Surjective
      (mfderiv 𝓘(ℂ,Space (d a)) 𝓘(ℂ,Model X × Model X) (f a) z) :=
    surjective_mfderiv_of_chart hzf y (hWsub hz).2.1 (hWsub hz).2.2
  have hv := (OpenManifold.val_mfderiv_bijective W hW hWn τ).2
  have hchain := mfderiv_comp τ (hzf.mdifferentiableAt (by decide))
    ((OpenManifold.val_holomorphic W hW hWn τ).mdifferentiableAt (by decide))
  rw [← modelWithCornersSelf_prod]
  change Function.Surjective (mfderiv (ModelWithCorners (OpenManifold.manifold.{u} W hW hWn))
    𝓘(ℂ,Model X × Model X)
    ((f a) ∘ (fun τ : (OpenManifold.manifold.{u} W hW hWn).Carrier => OpenManifold.val W τ)) τ)
  rw [hchain]
  exact hsurj.comp hv

end SplitTangent

namespace SplitTangent
 

def IntegrabilityStatement : Prop :=
  ∀ (X : ComplexManifold.{u}), ConnectedSpace X.Carrier → CompactSpace X.Carrier →
    2 ≤ X.dim → ∀ e : ProjectiveEmbedding X, RationallyConnected e →
    ∀ S : TangentSplitting X, Integrable X S.first ∧ Integrable X S.second

theorem integrability_main : IntegrabilityStatement.{u} := by
  intro X hconn hcompact hdim e hRC S
  let := hconn
  let := hcompact
  exact S.integrable_of_rationallyConnected e hRC hdim
end SplitTangent

end

end OAI
