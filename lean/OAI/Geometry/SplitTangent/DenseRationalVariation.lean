import Mathlib
import OAI.Geometry.SplitTangent.RationalFamilies
import OAI.Geometry.SplitTangent.BracketIntegrability
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.OpenManifold
import OAI.Geometry.SplitTangent.RationalAccepted
import OAI.Geometry.SplitTangent.RationalEncoding
import OAI.Geometry.SplitTangent.RationalFamilyCover

namespace OAI

/-! Dense Rational Variation. -/

noncomputable section
open Set Filter Topology IsManifold
open scoped ContDiff Manifold
universe u
namespace SplitTangent
open AnalyticZeroCover RationalParameters

 

theorem RationallyConnected.countable_dense_family_cover {X : ComplexManifold.{u}}
    [CompactSpace X.Carrier] (e : ProjectiveEmbedding X) (hRC : RationallyConnected e)
    (x₀ : X.Carrier) :
    ∃C : (d : ℕ) → Set (Patch (Coeff e.N d)),
      (∀d,(C d).Countable) ∧
      (∀d, ∀P∈C d,P.image ⊆ regular e.N d ∩ accepted e d) ∧
      ∃U : Set (X.Carrier × X.Carrier), IsOpen U ∧ U.Nonempty ∧ Dense U ∧
        U ⊆ ⋃ d, ⋃P∈C d, pairEvaluation e x₀ P '' P.domain := by
  classical
  obtain ⟨U,hUz,hUn,hUd,hU⟩ := hRC
  have Hd (d : ℕ) := countable_accepted e (d := d)
  choose C hC hCP hCc using Hd
  refine ⟨C,hC,hCP,U,hUz.isOpen e,hUn,hUd,?_⟩
  intro xy hxy
  obtain ⟨g,hg0,hg1⟩ := RationallyConnected.fixed_endpoints hU hxy
  obtain ⟨d,τ,hτ,hτf,hτi⟩ := curve_encoding e g
  obtain ⟨P,hP,z,hz,hzτ⟩ := mem_iUnion₂.mp (hCc d hτ)
  refine mem_iUnion.mpr ⟨d,mem_iUnion₂.mpr ⟨P,hP,z,hz,?_⟩⟩
  apply Prod.ext
  · change e.coneLift x₀ (ev false (P.map z) 0)=xy.1
    rw [hzτ, e.coneLift_eq x₀ (regular_nonzero hτ.1 false 0) (hτf 0),hg0]
  · change e.coneLift x₀ (ev false (P.map z) 1)=xy.2
    rw [hzτ, e.coneLift_eq x₀ (regular_nonzero hτ.1 false 1) (hτf 1),hg1]

 

theorem RationallyConnected.exists_submersive_family_in_open {X : ComplexManifold.{u}}
    [CompactSpace X.Carrier] (e : ProjectiveEmbedding X) (hRC : RationallyConnected e)
    (hdim : 0<X.dim) (V₀ : Set (X.Carrier × X.Carrier))
    (hV₀ : IsOpen V₀) (hV₀n : V₀.Nonempty) :
    ∃T : ComplexManifold.{u}, Nonempty T.Carrier ∧
      ∃G : RationalFamily X T, (∀τ,G.twoPointEvaluation 0 1 τ∈V₀) ∧ ∀τ, Function.Surjective
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
  obtain ⟨C,hC,hCP,V,hV,hVn,hVd,hcov⟩ := hRC.countable_dense_family_cover e x₀
  let : ∀d, Countable (C d) := fun d => (hC d).to_subtype
  let A := Σd, C d
  let d (a : A) := a.2.val.dim
  let f (a : A) := pairEvaluation e x₀ a.2.val
  let U (a : A) : Set (Space (d a)) := a.2.val.domain ∩ (f a) ⁻¹' V₀
  have hU (a : A) : IsOpen (U a) := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    exact Filter.inter_mem (a.2.val.isOpen_domain.mem_nhds hx.1)
      ((pairEvaluation_holomorphicAt e x₀ a.2.val
        (hCP a.1 a.2.val a.2.property) hx.1).continuousAt.preimage_mem_nhds (hV₀.mem_nhds hx.2))
  have hf (a : A) (x) (hx : x∈U a) :
      ContMDiffAt 𝓘(ℂ,Space (d a)) 𝓘(ℂ,Model X × Model X) ω (f a) x := by
    rw [modelWithCornersSelf_prod]
    exact pairEvaluation_holomorphicAt e x₀ a.2.val (hCP a.1 a.2.val a.2.property) hx.1
  have hcover : V∩V₀ ⊆ ⋃a,f a '' U a := by
    intro v hv
    obtain ⟨n,hn⟩ := mem_iUnion.mp (hcov hv.1)
    obtain ⟨P,hP,x,hx,hfx⟩ := mem_iUnion₂.mp hn
    exact mem_iUnion.mpr ⟨⟨n,⟨P,hP⟩⟩,x,⟨hx,by
      change pairEvaluation e x₀ P x ∈ V₀
      rw [hfx]
      exact hv.2⟩,hfx⟩
  have hdim' : 0<Module.finrank ℂ (Model X × Model X) := by
    simp only [Module.finrank_prod,Model,Module.finrank_fin_fun]
    omega
  obtain ⟨y,a,x,hx,hfx,hs⟩ := exists_chart_submersion_of_cover d U f hU hf
    (hV.inter hV₀) (by simpa only [Set.inter_comm] using hVd.inter_open_nonempty V₀ hV₀ hV₀n) hcover hdim'
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
  let G := family e x₀ a.2.val (hCP a.1 a.2.val a.2.property) hW hWn (fun z hz => (hWP hz).1)
  refine ⟨T,OpenManifold.nonempty W hWn,G,?_,?_⟩
  · intro τ
    exact (hWP τ.down.property).2
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

end

end OAI
