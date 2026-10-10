import Mathlib
import OAI.Geometry.NilpotentCharts.QuotientCharts

namespace OAI

/-! Smooth simply connected quotients by central vector subspaces. -/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators commutatorElement
open Function Set Manifold Topology Filter

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]
local notation "I₀" => 𝓘(ℝ,E₀)
variable (K : Submodule ℝ E₀) (S : Subgroup G)
  (hS : ∀ g, g ∈ S ↔ ∃ z : K, subspaceAxes (G := G) K z = g)
  (hEmb : Topology.IsEmbedding (subspaceAxes (G := G) K))
open scoped Pointwise
include hS hEmb in
lemma exists_subspace_quotient_injective_neighbourhood (W : Submodule ℝ E₀) (hWK : IsCompl W K) :
    ∃ U : Set W, IsOpen U ∧ 0 ∈ U ∧
      InjOn ((QuotientGroup.mk : G → G ⧸ S) ∘ subspaceAxes W) U := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup I₀ ∞
  obtain ⟨e,h0,he⟩ := exists_productSlice_localChart (G := G) W K hWK
  obtain ⟨A,T,hA,hA0,hT,hT0,hAT⟩ := mem_nhds_prod_iff'.mp (e.open_source.mem_nhds h0)
  obtain ⟨N,hNo,hNT⟩ := hEmb.isInducing.isOpen_iff.mp hT
  have hN1 : (1 : G) ∈ N := by
    have hh : (0 : K) ∈ subspaceAxes K ⁻¹' N := by rw [hNT]; exact hT0
    simpa only [Set.mem_preimage,subspaceAxes_zero] using hh
  obtain ⟨B,hB,_,hBi,hBB⟩ := exists_closed_nhds_one_inv_eq_mul_subset (hNo.mem_nhds hN1)
  have hpre : subspaceAxes (G := G) W ⁻¹' B ∈ 𝓝 (0 : W) := by
    have hc := (subspaceAxes_contMDiff (G := G) W).continuous.tendsto 0
    apply hc
    simpa only [subspaceAxes_zero] using hB
  obtain ⟨U,hUsub,hU,hU0⟩ := mem_nhds_iff.mp (Filter.inter_mem (hA.mem_nhds hA0) hpre)
  refine ⟨U,hU,hU0,?_⟩
  intro w hw w' hw' hq
  let g := (subspaceAxes (G := G) W w)⁻¹ * subspaceAxes W w'
  have hgS : g ∈ S := QuotientGroup.eq.mp hq
  obtain ⟨z,hz⟩ := (hS g).mp hgS
  have hgN : g ∈ N := by
    apply hBB
    apply Set.mul_mem_mul (a := (subspaceAxes (G := G) W w)⁻¹)
      (b := subspaceAxes W w') (s := B) (t := B) ?_ (hUsub hw').2
    rw [← hBi]
    apply Set.mem_inv.mpr
    rw [inv_inv]
    exact (hUsub hw).2
  have hzT : z ∈ T := by
    rw [← hNT]
    change subspaceAxes K z ∈ N
    rw [hz]
    exact hgN
  have hwsource : (w,z) ∈ e.source := hAT ⟨(hUsub hw).1,hzT⟩
  have hw'source : (w',(0 : K)) ∈ e.source := hAT ⟨(hUsub hw').1,hT0⟩
  have heq : e (w,z) = e (w',(0 : K)) := by
    rw [he hwsource,he hw'source]
    simp only [productSlice,subspaceAxes_zero,mul_one,hz,g,mul_inv_cancel_left]
  exact congrArg Prod.fst (e.injOn hwsource hw'source heq)

include hS in
lemma subspace_quotient_productSlice (W : Submodule ℝ E₀) (p : W × K) :
    QuotientGroup.mk (productSlice (G := G) W K p) =
      (QuotientGroup.mk (subspaceAxes W p.1) : G ⧸ S) := by
  symm
  apply QuotientGroup.eq.mpr
  change (subspaceAxes W p.1)⁻¹ * (subspaceAxes W p.1 * subspaceAxes K p.2) ∈ S
  rw [inv_mul_cancel_left]
  exact (hS _).mpr ⟨p.2,rfl⟩
end RawLieIntegration
namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]
local notation "I₀" => 𝓘(ℝ,E₀)
variable (K : Submodule ℝ E₀) (S : Subgroup G)
  (hS : ∀ g, g ∈ S ↔ ∃ z : K, subspaceAxes (G := G) K z = g)
  (hEmb : Topology.IsEmbedding (subspaceAxes (G := G) K))
open scoped Pointwise
include hS hEmb
 

theorem exists_subspace_quotient_openChart (W : Submodule ℝ E₀) (hWC : IsCompl W K) :
    ∃ q : OpenPartialHomeomorph W (G ⧸ S), 0 ∈ q.source ∧
      (q : W → G ⧸ S) = (QuotientGroup.mk : G → G ⧸ S) ∘ subspaceAxes W := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup I₀ ∞
  let f : W → G ⧸ S := (QuotientGroup.mk : G → G ⧸ S) ∘ subspaceAxes W
  have hf : Continuous f := QuotientGroup.continuous_mk.comp (subspaceAxes_contMDiff W).continuous
  obtain ⟨e,h0,he⟩ := exists_productSlice_localChart (G := G) W K hWC
  obtain ⟨A,T,hA,hA0,hT,hT0,hAT⟩ := mem_nhds_prod_iff'.mp (e.open_source.mem_nhds h0)
  obtain ⟨V,hV,hV0,hinj⟩ := exists_subspace_quotient_injective_neighbourhood K S hS hEmb W hWC
  let U := A ∩ V
  have hU : IsOpen U := hA.inter hV
  have hU0 : (0 : W) ∈ U := ⟨hA0,hV0⟩
  have hUinj : InjOn f U := hinj.mono inter_subset_right
  have hopen : ∀ B : Set W, IsOpen B → B ⊆ U → IsOpen (f '' B) := by
    intro B hB hBU
    have hBT : B ×ˢ T ⊆ e.source := fun p hp => hAT ⟨(hBU hp.1).1,hp.2⟩
    have hh := QuotientGroup.isOpenMap_coe (N := S) _
      (e.isOpen_image_of_subset_source (hB.prod hT) hBT)
    have heq : (QuotientGroup.mk : G → G ⧸ S) '' (e '' (B ×ˢ T)) = f '' B := by
      ext x
      constructor
      · rintro ⟨g,⟨p,hp,rfl⟩,rfl⟩
        refine ⟨p.1,hp.1,?_⟩
        rw [he (hBT hp), subspace_quotient_productSlice K S hS]
        rfl
      · rintro ⟨w,hw,rfl⟩
        refine ⟨e (w,0), ⟨(w,0), ⟨hw,hT0⟩, rfl⟩, ?_⟩
        rw [he (hBT ⟨hw,hT0⟩), subspace_quotient_productSlice K S hS]
        rfl
    exact heq ▸ hh
  let q₀ := hUinj.toPartialEquiv f U
  have hqopen : IsOpenMap (q₀.source.domRestrict q₀) := by
    intro B hB
    have hBopen : IsOpen ((Subtype.val : U → W) '' B) :=
      hU.isOpenEmbedding_subtypeVal.isOpenMap _ hB
    have hBsub : (Subtype.val : U → W) '' B ⊆ U := by
      rintro w ⟨a,ha,rfl⟩
      exact a.property
    have hh := hopen _ hBopen hBsub
    change IsOpen ((fun w : U => f w) '' B)
    erw [Set.image_image] at hh
    exact hh
  refine ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict q₀ hf.continuousOn hqopen hU,hU0,rfl⟩

end RawLieIntegration
namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]
local notation "I₀" => 𝓘(ℝ,E₀)
variable (K : Submodule ℝ E₀) (S : Subgroup G)
  (hS : ∀ g, g ∈ S ↔ ∃ z : K, subspaceAxes (G := G) K z = g)
  (hEmb : Topology.IsEmbedding (subspaceAxes (G := G) K))
open scoped Pointwise
include hS hEmb
omit hEmb in
lemma subspace_quotient_coordinates_smooth (W : Submodule ℝ E₀)
    (e : PartialDiffeomorph 𝓘(ℝ, W × K) I₀ (W × K) G ∞)
    (he : EqOn e (productSlice W K) e.source)
    (q : OpenPartialHomeomorph W (G ⧸ S))
    (hq : (q : W → G ⧸ S) = (QuotientGroup.mk : G → G ⧸ S) ∘ subspaceAxes W)
    (hqe : ∀ w ∈ q.source, (w, (0 : K)) ∈ e.source) :
    ContMDiffOn I₀ 𝓘(ℝ,W) ∞ (q.symm ∘ QuotientGroup.mk)
      ((QuotientGroup.mk : G → G ⧸ S) ⁻¹' q.target) := by
  intro g hg
  let u := q.symm (QuotientGroup.mk g)
  have hu : u ∈ q.source := q.map_target hg
  have hqu : q u = QuotientGroup.mk g := q.right_inv hg
  let z := (subspaceAxes (G := G) W u)⁻¹ * g
  have hz : z ∈ S := QuotientGroup.eq.mp (by simpa only [hq, Function.comp_apply] using hqu)
  let R : G → G := fun x => x * z⁻¹
  have hR : ContMDiff I₀ I₀ ∞ R := contMDiff_id.mul contMDiff_const
  have hRg : R g = subspaceAxes W u := by simp [R,z]
  have hezero : e (u,0) = subspaceAxes W u := by
    rw [he (hqe _ hu)]
    simp only [productSlice, subspaceAxes_zero, mul_one]
  have hRt : R g ∈ e.target := by rw [hRg, ← hezero]; exact e.map_source (hqe _ hu)
  have hsymm : e.symm (R g) = (u, 0) := by
    rw [hRg, ← hezero]
    exact e.toPartialEquiv.left_inv (hqe _ hu)
  let A : Set G := e.target ∩ e.symm ⁻¹' (q.source ×ˢ (Set.univ : Set K))
  have hA : A ∈ 𝓝 (R g) := by
    refine Filter.inter_mem (e.open_target.mem_nhds hRt) ?_
    apply e.toOpenPartialHomeomorph.continuousAt_symm hRt
    change q.source ×ˢ (Set.univ : Set K) ∈ 𝓝 (e.symm (R g))
    rw [hsymm]
    exact (q.open_source.prod isOpen_univ).mem_nhds ⟨hu,mem_univ _⟩
  have hnear : R ⁻¹' A ∈ 𝓝 g := hR.continuous.tendsto g hA
  have hequiv : (q.symm ∘ QuotientGroup.mk) =ᶠ[𝓝 g] (fun x => (e.symm (R x)).1) := by
    filter_upwards [hnear] with x hx
    have hp := e.map_target hx.1
    have hprod : productSlice W K (e.symm (R x)) = R x :=
      (he hp).symm.trans (e.right_inv hx.1)
    have hqprod : q (e.symm (R x)).1 = QuotientGroup.mk (R x) := by
      rw [hq]
      exact (subspace_quotient_productSlice K S hS W (e.symm (R x))).symm.trans (congrArg QuotientGroup.mk hprod)
    have hqx : (QuotientGroup.mk (R x) : G ⧸ S) = QuotientGroup.mk x := by
      symm
      apply QuotientGroup.eq.mpr
      change x⁻¹ * (x * z⁻¹) ∈ S
      rw [inv_mul_cancel_left]
      exact (S).inv_mem hz
    change q.symm (QuotientGroup.mk x) = (e.symm (R x)).1
    rw [← hqx, ← hqprod]
    exact q.left_inv hx.2.1
  have hinv : ContMDiffAt I₀ 𝓘(ℝ,W × K) ∞ e.symm (R g) :=
    e.contMDiffOn_invFun.contMDiffAt (e.open_target.mem_nhds hRt)
  have hF : ContMDiffAt I₀ 𝓘(ℝ,W) ∞ (fun x => (e.symm (R x)).1) g :=
    (ContinuousLinearMap.fst ℝ W K).contDiff.contMDiff.contMDiffAt.comp g
      (hinv.comp g (hR g))
  exact (hF.congr_of_eventuallyEq hequiv).contMDiffWithinAt

 

theorem exists_subspace_quotient_smoothChart (W : Submodule ℝ E₀) (hWC : IsCompl W K) :
    ∃ q : OpenPartialHomeomorph W (G ⧸ S), 0 ∈ q.source ∧
      (q : W → G ⧸ S) = (QuotientGroup.mk : G → G ⧸ S) ∘ subspaceAxes W ∧
      ContMDiffOn I₀ 𝓘(ℝ,W) ∞ (q.symm ∘ QuotientGroup.mk)
        ((QuotientGroup.mk : G → G ⧸ S) ⁻¹' q.target) := by
  obtain ⟨e,h0,he⟩ := exists_productSlice_partialDiffeomorph (G := G) W K hWC
  obtain ⟨q₀,hq₀0,hq₀⟩ := exists_subspace_quotient_openChart K S hS hEmb W hWC
  let U : Set W := (fun w => (w, (0 : K))) ⁻¹' e.source
  have hU : IsOpen U := e.open_source.preimage (continuous_id.prodMk continuous_const)
  let q := q₀.restr U
  have hqs : q.source = q₀.source ∩ U := q₀.restr_source' U hU
  have hq0 : (0 : W) ∈ q.source := by rw [hqs]; exact ⟨hq₀0,h0⟩
  have hq : (q : W → G ⧸ S) = (QuotientGroup.mk : G → G ⧸ S) ∘ subspaceAxes W := hq₀
  refine ⟨q,hq0,hq,subspace_quotient_coordinates_smooth K S hS W e he q hq ?_⟩
  intro w hw
  exact ((hqs ▸ hw).2)

end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]
variable (K : Submodule ℝ E₀) (S : Subgroup G) [S.Normal]
  (hS : ∀ g, g ∈ S ↔ ∃ z : K, subspaceAxes (G := G) K z = g)
  (hEmb : Topology.IsEmbedding (subspaceAxes (G := G) K))
include hS hEmb

 

theorem exists_subspace_quotient_submersion (W : Submodule ℝ E₀) (hWC : IsCompl W K) :
    ∃ cs : ChartedSpace W (G ⧸ S),
      letI := cs
      LieGroup 𝓘(ℝ,W) ∞ (G ⧸ S) ∧
      ContMDiff 𝓘(ℝ,E₀) 𝓘(ℝ,W) ∞ (QuotientGroup.mk' S) ∧
      Surjective (mfderiv 𝓘(ℝ,E₀) 𝓘(ℝ,W) (QuotientGroup.mk' S) 1 : E₀ →L[ℝ] W) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E₀) ∞
  obtain ⟨q,hq0,hq,hcoord⟩ := exists_subspace_quotient_smoothChart K S hS hEmb W hWC
  have hqzero : q 0 = (1 : G ⧸ S) := by
    simp only [hq,Function.comp_apply,subspaceAxes_zero,QuotientGroup.mk_one]
  have h1 : (1 : G ⧸ S) ∈ q.target := hqzero ▸ q.map_source hq0
  let cs := RawQuotientLie.quotientChartedSpace q h1
  refine ⟨cs,?_,?_,?_⟩
  · exact RawQuotientLie.quotient_lieGroup (QuotientGroup.mk' S) (QuotientGroup.mk'_surjective S)
      QuotientGroup.continuous_mk (subspaceAxes W) (subspaceAxes_contMDiff W) q h1 hq hcoord
  · exact RawQuotientLie.quotient_projection_smooth q h1 (QuotientGroup.mk' S)
      QuotientGroup.continuous_mk hcoord
  · exact RawQuotientLie.quotient_derivative_surjective (QuotientGroup.mk' S)
      (QuotientGroup.mk'_surjective S) QuotientGroup.continuous_mk
      (subspaceAxes W) (subspaceAxes_contMDiff W) (subspaceAxes_zero W) q hq0 h1 hq hcoord

omit [S.Normal] hEmb in
lemma subspace_range_pathConnectedSpace : PathConnectedSpace S := by
  let f : K → S := fun v => ⟨subspaceAxes K v,(hS _).mpr ⟨v,rfl⟩⟩
  have hf : Continuous f := (subspaceAxes_contMDiff (G := G) K).continuous.subtype_mk _
  have hon : Surjective f := by
    rintro ⟨g,hg⟩
    obtain ⟨v,hv⟩ := (hS g).mp hg
    exact ⟨v,Subtype.ext hv⟩
  exact hon.pathConnectedSpace hf

lemma subspace_quotient_simplyConnected [SimplyConnectedSpace G] : SimplyConnectedSpace (G ⧸ S) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E₀) ∞
  let : PathConnectedSpace S := subspace_range_pathConnectedSpace K S hS
  let : PathConnectedSpace (QuotientGroup.mk' S).ker := by rw [QuotientGroup.ker_mk']; infer_instance
  obtain ⟨W,hKW⟩ := Submodule.exists_isCompl K
  obtain ⟨q,hq0,hq,_⟩ := exists_subspace_quotient_smoothChart K S hS hEmb W hKW.symm
  have hqzero : q 0 = (1 : G ⧸ S) := by simp only [hq,Function.comp_apply,subspaceAxes_zero,QuotientGroup.mk_one]
  have h1 : (1 : G ⧸ S) ∈ q.target := hqzero ▸ q.map_source hq0
  apply RawQuotientTopology.simplyConnected_quotient (QuotientGroup.mk' S)
    (QuotientGroup.mk'_surjective S) QuotientGroup.continuous_mk
  exact RawQuotientTopology.local_sections_of_chart (QuotientGroup.mk' S)
    (QuotientGroup.mk'_surjective S) (subspaceAxes W) (subspaceAxes_contMDiff W).continuous q h1 hq
end RawLieIntegration
end

end OAI
