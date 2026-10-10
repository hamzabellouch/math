import Mathlib
import OAI.Geometry.CubicTorus.Reflection.SiblingReflectNormal

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coverAEAgreement_common_model {A B S : Set Cover} {x : Cover}
    (hA : x∈coverAEAgreement A S ∨ x∈coverAEAgreement A Sᶜ)
    (hB : x∈coverAEAgreement B S ∨ x∈coverAEAgreement B Sᶜ) :
    x∈coverAEAgreement A B ∨ x∈coverAEAgreement A Bᶜ := by
  rcases hA with ha|ha <;> rcases hB with hb|hb
  · exact Or.inl (coverAEAgreement_trans ha (coverAEAgreement_symm hb))
  · right
    have hh := coverAEAgreement_compl (coverAEAgreement_symm hb)
    rw [compl_compl] at hh
    exact coverAEAgreement_trans ha hh
  · exact Or.inr (coverAEAgreement_trans ha (coverAEAgreement_compl (coverAEAgreement_symm hb)))
  · exact Or.inl (coverAEAgreement_trans ha (coverAEAgreement_symm hb))

lemma off_essential_boundary_phase {A : Set Cover} {x : Cover}
    (h : x∉coverEssentialBoundary A) :
    x∈coverAEAgreement A ∅ ∨ x∈coverAEAgreement A (∅ : Set Cover)ᶜ := by
  rw [coverEssentialBoundary_eq_support] at h
  have h' := not_and_or.mp h
  have he1 : {y : Cover | ¬(y∈A ↔ y∈(∅ : Set Cover))}=A := by ext y; simp
  have he2 : {y : Cover | ¬(y∈A ↔ y∈(∅ : Set Cover)ᶜ)}=Aᶜ := by ext y; simp
  change x∉(volume.restrict {y | ¬(y∈A ↔ y∈(∅ : Set Cover))}).support ∨
    x∉(volume.restrict {y | ¬(y∈A ↔ y∈(∅ : Set Cover)ᶜ)}).support
  rw [he1,he2]
  exact h'

lemma graph_boundary_local_phase {A : Set Cover} (hA : MeasurableSet A)
    {a n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ} (hg : Continuous g)
    (ha : a∈coverEssentialBoundary A)
    (hbd : ∀ᶠ x in 𝓝 a,x∈coverEssentialBoundary A →
      normalGraph n g (normalPlaneCoordinates n (x-a))=x-a) :
    a∈coverAEAgreement A {x | 0<graphSignedHeight a n g x} ∨
    a∈coverAEAgreement A {x | 0<graphSignedHeight a n g x}ᶜ := by
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hbd
  obtain ⟨W,hW,haW,_,hphase⟩ := cover_graph_boundary_phases hA a hn hg
    (Metric.ball_mem_nhds a hr) ha (fun x hx ↦ hsub hx)
  rcases hphase with hp|hp
  · exact Or.inl (mem_coverAEAgreement_iff.mpr ⟨W,hW,haW,hp⟩)
  · right
    apply mem_coverAEAgreement_iff.mpr
    refine ⟨W,hW,haW,?_⟩
    have hz : ∀ᵐ x ∂volume,graphSignedHeight a n g x≠0 := by
      apply ae_iff.mpr
      simpa only [not_ne_iff,graphSignedHeight,sub_eq_zero] using graph_trace_volume_zero a hn hg
    filter_upwards [hp,hz] with x hx hz hxW
    change x∈A ↔ ¬0<graphSignedHeight a n g x
    rw [hx hxW]
    exact ⟨fun h h' ↦ (lt_asymm h h'),fun h ↦ lt_of_le_of_ne (le_of_not_gt h) hz⟩

theorem graph_boundary_phase_identity {A B : Set Cover} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (he : coverEssentialBoundary A=coverEssentialBoundary B)
    (hgraphs : ∀ a∈coverEssentialBoundary A,∃ (n : Cover) (g : Plane → ℝ),
      ‖n‖=1 ∧ Continuous g ∧ ∀ᶠ x in 𝓝 a,x∈coverEssentialBoundary A →
        normalGraph n g (normalPlaneCoordinates n (x-a))=x-a) :
    A=ᵐ[volume]B ∨ A=ᵐ[volume]Bᶜ := by
  apply cover_local_phase_global hA hB
  intro a
  by_cases ha : a∈coverEssentialBoundary A
  · obtain ⟨n,g,hn,hg,hga⟩ := hgraphs a ha
    have hab : a∈coverEssentialBoundary B := he ▸ ha
    have hgb : ∀ᶠ x in 𝓝 a,x∈coverEssentialBoundary B →
        normalGraph n g (normalPlaneCoordinates n (x-a))=x-a := by rwa [←he]
    exact coverAEAgreement_common_model (graph_boundary_local_phase hA hn hg ha hga)
      (graph_boundary_local_phase hB hn hg hab hgb)
  · have hb : a∉coverEssentialBoundary B := he ▸ ha
    exact coverAEAgreement_common_model (off_essential_boundary_phase ha)
      (off_essential_boundary_phase hb)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_same_boundary_phase {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (he : frontier (openRepresentative E)=frontier (openRepresentative F)) :
    E=ᵐ[torusVolume]F ∨ E=ᵐ[torusVolume]Fᶜ := by
  obtain ⟨μ,H,N,hμ,hN,hp,hae,hbd,_⟩ := Periodic.isMinimizerAt_tubular_normal_stability hV hE hmE
  have hch := isMinimizerAt_hasNormalizedCMCCharts hV hE hmE hμ hN hp hae hbd
  have hbe : coverEssentialBoundary (quotientMap ⁻¹' E)=coverEssentialBoundary (quotientMap ⁻¹' F) := by
    ext x
    rw [isMinimizerAt_lifted_boundary_global hV hE hmE,
      isMinimizerAt_lifted_boundary_global hW hF hmF,he]
  have hgraphs : ∀ a∈coverEssentialBoundary (quotientMap ⁻¹' E),∃ (n : Cover) (g : Plane → ℝ),
      ‖n‖=1 ∧ Continuous g ∧ ∀ᶠ x in 𝓝 a,x∈coverEssentialBoundary (quotientMap ⁻¹' E) →
        normalGraph n g (normalPlaneCoordinates n (x-a))=x-a := by
    intro a ha
    have hab := (isMinimizerAt_lifted_boundary_global hV hE hmE a).mp ha
    obtain ⟨hn,g,hg,_,_,_,hcov⟩ := hch a hab
    refine ⟨N a,g,hn,hg.continuous,?_⟩
    have ht : Tendsto (fun x : Cover ↦ x-a) (𝓝 a) (𝓝 (0 : Cover)) := by
      have hc : Continuous (fun x : Cover ↦ x-a) := continuous_id.sub continuous_const
      simpa only [sub_self] using hc.tendsto a
    filter_upwards [ht.eventually hcov] with x hx hxb
    have hxb' := (isMinimizerAt_lifted_boundary_global hV hE hmE x).mp hxb
    simpa only [add_sub_cancel] using hx.mp (by simpa only [add_sub_cancel] using hxb')
  rcases graph_boundary_phase_identity (hE.preimage measurable_quotientMap)
      (hF.preimage measurable_quotientMap) hbe hgraphs with hh|hh
  · exact Or.inl (lifted_ae_eq_torus hE hF hh)
  · exact Or.inr (lifted_ae_eq_torus hE hF.compl hh)

theorem isMinimizerAt_connected_common_patch {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hcE : IsPreconnected (frontier (openRepresentative E)))
    (hcF : IsPreconnected (frontier (openRepresentative F)))
    (hpatch : ∃ x∈frontier (openRepresentative E),∀ᶠ z in 𝓝 x,
      z∈frontier (openRepresentative E) ↔ z∈frontier (openRepresentative F)) :
    frontier (openRepresentative E)=frontier (openRepresentative F) ∧
      (E=ᵐ[torusVolume]F ∨ E=ᵐ[torusVolume]Fᶜ) := by
  obtain ⟨μ,H,N,hμ,hN,hp,hae,hbd,_⟩ := Periodic.isMinimizerAt_tubular_normal_stability hV hE hmE
  obtain ⟨ν,K,M,hν,hM,hq,hbe,hcd,_⟩ := Periodic.isMinimizerAt_tubular_normal_stability hW hF hmF
  have he := (CMC_surfaces_unoriented_identity isClosed_frontier isClosed_frontier hcE hcF hN hM hp hq
    (isMinimizerAt_hasNormalizedCMCCharts hV hE hmE hμ hN hp hae hbd)
    (isMinimizerAt_hasNormalizedCMCCharts hW hF hmF hν hM hq hbe hcd) hcd hpatch).1
  exact ⟨he,isMinimizerAt_same_boundary_phase hV hW hE hF hmE hmF he⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalized_CMC_oriented_germ_curvature {B C : Set Torus}
    {N M : Cover → Cover} {H : ℝ}
    (hBch : HasNormalizedCMCCharts B N H)
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hM : ContDiff ℝ (⊤ : ℕ∞) M)
    (hpN : ∀ m x,N (x+latticeVector m)=N x)
    (hpM : ∀ m x,M (x+latticeVector m)=M x)
    {a : Cover} (ha : quotientMap a∈B)
    (huN : ∀ᶠ v in 𝓝 a,‖N v‖=1) (huM : ∀ᶠ v in 𝓝 a,‖M v‖=1)
    (hag : quotientMap a∈orientedSurfaceAgreement B C N M) :
    coverTrace ((fderiv ℝ N a).comp (fderiv ℝ N a))=
      coverTrace ((fderiv ℝ M a).comp (fderiv ℝ M a)) := by
  obtain ⟨hn,f,hf,hf0,_,hfm,_⟩ := hBch a ha
  have hF0 : normalGraph (N a) f 0=0 := by
    change (normalPlaneLinearIsometry (N a)) 0+f 0 • N a=0
    rw [map_zero,hf0,zero_smul,add_zero]
  have hq : Tendsto (fun y : Plane ↦ quotientMap (a+normalGraph (N a) f y))
      (𝓝 0) (𝓝 (quotientMap a)) := by
    have hc : Continuous (fun y : Plane ↦ quotientMap (a+normalGraph (N a) f y)) :=
      continuous_quotientMap.comp (continuous_const.add (normalGraph_contDiff hf).continuous)
    simpa only [hF0,add_zero] using (hc.continuousAt (x := 0)).tendsto
  have hMmatch : ∀ᶠ y in 𝓝 (0 : Plane),M (a+normalGraph (N a) f y)=
      (1 : ℝ) • graphSlopeNormal (N a) (gradient f y) := by
    filter_upwards [hfm,hq.eventually hag] with y hy he
    have hNM := he.2 hy.2.1
    rw [periodic_representative hpN,periodic_representative hpM] at hNM
    rw [←hNM,hy.1,one_smul]
  have hNmatch : ∀ᶠ y in 𝓝 (0 : Plane),N (a+normalGraph (N a) f y)=
      (1 : ℝ) • graphSlopeNormal (N a) (gradient f y) := by
    simpa only [one_smul] using hfm.mono (fun _ hy ↦ hy.1)
  have hnq := graph_normal_extension_curvature a hn hf (0 : Plane) (Or.inl rfl) hN
    (by simpa only [hF0,add_zero] using huN) hNmatch
  have hmq := graph_normal_extension_curvature a hn hf (0 : Plane) (Or.inl rfl) hM
    (by simpa only [hF0,add_zero] using huM) hMmatch
  simpa only [hF0,add_zero] using hnq.trans hmq.symm

theorem normalized_CMC_common_germ_curvature {B C : Set Torus}
    {N M : Cover → Cover} {H K : ℝ}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hM : ContDiff ℝ (⊤ : ℕ∞) M)
    (hpN : ∀ m x,N (x+latticeVector m)=N x)
    (hpM : ∀ m x,M (x+latticeVector m)=M x)
    (hBch : HasNormalizedCMCCharts B N H) (hCch : HasNormalizedCMCCharts C M K)
    (hMbd : ∀ a : Cover,quotientMap a∈C →
      (∀ᶠ v in 𝓝 a,‖M v‖=1) ∧ divergence M a=K)
    {a : Cover} (ha : quotientMap a∈B) (huN : ∀ᶠ v in 𝓝 a,‖N v‖=1)
    (he : ∀ᶠ z in 𝓝 (quotientMap a),z∈B ↔ z∈C) :
    coverTrace ((fderiv ℝ N a).comp (fderiv ℝ N a))=
      coverTrace ((fderiv ℝ M a).comp (fderiv ℝ M a)) := by
  have huM := (hMbd a (he.self_of_nhds.mp ha)).1
  rcases normalized_CMC_common_germ_normals hBch hCch ha he with hsame|hop
  · have hag := normalized_CMC_common_germ_oriented hN.continuous hM.continuous hpN hpM
      hBch hCch ha he (by simpa only [periodic_representative hpN,periodic_representative hpM] using hsame)
    exact normalized_CMC_oriented_germ_curvature hBch hN hM hpN hpM ha huN huM hag
  · have hneg := hCch.neg hM hMbd
    have hnegp : ∀ m x,-M (x+latticeVector m)= -M x := fun m x ↦ congrArg Neg.neg (hpM m x)
    have hag := normalized_CMC_common_germ_oriented hN.continuous hM.continuous.neg hpN hnegp
      hBch hneg ha he (by simpa only [Pi.neg_apply,periodic_representative hpN,periodic_representative hpM] using hop)
    have hh := normalized_CMC_oriented_germ_curvature hBch hN hM.neg hpN hnegp ha huN
      (by simpa only [norm_neg] using huM) hag
    change coverTrace ((fderiv ℝ N a).comp (fderiv ℝ N a))=
      coverTrace ((fderiv ℝ (-M) a).comp (fderiv ℝ (-M) a)) at hh
    simpa only [fderiv_neg,ContinuousLinearMap.neg_comp,ContinuousLinearMap.comp_neg,neg_neg] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_connected_of_common_patch {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hcE : IsPreconnected (frontier (openRepresentative E)))
    (hpatch : ∃ x∈frontier (openRepresentative E),∀ᶠ z in 𝓝 x,
      z∈frontier (openRepresentative E) ↔ z∈frontier (openRepresentative F)) :
    IsPreconnected (frontier (openRepresentative F)) := by
  obtain ⟨μ,H,N,hμ,hN,hp,hae,hbd,_⟩ := Periodic.isMinimizerAt_tubular_normal_stability hV hE hmE
  obtain ⟨ν,K,M,hν,hM,hq,hbe,hcd,_,hconn⟩ := Periodic.isMinimizerAt_connected_or_zero_curvature hW hF hmF
  rcases hconn with hcF|hzero
  · exact hcF
  · have hcd' : ∀ a : Cover,quotientMap a∈frontier (openRepresentative F) →
        (∀ᶠ v in 𝓝 a,‖M v‖=1) ∧ divergence M a=K :=
      fun a ha ↦ ⟨(hcd a ha).1,(hcd a ha).2.1⟩
    have hchE := isMinimizerAt_hasNormalizedCMCCharts hV hE hmE hμ hN hp hae hbd
    have hchF := isMinimizerAt_hasNormalizedCMCCharts hW hF hmF hν hM hq hbe hcd'
    have he := CMC_surface_unoriented_subset isClosed_frontier hcE hN hM hp hq hchE hchF hcd' hpatch
    have hz : ∀ a,quotientMap a∈frontier (openRepresentative E) →
        coverTrace ((fderiv ℝ N a).comp (fderiv ℝ N a))=0 := by
      intro a ha
      rw [normalized_CMC_common_germ_curvature hN hM hp hq hchE hchF hcd' ha (hbd a ha).1 (he _ ha)]
      exact hzero a ((he _ ha).self_of_nhds.mp ha)
    exact False.elim (isMinimizerAt_zero_curvature_not_preconnected hV hE hmE hμ hN hp hae
      (fun a ha ↦ (hbd a ha).1) hz hcE)

theorem isMinimizerAt_common_patch_rigidity {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hcE : IsPreconnected (frontier (openRepresentative E)))
    (hpatch : ∃ x∈frontier (openRepresentative E),∀ᶠ z in 𝓝 x,
      z∈frontier (openRepresentative E) ↔ z∈frontier (openRepresentative F)) :
    frontier (openRepresentative E)=frontier (openRepresentative F) ∧
      (E=ᵐ[torusVolume]F ∨ E=ᵐ[torusVolume]Fᶜ) :=
  isMinimizerAt_connected_common_patch hV hW hE hF hmE hmF hcE
    (isMinimizerAt_connected_of_common_patch hV hW hE hF hmE hmF hcE hpatch) hpatch

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isMinimizerAt_boundary_local_ae {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F O : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    {x : Torus} (hO : O∈𝓝 x)
    (hae : ∀ᵐ z ∂torusVolume,z∈O → (z∈E ↔ z∈F)) :
    x∈frontier (openRepresentative E) ↔ x∈frontier (openRepresentative F) := by
  rw [isMinimizerAt_frontier_openRepresentative hV hE hmE,
    isMinimizerAt_frontier_openRepresentative hW hF hmF]
  constructor
  · intro hx
    exact ⟨measureSupport_local_ae_mono hO (hae.mono (fun _ h ho ↦ (h ho).mp)) hx.1,
      measureSupport_local_ae_mono hO (hae.mono (fun _ h ho ↦ (not_congr (h ho)).mp)) hx.2⟩
  · intro hx
    exact ⟨measureSupport_local_ae_mono hO (hae.mono (fun _ h ho ↦ (h ho).mpr)) hx.1,
      measureSupport_local_ae_mono hO (hae.mono (fun _ h ho ↦ (not_congr (h ho)).mpr)) hx.2⟩

lemma connected_torus_phase {E O : Set Torus} (hE : MeasurableSet E)
    (hO : MeasurableSet O) (hc : IsPreconnected O)
    (hd : Disjoint O (volumeSupport E∩volumeSupport Eᶜ)) :
    torusVolume (O∩E)=0 ∨ torusVolume (O∩Eᶜ)=0 := by
  let U := (volumeSupport E)ᶜ
  let W := (volumeSupport Eᶜ)ᶜ
  have hUW : Disjoint U W := by
    have hs : volumeSupport E∪volumeSupport Eᶜ=univ := by
      unfold volumeSupport
      rw [←Measure.support_add,Measure.restrict_add_restrict_compl hE,Measure.support_eq_univ]
    rw [Set.disjoint_iff_inter_eq_empty]
    change (volumeSupport E)ᶜ∩(volumeSupport Eᶜ)ᶜ=∅
    rw [←compl_union,hs,compl_univ]
  have hsub : O⊆U∪W := by
    intro x hx
    exact not_and_or.mp (fun hb ↦ Set.disjoint_left.mp hd hx hb)
  have hnullE (h : O⊆U) : torusVolume (O∩E)=0 := by
    rw [←Measure.restrict_apply hO]
    exact measure_mono_null h Measure.measure_compl_support
  have hnullC (h : O⊆W) : torusVolume (O∩Eᶜ)=0 := by
    rw [←Measure.restrict_apply hO]
    exact measure_mono_null h Measure.measure_compl_support
  by_cases hn : (O∩U).Nonempty
  · exact Or.inl (hnullE (hc.subset_left_of_subset_union Measure.isOpen_compl_support
      Measure.isOpen_compl_support hUW hsub hn))
  · right
    apply hnullC
    intro x hx
    exact (hsub hx).resolve_left (fun hu ↦ hn ⟨x,hx,hu⟩)

lemma isMinimizerAt_boundary_meets_region {V : ℝ} (hV : V∈Ioo 0 1)
    {E O : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    (hO : MeasurableSet O) (hc : IsPreconnected O)
    (hpos : 0<torusVolume (O∩E)) (hneg : 0<torusVolume (O∩Eᶜ)) :
    (O∩frontier (openRepresentative E)).Nonempty := by
  by_contra hn
  have hd : Disjoint O (volumeSupport E∩volumeSupport Eᶜ) := by
    rw [←isMinimizerAt_frontier_openRepresentative hV hE hmE,Set.disjoint_iff_inter_eq_empty]
    exact Set.not_nonempty_iff_eq_empty.mp hn
  rcases connected_torus_phase hE hO hc hd with he|he
  · exact hpos.ne' he
  · exact hneg.ne' he

theorem isMinimizerAt_local_region_rigidity {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F O : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hcE : IsPreconnected (frontier (openRepresentative E)))
    (hO : IsOpen O) (hcO : IsPreconnected O)
    (hpos : 0<torusVolume (O∩E)) (hneg : 0<torusVolume (O∩Eᶜ))
    (hae : ∀ᵐ z ∂torusVolume,z∈O → (z∈E ↔ z∈F)) : E=ᵐ[torusVolume]F := by
  obtain ⟨x,hxO,hx⟩ := isMinimizerAt_boundary_meets_region hV hE hmE hO.measurableSet hcO hpos hneg
  have hg : ∀ᶠ z in 𝓝 x,z∈frontier (openRepresentative E) ↔ z∈frontier (openRepresentative F) := by
    filter_upwards [hO.mem_nhds hxO] with z hz
    exact isMinimizerAt_boundary_local_ae hV hW hE hF hmE hmF (hO.mem_nhds hz) hae
  rcases (isMinimizerAt_common_patch_rigidity hV hW hE hF hmE hmF hcE ⟨x,hx,hg⟩).2 with he|he
  · exact he
  · have hz : torusVolume O=0 := by
      have hn : ∀ᵐ z ∂torusVolume,z∉O := by
        filter_upwards [hae,he] with z hz hez
        intro hzO
        have hh := hz hzO
        change (z∈E)=(z∈Fᶜ) at hez
        have hc : z∈E ↔ z∉F := Iff.of_eq hez
        tauto
      simpa only [ae_iff,not_not,ofPred_mem_eq] using hn
    exact False.elim (hpos.ne' (measure_mono_null inter_subset_left hz))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def firstSeamFunction (x : Cover) : ℝ := Real.sin (2*Real.pi*x 0)

lemma firstSeamFunction_contDiff : ContDiff ℝ (⊤ : ℕ∞) firstSeamFunction := by
  unfold firstSeamFunction
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x : Cover ↦ x 0) := (EuclideanSpace.proj 0 : Cover →L[ℝ] ℝ).contDiff
  exact ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Cover ↦ 2*Real.pi)).mul hc).sin

lemma firstSeamFunction_periodic :
    ∀ n x,firstSeamFunction (x+latticeVector n)=firstSeamFunction x := by
  intro n x
  unfold firstSeamFunction
  simp only [PiLp.add_apply,latticeVector]
  convert Real.sin_add_int_mul_two_pi (2*Real.pi*x 0) (n 0) using 1
  congr 1
  ring

lemma firstSeamFunction_reflection (x : Cover) :
    firstSeamFunction (firstReflection x)= -firstSeamFunction x := by
  simp only [firstSeamFunction,firstReflection_apply,ite_true,mul_neg,Real.sin_neg]

lemma firstSeam_distance_bound (t : ℝ) :
    4*|t-(round (2*t):ℝ)/2|≤|Real.sin (2*Real.pi*t)| := by
  let n := round (2*t)
  let d := t-(n:ℝ)/2
  have hd : |d|≤1/4 := by
    have hh := abs_sub_round (2*t)
    have he : 2*t-(n:ℝ)=2*d := by dsimp [d]; ring
    rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
    linarith
  have ha : |2*Real.pi*d|≤Real.pi/2 := by
    rw [abs_mul,abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    nlinarith [Real.pi_pos]
  have hh := Real.mul_abs_le_abs_sin ha
  have hleft : 2/Real.pi*|2*Real.pi*d|=4*|d| := by
    rw [abs_mul,abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    field_simp
    ring
  rw [hleft] at hh
  have he : 2*Real.pi*t=2*Real.pi*d+(n:ℝ)*Real.pi := by dsimp [d]; ring
  rw [he,Real.sin_add_int_mul_pi,abs_mul,abs_zpow,abs_neg,abs_one,one_zpow,one_mul]
  exact hh

lemma smooth_periodic_lipschitz {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hp : ∀ n x,F (x+latticeVector n)=F x) :
    ∃ L : ℝ≥0,LipschitzWith L F := by
  obtain ⟨C,hC,hb⟩ := periodic_bounded (hF.continuous_fderiv (by simp)) (fderiv_periodic hp)
  refine ⟨⟨C,hC⟩,lipschitzWith_of_nnnorm_fderiv_le (hF.differentiable (by simp)) ?_⟩
  intro x
  exact NNReal.coe_le_coe.mp (hb x)

lemma reflection_symmetric_seam_zero {F : Cover → Cover}
    (hp : ∀ n x,F (x+latticeVector n)=F x)
    (hs : reflectionPullback F=F) {y : Cover} {n : ℤ} (hy : y 0=(n:ℝ)/2) :
    F y 0=0 := by
  have he : firstReflection y=y+latticeVector (Pi.single 0 (-n)) := by
    ext i
    by_cases hi : i=0
    · subst i
      simp only [firstReflection_apply,ite_true,PiLp.add_apply,latticeVector,
        Pi.single_eq_same,Int.cast_neg,hy]
      ring
    · simp [firstReflection_apply,hi,latticeVector,Pi.single_apply]
  have hh := congrArg (fun G : Cover → Cover ↦ G y 0) hs
  change firstReflection (F (firstReflection y)) 0=F y 0 at hh
  simp only [he,hp,firstReflection_apply,ite_true] at hh
  linarith

lemma reflection_symmetric_seam_bound {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hp : ∀ n x,F (x+latticeVector n)=F x)
    (hs : reflectionPullback F=F) :
    ∃ C : ℝ,0≤C ∧ ∀ x,|F x 0|≤C*|firstSeamFunction x| := by
  obtain ⟨L,hL⟩ := smooth_periodic_lipschitz hF hp
  refine ⟨(L:ℝ)/4,by positivity,fun x ↦ ?_⟩
  let n := round (2*x 0)
  let y : Cover := WithLp.toLp 2 (Function.update (WithLp.ofLp x) 0 ((n:ℝ)/2))
  have hy : y 0=(n:ℝ)/2 := by simp [y]
  have hz := reflection_symmetric_seam_zero hp hs hy
  have he : x-y=(x 0-(n:ℝ)/2) • EuclideanSpace.single 0 1 := by
    ext i
    by_cases hi : i=0
    · subst i; simp [y]
    · simp [y,hi]
  have hd : dist x y=|x 0-(n:ℝ)/2| := by
    rw [dist_eq_norm,he,norm_smul,Real.norm_eq_abs]
    simp
  have hc : |F x 0|≤dist (F x) (F y) := by
    rw [dist_eq_norm]
    have hh := PiLp.norm_apply_le (F x-F y) 0
    simpa [PiLp.sub_apply,hz] using hh
  have hh := (hc.trans (hL.dist_le_mul x y))
  rw [hd] at hh
  have hsine := firstSeam_distance_bound (x 0)
  change 4*|x 0-(n:ℝ)/2|≤|firstSeamFunction x| at hsine
  nlinarith [mul_le_mul_of_nonneg_left hsine L.coe_nonneg]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma fderiv_firstSeamFunction (x v : Cover) :
    fderiv ℝ firstSeamFunction x v=2*Real.pi*Real.cos (2*Real.pi*x 0)*v 0 := by
  let L : Cover →L[ℝ] ℝ := (2*Real.pi) • (EuclideanSpace.proj 0)
  have hd := (Real.hasDerivAt_sin (L x)).comp_hasFDerivAt x L.hasFDerivAt
  change HasFDerivAt firstSeamFunction _ x at hd
  rw [hd.fderiv]
  simp only [smul_apply,L,EuclideanSpace.coe_proj,smul_eq_mul]
  ring

lemma seam_cutoff_error_bound {F : Cover → Cover} {C K ε : ℝ}
    (hC : 0≤C) (hK : 0≤K)
    (hb : ∀ x,|F x 0|≤C*|firstSeamFunction x|)
    (hder : ∀ t,‖deriv Real.smoothTransition t‖≤K) (hε : 0<ε) (x : Cover) :
    |⟪gradient (sublevelCutoff firstSeamFunction 0 ε) x,F x⟫| ≤
      K*(2*Real.pi)*C := by
  by_cases hx : firstSeamFunction x≤ -ε ∨ 0≤firstSeamFunction x
  · rw [sublevelCutoff_gradient_zero (firstSeamFunction_contDiff.differentiable (by simp))
      hε 0 x (by simpa only [zero_sub] using hx),inner_zero_left,abs_zero]
    positivity
  push Not at hx
  have hf : |F x 0|≤C*ε := (hb x).trans
    (mul_le_mul_of_nonneg_left (by rw [abs_of_neg hx.2]; linarith) hC)
  rw [inner_gradient_left,fderiv_sublevelCutoff
    (firstSeamFunction_contDiff.differentiable (by simp) x)]
  simp only [smul_apply,neg_apply,smul_eq_mul,
    abs_mul,abs_div,abs_neg,abs_of_pos hε,fderiv_firstSeamFunction]
  rw [abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_pos Real.pi_pos]
  have hd : |deriv Real.smoothTransition ((0-firstSeamFunction x)/ε)|≤K := hder _
  calc
    _ ≤ (K/ε)*((2*Real.pi)*1*(C*ε)) := mul_le_mul
      (div_le_div_of_nonneg_right hd hε.le)
      (mul_le_mul (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity))
        hf (abs_nonneg _) (by positivity))
      (by positivity) (div_nonneg hK hε.le)
    _ = _ := by field_simp

lemma seam_cutoff_error_tendsto {F : Cover → Cover} (x : Cover) :
    Tendsto (fun n : ℕ ↦ ⟪gradient
      (sublevelCutoff firstSeamFunction 0 (1/((n:ℝ)+1))) x,F x⟫) atTop (𝓝 0) := by
  have ht := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have he : ∀ n : ℕ,0<1/((n:ℝ)+1) := fun n ↦ by positivity
  have hz : ∀ᶠ n : ℕ in atTop,gradient
      (sublevelCutoff firstSeamFunction 0 (1/((n:ℝ)+1))) x=0 := by
    by_cases hx : 0≤firstSeamFunction x
    · exact Eventually.of_forall fun n ↦ sublevelCutoff_gradient_zero
        (firstSeamFunction_contDiff.differentiable (by simp)) (he n) 0 x (Or.inr hx)
    · have hx' : 0< -firstSeamFunction x := neg_pos.mpr (lt_of_not_ge hx)
      filter_upwards [ht.eventually (gt_mem_nhds hx')] with n hn
      apply sublevelCutoff_gradient_zero
        (firstSeamFunction_contDiff.differentiable (by simp)) (he n) 0 x
      exact Or.inl (by linarith)
  apply tendsto_const_nhds.congr'
  filter_upwards [hz] with n hn
  rw [hn,inner_zero_left]

lemma reflectionPullback_sub (F G : Cover → Cover) :
    reflectionPullback (fun x ↦ F x-G x)=
      fun x ↦ reflectionPullback F x-reflectionPullback G x := by
  funext x
  simp only [reflectionPullback,map_sub]

lemma seam_cutoff_integral_error_tendsto {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hp : ∀ n x,F (x+latticeVector n)=F x)
    (hs : reflectionPullback F=F) (E : Set Torus) :
    Tendsto (fun n : ℕ ↦ ∫ x in fundamentalCube∩quotientMap ⁻¹' E,
      ⟪gradient (sublevelCutoff firstSeamFunction 0 (1/((n:ℝ)+1))) x,F x⟫)
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := reflection_symmetric_seam_bound hF hp hs
  obtain ⟨K,hK,hder⟩ := smoothTransition_exists_deriv_bound
  have ht := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (fundamentalCube∩quotientMap ⁻¹' E))
    (bound := fun _ ↦ K*(2*Real.pi)*C)
    (F := fun n : ℕ ↦ fun x ↦ ⟪gradient
      (sublevelCutoff firstSeamFunction 0 (1/((n:ℝ)+1))) x,F x⟫)
    (f := fun _ ↦ (0:ℝ))
    (fun n ↦ ((gradient_contDiff (sublevelCutoff_contDiff firstSeamFunction_contDiff 0 _)).continuous.inner
      hF.continuous).aestronglyMeasurable)
    (?_ : Integrable (fun _ : Cover ↦ K*(2*Real.pi)*C)
      (volume.restrict (fundamentalCube∩quotientMap ⁻¹' E)))
    (fun n ↦ Eventually.of_forall fun x ↦ by
      simpa only [Real.norm_eq_abs] using seam_cutoff_error_bound hC hK.le hb hder (by positivity) x)
    (Eventually.of_forall fun x ↦ seam_cutoff_error_tendsto x)
  · simpa only [integral_zero] using ht
  · exact (integrableOn_const (μ := volume) (s := fundamentalCube)
      (by rw [volume_fundamentalCube]; exact ENNReal.one_ne_top)).mono_set inter_subset_left

theorem symmetric_partition_flux_le {E : Set Torus} (hP : perimeter E≠⊤)
    {F G : Cover → Cover} (hF : AdmissibleField F) (hG : AdmissibleField G)
    (hsF : reflectionPullback F=F) (hsG : reflectionPullback G=G) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' (E∩sublevelRegion firstSeamFunction 0),divergence F x)+
    (∫ x in fundamentalCube∩quotientMap ⁻¹' (E\sublevelRegion firstSeamFunction 0),divergence G x)≤
      (perimeter E).toReal := by
  let ε : ℕ → ℝ := fun n ↦ 1/((n:ℝ)+1)
  let w : ℕ → Cover → ℝ := fun n ↦ sublevelCutoff firstSeamFunction 0 (ε n)
  have hw (n) : ContDiff ℝ (⊤ : ℕ∞) (w n) := sublevelCutoff_contDiff firstSeamFunction_contDiff _ _
  have hwp (n) : ∀ m x,w n (x+latticeVector m)=w n x :=
    sublevelCutoff_periodic firstSeamFunction_periodic _ _
  let H : ℕ → Cover → Cover := fun n x ↦ w n x • F x+(1-w n x) • G x
  have hH n : AdmissibleField (H n) := admissible_convex_cutoff (hw n) (hwp n)
    (sublevelCutoff_mem_Icc _ _ _) hF hG
  have hd (n) (x) : divergence (H n) x=w n x*divergence F x+
      (1-w n x)*divergence G x+⟪gradient (w n) x,F x-G x⟫ := by
    have hwd : DifferentiableAt ℝ (fun y ↦ w n y • F y) x :=
      ((hw n).smul hF.1).differentiable (by simp) x
    have hwc : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ 1-w n x) := contDiff_const.sub (hw n)
    have hgd : DifferentiableAt ℝ (fun y ↦ (1-w n y) • G y) x :=
      (hwc.smul hG.1).differentiable (by simp) x
    change divergence (fun y ↦ w n y • F y+(1-w n y) • G y) x=_
    rw [divergence_add_fields hwd hgd,
      divergence_smul_function ((hw n).differentiable (by simp) x) (hF.1.differentiable (by simp) x),
      divergence_smul_function (hwc.differentiable (by simp) x)
        (hG.1.differentiable (by simp) x),gradient_const_sub,inner_neg_left,inner_sub_right]
    ring
  have ht := partition_flux_tendsto (E := E)
    (measurableSet_sublevelRegion firstSeamFunction_contDiff.continuous.measurable 0)
    (fun n ↦ (hw n).continuous) (fun n ↦ sublevelCutoff_mem_Icc _ _ _)
    (sublevelCutoff_tendsto firstSeamFunction_periodic (ε := ε) (fun n ↦ by dsimp [ε]; positivity)
      tendsto_one_div_add_atTop_nhds_zero_nat 0) hF hG
  have he := seam_cutoff_integral_error_tendsto (hF.1.sub hG.1)
    (fun n x ↦ by rw [hF.2.1,hG.2.1]) (by rw [reflectionPullback_sub,hsF,hsG]) E
  have ht' := ht.add he
  rw [add_zero] at ht'
  apply le_of_tendsto ht'
  apply Eventually.of_forall
  intro n
  have hii : IntegrableOn (fun x ↦ ⟪gradient (w n) x,F x-G x⟫)
      (fundamentalCube∩quotientMap ⁻¹' E) :=
    (integrableOn_periodic_continuous ((gradient_contDiff (hw n)).continuous.inner
      (hF.1.continuous.sub hG.1.continuous)) (fun m x ↦ by simp only [Pi.sub_apply,gradient_periodic (hwp n),hF.2.1,hG.2.1])).mono_set inter_subset_left
  have hiH := (integrableOn_divergence (hH n).1).mono_set
    (s := fundamentalCube∩quotientMap ⁻¹' E) inter_subset_left
  have heq : (fun x ↦ w n x*divergence F x+(1-w n x)*divergence G x)=
      fun x ↦ divergence (H n) x-⟪gradient (w n) x,F x-G x⟫ := by
    funext x
    rw [hd]
    ring
  change (∫ x in fundamentalCube∩quotientMap ⁻¹' E,w n x*divergence F x+(1-w n x)*divergence G x)+
    (∫ x in fundamentalCube∩quotientMap ⁻¹' E,⟪gradient (w n) x,F x-G x⟫)≤_
  rw [heq,integral_sub hiH hii,sub_add_cancel]
  exact (le_abs_self _).trans (abs_flux_le_perimeter hP (hH n))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma firstSeam_representative_reflection (z : Torus) :
    firstSeamFunction (representative (torusFirstReflection z))=
      -firstSeamFunction (representative z) := by
  rw [← quotientMap_representative z,← firstReflection_quotient,
    periodic_representative firstSeamFunction_periodic,
    firstSeamFunction_reflection,periodic_representative firstSeamFunction_periodic]

lemma firstSeam_null :
    torusVolume {z | firstSeamFunction (representative z)=0}=0 := by
  apply measure_mono_null (t := ⋃ n : ℤ,
    {z : Torus | z 0=(((n:ℝ)/2:ℝ):AddCircle (1:ℝ))})
  · intro z hz
    obtain ⟨n,hn⟩ := Real.sin_eq_zero_iff.mp hz
    apply mem_iUnion.mpr
    refine ⟨n,?_⟩
    change z 0=(((n:ℝ)/2:ℝ):AddCircle (1:ℝ))
    have he : representative z 0=(n:ℝ)/2 := by
      nlinarith [Real.pi_pos]
    have hq := congrArg (fun z : Torus ↦ z 0) (quotientMap_representative z)
    change ((representative z 0 : ℝ):AddCircle (1:ℝ))=z 0 at hq
    rw [← hq,he]
  · apply measure_iUnion_null
    intro n
    change torusVolume ((fun z : Torus ↦ z 0) ⁻¹' {(((n:ℝ)/2:ℝ):AddCircle (1:ℝ))})=0
    rw [(torus_coordinate_measurePreserving 0).measure_preimage (measurableSet_singleton _).nullMeasurableSet]
    rw [← Metric.closedBall_zero,AddCircle.volume_closedBall]
    norm_num

def reflectionClosure (A : Set Torus) : Set Torus :=
  A∪torusFirstReflection ⁻¹' A

lemma measurableSet_reflectionClosure {A : Set Torus} (hA : MeasurableSet A) :
    MeasurableSet (reflectionClosure A) :=
  hA.union (hA.preimage torusFirstReflection.continuous.measurable)

lemma reflected_half_disjoint (E : Set Torus) :
    Disjoint (E∩sublevelRegion firstSeamFunction 0)
      (torusFirstReflection ⁻¹' (E∩sublevelRegion firstSeamFunction 0)) := by
  apply disjoint_left.mpr
  intro z hz hr
  have h1 : firstSeamFunction (representative z)<0 := hz.2
  have h2 : firstSeamFunction (representative (torusFirstReflection z))<0 := hr.2
  rw [firstSeam_representative_reflection] at h2
  linarith

lemma reflected_other_half_aedisjoint (E : Set Torus) :
    AEDisjoint torusVolume (E\sublevelRegion firstSeamFunction 0)
      (torusFirstReflection ⁻¹' (E\sublevelRegion firstSeamFunction 0)) := by
  apply measure_mono_null (t := {z | firstSeamFunction (representative z)=0}) ?_ firstSeam_null
  intro z hz
  have h1 : ¬firstSeamFunction (representative z)<0 := hz.1.2
  have h2 : ¬firstSeamFunction (representative (torusFirstReflection z))<0 := hz.2.2
  rw [firstSeam_representative_reflection] at h2
  change firstSeamFunction (representative z)=0
  linarith

lemma lift_aedisjoint {A B : Set Torus} (hd : AEDisjoint torusVolume A B) :
    AEDisjoint volume (fundamentalCube∩quotientMap ⁻¹' A)
      (fundamentalCube∩quotientMap ⁻¹' B) := by
  have he : (A∩B:Set Torus)=ᵐ[torusVolume] (∅:Set Torus) := ae_eq_empty.mpr hd
  have hh := liftSet_congr_ae he
  simp only [preimage_empty,inter_empty] at hh
  change volume ((fundamentalCube∩quotientMap ⁻¹' A)∩
    (fundamentalCube∩quotientMap ⁻¹' B))=0
  have hs : (fundamentalCube∩quotientMap ⁻¹' A)∩
      (fundamentalCube∩quotientMap ⁻¹' B)=fundamentalCube∩quotientMap ⁻¹' (A∩B) := by aesop
  rw [hs]
  exact ae_eq_empty.mp hh

lemma flux_union_ae {F : Cover → Cover} (hF : AdmissibleField F)
    {A B : Set Torus} (hB : MeasurableSet B) (hd : AEDisjoint torusVolume A B) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' (A∪B),divergence F x)=
      (∫ x in fundamentalCube∩quotientMap ⁻¹' A,divergence F x)+
      (∫ x in fundamentalCube∩quotientMap ⁻¹' B,divergence F x) := by
  rw [preimage_union,inter_union_distrib_left]
  exact setIntegral_union₀ (lift_aedisjoint hd)
    ((measurableSet_fundamentalCube.inter (measurable_quotientMap hB)).nullMeasurableSet)
    ((integrableOn_divergence hF.1).mono_set inter_subset_left)
    ((integrableOn_divergence hF.1).mono_set inter_subset_left)

def reflectionMean (F : Cover → Cover) : Cover → Cover :=
  fun x ↦ (1/2:ℝ) • F x+(1/2:ℝ) • reflectionPullback F x

lemma reflectionMean_admissible {F : Cover → Cover} (hF : AdmissibleField F) :
    AdmissibleField (reflectionMean F) := by
  have hh := admissible_convex_cutoff (w := fun _ : Cover ↦ (1/2:ℝ))
    contDiff_const (fun _ _ ↦ rfl) (fun _ ↦ by norm_num) hF (reflectionPullback_admissible hF)
  norm_num at hh
  exact hh

lemma reflectionMean_symmetric (F : Cover → Cover) :
    reflectionPullback (reflectionMean F)=reflectionMean F := by
  funext x
  simp only [reflectionPullback,reflectionMean,map_add,map_smul,firstReflection_involutive]
  exact add_comm _ _

lemma divergence_reflectionMean {F : Cover → Cover} (hF : AdmissibleField F) (x : Cover) :
    divergence (reflectionMean F) x=
      (1/2:ℝ)*divergence F x+(1/2:ℝ)*divergence (reflectionPullback F) x := by
  have hG := reflectionPullback_admissible hF
  have hFd := hF.1.differentiable (by simp) x
  have hGd := hG.1.differentiable (by simp) x
  change divergence (fun y ↦ (1/2:ℝ) • F y+(1/2:ℝ) • reflectionPullback F y) x=_
  have hFd2 : DifferentiableAt ℝ (fun y ↦ (1/2:ℝ) • F y) x := hFd.const_smul (1/2:ℝ)
  have hGd2 : DifferentiableAt ℝ (fun y ↦ (1/2:ℝ) • reflectionPullback F y) x := hGd.const_smul (1/2:ℝ)
  rw [divergence_add_fields hFd2 hGd2,
    divergence_const_smul hFd,divergence_const_smul hGd]

lemma flux_reflectionClosure {F : Cover → Cover} (hF : AdmissibleField F)
    {A : Set Torus} (hA : MeasurableSet A)
    (hd : AEDisjoint torusVolume A (torusFirstReflection ⁻¹' A)) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' reflectionClosure A,divergence F x)=
      2*(∫ x in fundamentalCube∩quotientMap ⁻¹' A,divergence (reflectionMean F) x) := by
  rw [reflectionClosure,flux_union_ae hF
    (hA.preimage torusFirstReflection.continuous.measurable) hd,flux_firstReflection hF hA]
  simp_rw [divergence_reflectionMean hF]
  rw [integral_add
    (((integrableOn_divergence hF.1).mono_set inter_subset_left).const_mul _)
    (((integrableOn_divergence (reflectionPullback_admissible hF).1).mono_set inter_subset_left).const_mul _),
    integral_const_mul,integral_const_mul]
  ring

lemma volume_reflectionClosure {A : Set Torus} (hA : MeasurableSet A)
    (hd : AEDisjoint torusVolume A (torusFirstReflection ⁻¹' A)) :
    (torusVolume (reflectionClosure A)).toReal=2*(torusVolume A).toReal := by
  unfold reflectionClosure
  rw [measure_union₀ (hA.preimage torusFirstReflection.continuous.measurable).nullMeasurableSet hd,
    torusFirstReflection_measurePreserving.measure_preimage hA.nullMeasurableSet,
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma perimeter_pair_le_of_flux_bound {A B : Set Torus}
    (hA : NullMeasurableSet A torusVolume) (hB : NullMeasurableSet B torusVolume) {C : ℝ}
    (hb : ∀ F G : Cover → Cover,AdmissibleField F → AdmissibleField G →
      (∫ x in fundamentalCube∩quotientMap ⁻¹' A,divergence F x)+
      (∫ x in fundamentalCube∩quotientMap ⁻¹' B,divergence G x)≤C) :
    FinitePerimeter A ∧ FinitePerimeter B ∧ (perimeter A).toReal+(perimeter B).toReal≤C := by
  have ha : perimeter A≤ENNReal.ofReal C := by
    apply iSup_le; intro F
    apply iSup_le; intro hF
    apply ENNReal.ofReal_le_ofReal
    simpa only [divergence_zero,integral_zero,add_zero] using hb F (fun _ ↦ 0) hF admissible_zero
  have hc : perimeter B≤ENNReal.ofReal C := by
    apply iSup_le; intro G
    apply iSup_le; intro hG
    apply ENNReal.ofReal_le_ofReal
    simpa only [divergence_zero,integral_zero,zero_add] using hb (fun _ ↦ 0) G admissible_zero hG
  refine ⟨⟨hA,ha.trans_lt ENNReal.ofReal_lt_top⟩,
    ⟨hB,hc.trans_lt ENNReal.ofReal_lt_top⟩,?_⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨F,hF,hf⟩ := exists_admissible_flux_gt A (half_pos hε)
  obtain ⟨G,hG,hg⟩ := exists_admissible_flux_gt B (half_pos hε)
  linarith [hb F G hF hG]

theorem reflected_halves_perimeter_bound {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E≠⊤) :
    FinitePerimeter (reflectionClosure (E∩sublevelRegion firstSeamFunction 0)) ∧
    FinitePerimeter (reflectionClosure (E\sublevelRegion firstSeamFunction 0)) ∧
      (perimeter (reflectionClosure (E∩sublevelRegion firstSeamFunction 0))).toReal+
      (perimeter (reflectionClosure (E\sublevelRegion firstSeamFunction 0))).toReal≤
        2*(perimeter E).toReal := by
  have hB := measurableSet_sublevelRegion firstSeamFunction_contDiff.continuous.measurable 0
  apply perimeter_pair_le_of_flux_bound
    (measurableSet_reflectionClosure (hE.inter hB)).nullMeasurableSet
    (measurableSet_reflectionClosure (hE.diff hB)).nullMeasurableSet
  intro F G hF hG
  rw [flux_reflectionClosure hF (hE.inter hB) (reflected_half_disjoint E).aedisjoint,
    flux_reflectionClosure hG (hE.diff hB) (reflected_other_half_aedisjoint E)]
  have hh := symmetric_partition_flux_le hP (reflectionMean_admissible hF)
    (reflectionMean_admissible hG) (reflectionMean_symmetric F) (reflectionMean_symmetric G)
  linarith

lemma volume_halves_sum {E : Set Torus} (_hE : MeasurableSet E) :
    (torusVolume (E∩sublevelRegion firstSeamFunction 0)).toReal+
      (torusVolume (E\sublevelRegion firstSeamFunction 0)).toReal=(torusVolume E).toReal := by
  rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    measure_inter_add_sdiff E
      (measurableSet_sublevelRegion firstSeamFunction_contDiff.continuous.measurable 0)]

theorem bisected_reflection_minimizers {V : ℝ} {E : Set Torus}
    (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hhalf : (torusVolume (E∩sublevelRegion firstSeamFunction 0)).toReal=
      (torusVolume E).toReal/2) :
    IsMinimizerAt V (reflectionClosure (E∩sublevelRegion firstSeamFunction 0)) ∧
    IsMinimizerAt V (reflectionClosure (E\sublevelRegion firstSeamFunction 0)) := by
  let A := reflectionClosure (E∩sublevelRegion firstSeamFunction 0)
  let B := reflectionClosure (E\sublevelRegion firstSeamFunction 0)
  have hm := measurableSet_sublevelRegion firstSeamFunction_contDiff.continuous.measurable 0
  obtain ⟨hA,hB,hP⟩ := reflected_halves_perimeter_bound hE hmin.1.2.ne
  have hvA : torusVolume A=torusVolume E := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    rw [volume_reflectionClosure (hE.inter hm) (reflected_half_disjoint E).aedisjoint,hhalf]
    ring
  have hvB : torusVolume B=torusVolume E := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    rw [volume_reflectionClosure (hE.diff hm) (reflected_other_half_aedisjoint E)]
    have hh := volume_halves_sum hE
    linarith
  have hpa := hmin.2.2 A hA (hvA.trans hmin.2.1)
  have hpb := hmin.2.2 B hB (hvB.trans hmin.2.1)
  have hpAr : (perimeter E).toReal≤(perimeter A).toReal :=
    ENNReal.toReal_mono hA.2.ne hpa
  have hpBr : (perimeter E).toReal≤(perimeter B).toReal :=
    ENNReal.toReal_mono hB.2.ne hpb
  have heA : perimeter A=perimeter E := by
    apply (ENNReal.toReal_eq_toReal_iff' hA.2.ne hmin.1.2.ne).mp
    change (perimeter A).toReal+(perimeter B).toReal≤2*(perimeter E).toReal at hP
    linarith
  have heB : perimeter B=perimeter E := by
    apply (ENNReal.toReal_eq_toReal_iff' hB.2.ne hmin.1.2.ne).mp
    change (perimeter A).toReal+(perimeter B).toReal≤2*(perimeter E).toReal at hP
    linarith
  exact ⟨⟨hA,hvA.trans hmin.2.1,fun D hD hv ↦ heA.le.trans (hmin.2.2 D hD hv)⟩,
    ⟨hB,hvB.trans hmin.2.1,fun D hD hv ↦ heB.le.trans (hmin.2.2 D hD hv)⟩⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

end CubicTorus
end
end
end

end OAI
