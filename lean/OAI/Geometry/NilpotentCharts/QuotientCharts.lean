import Mathlib
import OAI.Geometry.NilpotentCharts.CentralAxes
import OAI.Geometry.NilpotentCharts.QuotientLie
import OAI.Geometry.NilpotentCharts.QuotientTopology
import OAI.Geometry.NilpotentCharts.SmoothCalculus

namespace OAI

/-! Smooth central quotient charts, covering maps and central homeomorphisms. -/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators commutatorElement
open Function Set Manifold Topology Filter

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀] {G : Type} [Group G] [TopologicalSpace G]
  [ChartedSpace (E₀) G]
  [LieGroup (𝓘(ℝ, E₀)) ∞ G] [T2Space G]
local notation "𝓘ₙ" => 𝓘(ℝ, E₀)
local notation "E" => E₀

omit [FiniteDimensional ℝ E₀] [T2Space G] in
lemma exists_smooth_localChart_of_derivative
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (f : V → G) (hf0 : f 0 = 1) (hf : ContMDiff 𝓘(ℝ,V) 𝓘ₙ ∞ f)
    (L : V ≃L[ℝ] E) (hD : (mfderiv 𝓘(ℝ,V) 𝓘ₙ f 0 : V →L[ℝ] E) = L.toContinuousLinearMap) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ,V) 𝓘ₙ V G ∞,
      0 ∈ e.source ∧ EqOn e f e.source := by
  let c := chartAt E (1 : G)
  let cD : PartialDiffeomorph 𝓘ₙ 𝓘ₙ G E ∞ := {
    c with
    contMDiffOn_toFun := contMDiffOn_chart
    contMDiffOn_invFun := contMDiffOn_chart_symm }
  let U := f ⁻¹' c.source
  have hU : IsOpen U := c.open_source.preimage hf.continuous
  have h0 : (0 : V) ∈ U := by
    change f 0 ∈ c.source
    rw [hf0]
    exact mem_chart_source _ _
  have hcf : ContDiffOn ℝ ∞ (c ∘ f) U :=
    ((contMDiffOn_chart (I := 𝓘ₙ) (n := ∞)).comp hf.contMDiffOn (fun _ hx => hx)).contDiffOn
  have hcd : HasFDerivAt (c ∘ f) L.toContinuousLinearMap 0 :=
    chart_comp_hasFDerivAt_one f hf0 (hf.mdifferentiableAt (by simp)) _ hD
  obtain ⟨e₀,he₀,he₀U,he₀eq⟩ := RawSliceInverse.exists_smooth_local_inverse (c ∘ f) U hU h0 hcf L hcd
  refine ⟨e₀.trans cD.symm, ?_, ?_⟩
  · refine ⟨he₀, ?_⟩
    change e₀ 0 ∈ c.target
    rw [he₀eq]
    exact c.map_source h0
  · intro x hx
    change c.symm (e₀ x) = f x
    rw [he₀eq]
    exact c.left_inv (he₀U hx.1)

 

theorem exists_productSlice_partialDiffeomorph (W K : Submodule ℝ E) (hWK : IsCompl W K) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, W × K) 𝓘ₙ (W × K) G ∞,
      0 ∈ e.source ∧ EqOn e (productSlice (G := G) W K) e.source := by
  apply exists_smooth_localChart_of_derivative (productSlice (G := G) W K)
    (productSlice_zero W K) (productSlice_contMDiff W K)
    (W.prodEquivOfIsCompl K hWK).toContinuousLinearEquiv
  exact productSlice_derivative W K

end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀] {G : Type} [Group G] [TopologicalSpace G]
  [ChartedSpace (E₀) G]
  [LieGroup (𝓘(ℝ, E₀)) ∞ G] [T2Space G]
local notation "𝓘ₙ" => 𝓘(ℝ, E₀)
local notation "E" => E₀
local notation "C" => RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)
local notation "S" => MonoidHom.range (centralAxesHom (G := G) (E₀ := E₀))

lemma quotient_coordinates_smooth (W : Submodule ℝ E)
    (e : PartialDiffeomorph 𝓘(ℝ, W × C) 𝓘ₙ (W × C) G ∞)
    (he : EqOn e (productSlice W C) e.source)
    (q : OpenPartialHomeomorph W (G ⧸ S))
    (hq : (q : W → G ⧸ S) = (QuotientGroup.mk : G → G ⧸ S) ∘ subspaceAxes W)
    (hqe : ∀ w ∈ q.source, (w, (0 : C)) ∈ e.source) :
    ContMDiffOn 𝓘ₙ 𝓘(ℝ,W) ∞ (q.symm ∘ QuotientGroup.mk)
      ((QuotientGroup.mk : G → G ⧸ S) ⁻¹' q.target) := by
  intro g hg
  let u := q.symm (QuotientGroup.mk g)
  have hu : u ∈ q.source := q.map_target hg
  have hqu : q u = QuotientGroup.mk g := q.right_inv hg
  let z := (subspaceAxes (G := G) W u)⁻¹ * g
  have hz : z ∈ S := QuotientGroup.eq.mp (by simpa only [hq, Function.comp_apply] using hqu)
  let R : G → G := fun x => x * z⁻¹
  have hR : ContMDiff 𝓘ₙ 𝓘ₙ ∞ R := contMDiff_id.mul contMDiff_const
  have hRg : R g = subspaceAxes W u := by simp [R,z]
  have hezero : e (u,0) = subspaceAxes W u := by
    rw [he (hqe _ hu)]
    simp only [productSlice, subspaceAxes_zero, mul_one]
  have hRt : R g ∈ e.target := by rw [hRg, ← hezero]; exact e.map_source (hqe _ hu)
  have hsymm : e.symm (R g) = (u, 0) := by
    rw [hRg, ← hezero]
    exact e.toPartialEquiv.left_inv (hqe _ hu)
  let A : Set G := e.target ∩ e.symm ⁻¹' (q.source ×ˢ (Set.univ : Set C))
  have hA : A ∈ 𝓝 (R g) := by
    refine Filter.inter_mem (e.open_target.mem_nhds hRt) ?_
    apply e.toOpenPartialHomeomorph.continuousAt_symm hRt
    change q.source ×ˢ (Set.univ : Set C) ∈ 𝓝 (e.symm (R g))
    rw [hsymm]
    exact (q.open_source.prod isOpen_univ).mem_nhds ⟨hu,mem_univ _⟩
  have hnear : R ⁻¹' A ∈ 𝓝 g := hR.continuous.tendsto g hA
  have hequiv : (q.symm ∘ QuotientGroup.mk) =ᶠ[𝓝 g] (fun x => (e.symm (R x)).1) := by
    filter_upwards [hnear] with x hx
    have hp := e.map_target hx.1
    have hprod : productSlice W C (e.symm (R x)) = R x :=
      (he hp).symm.trans (e.right_inv hx.1)
    have hqprod : q (e.symm (R x)).1 = QuotientGroup.mk (R x) := by
      rw [hq]
      exact (quotient_productSlice W (e.symm (R x))).symm.trans (congrArg QuotientGroup.mk hprod)
    have hqx : (QuotientGroup.mk (R x) : G ⧸ S) = QuotientGroup.mk x := by
      symm
      apply QuotientGroup.eq.mpr
      change x⁻¹ * (x * z⁻¹) ∈ S
      rw [inv_mul_cancel_left]
      exact (S).inv_mem hz
    change q.symm (QuotientGroup.mk x) = (e.symm (R x)).1
    rw [← hqx, ← hqprod]
    exact q.left_inv hx.2.1
  have hinv : ContMDiffAt 𝓘ₙ 𝓘(ℝ,W × C) ∞ e.symm (R g) :=
    e.contMDiffOn_invFun.contMDiffAt (e.open_target.mem_nhds hRt)
  have hF : ContMDiffAt 𝓘ₙ 𝓘(ℝ,W) ∞ (fun x => (e.symm (R x)).1) g :=
    (ContinuousLinearMap.fst ℝ W C).contDiff.contMDiff.contMDiffAt.comp g
      (hinv.comp g (hR g))
  exact (hF.congr_of_eventuallyEq hequiv).contMDiffWithinAt

 

theorem exists_central_quotient_smoothChart (W : Submodule ℝ E) (hWC : IsCompl W C) :
    ∃ q : OpenPartialHomeomorph W (G ⧸ S), 0 ∈ q.source ∧
      (q : W → G ⧸ S) = (QuotientGroup.mk : G → G ⧸ S) ∘ subspaceAxes W ∧
      ContMDiffOn 𝓘ₙ 𝓘(ℝ,W) ∞ (q.symm ∘ QuotientGroup.mk)
        ((QuotientGroup.mk : G → G ⧸ S) ⁻¹' q.target) := by
  obtain ⟨e,h0,he⟩ := exists_productSlice_partialDiffeomorph (G := G) W C hWC
  obtain ⟨q₀,hq₀0,hq₀⟩ := exists_central_quotient_openChart (G := G) W hWC
  let U : Set W := (fun w => (w, (0 : C))) ⁻¹' e.source
  have hU : IsOpen U := e.open_source.preimage (continuous_id.prodMk continuous_const)
  let q := q₀.restr U
  have hqs : q.source = q₀.source ∩ U := q₀.restr_source' U hU
  have hq0 : (0 : W) ∈ q.source := by rw [hqs]; exact ⟨hq₀0,h0⟩
  have hq : (q : W → G ⧸ S) = (QuotientGroup.mk : G → G ⧸ S) ∘ subspaceAxes W := hq₀
  refine ⟨q,hq0,hq,quotient_coordinates_smooth W e he q hq ?_⟩
  intro w hw
  exact ((hqs ▸ hw).2)

end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀] {G : Type} [Group G] [TopologicalSpace G]
  [ChartedSpace (E₀) G]
  [LieGroup (𝓘(ℝ, E₀)) ∞ G] [T2Space G]
local notation "𝓘ₙ" => 𝓘(ℝ, E₀)
local notation "E" => E₀
local notation "C" => RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)
local notation "S" => MonoidHom.range (centralAxesHom (G := G) (E₀ := E₀))

instance centralAxesHom_range_normal : (S).Normal where
  conj_mem a ha b := by
    have hc := Subgroup.mem_center_iff.mp (centralAxesHom_range_le_center ha) b
    simpa only [hc, mul_inv_cancel_right] using ha

lemma central_quotient_t2Space : T2Space (G ⧸ S) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘ₙ ∞
  let : IsClosed (S : Set G) := centralAxesHom_range_isClosed
  infer_instance

 

theorem exists_central_quotient_lieChart (W : Submodule ℝ E) (hWC : IsCompl W C) :
    ∃ cs : ChartedSpace W (G ⧸ S),
      letI := cs
      LieGroup 𝓘(ℝ,W) ∞ (G ⧸ S) ∧
      ContMDiff 𝓘ₙ 𝓘(ℝ,W) ∞ (QuotientGroup.mk' S) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘ₙ ∞
  obtain ⟨q,hq0,hq,hcoord⟩ := exists_central_quotient_smoothChart (G := G) W hWC
  have hqzero : q 0 = (1 : G ⧸ S) := by simp only [hq, Function.comp_apply, subspaceAxes_zero, QuotientGroup.mk_one]
  have h1 : (1 : G ⧸ S) ∈ q.target := hqzero ▸ q.map_source hq0
  let cs := RawQuotientLie.quotientChartedSpace q h1
  refine ⟨cs,?_⟩
  constructor
  · exact RawQuotientLie.quotient_lieGroup (QuotientGroup.mk' S) (QuotientGroup.mk'_surjective S)
      QuotientGroup.continuous_mk (subspaceAxes W) (subspaceAxes_contMDiff W) q h1 hq hcoord
  · exact RawQuotientLie.quotient_projection_smooth q h1 (QuotientGroup.mk' S)
      QuotientGroup.continuous_mk hcoord

end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀] {G : Type} [Group G] [TopologicalSpace G]
  [ChartedSpace (E₀) G]
  [LieGroup (𝓘(ℝ, E₀)) ∞ G] [T2Space G]
local notation "𝓘ₙ" => 𝓘(ℝ, E₀)
local notation "E" => E₀
local notation "C" => RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)
local notation "S" => MonoidHom.range (centralAxesHom (G := G) (E₀ := E₀))

lemma centralAxesHom_range_pathConnectedSpace : PathConnectedSpace S := by
  let f : C → S := fun v => ⟨subspaceAxes C v, ⟨Multiplicative.ofAdd v,rfl⟩⟩
  have hf : Continuous f := (subspaceAxes_contMDiff (G := G) C).continuous.subtype_mk _
  have hon : Surjective f := by
    rintro ⟨g,⟨v,rfl⟩⟩
    exact ⟨v.toAdd,rfl⟩
  exact hon.pathConnectedSpace hf

 

theorem central_quotient_simplyConnected [SimplyConnectedSpace G] : SimplyConnectedSpace (G ⧸ S) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘ₙ ∞
  let : PathConnectedSpace (S) := centralAxesHom_range_pathConnectedSpace
  let : PathConnectedSpace (QuotientGroup.mk' S).ker := by rw [QuotientGroup.ker_mk']; infer_instance
  obtain ⟨W,hCW⟩ := Submodule.exists_isCompl C
  obtain ⟨q,hq0,hq,_⟩ := exists_central_quotient_smoothChart (G := G) W hCW.symm
  have hqzero : q 0 = (1 : G ⧸ S) := by simp only [hq, Function.comp_apply, subspaceAxes_zero, QuotientGroup.mk_one]
  have h1 : (1 : G ⧸ S) ∈ q.target := hqzero ▸ q.map_source hq0
  apply RawQuotientTopology.simplyConnected_quotient (QuotientGroup.mk' S)
    (QuotientGroup.mk'_surjective S) QuotientGroup.continuous_mk
  exact RawQuotientTopology.local_sections_of_chart (QuotientGroup.mk' S)
    (QuotientGroup.mk'_surjective S) (subspaceAxes W) (subspaceAxes_contMDiff W).continuous q h1 hq

end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G]
  [ChartedSpace E₀ G] [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]
local notation "C" => RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)
local notation "S" => MonoidHom.range (centralAxesHom (G := G) (E₀ := E₀))
local notation "f" => MonoidHom.rangeRestrict (centralAxesHom (G := G) (E₀ := E₀))

lemma centralAxes_range_continuous : Continuous f := centralAxesHom_continuous.subtype_mk _

lemma centralAxes_range_isOpenMap : IsOpenMap f := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E₀) ∞
  let : LocallyCompactSpace G := ChartedSpace.locallyCompactSpace E₀ G
  let : LocallyCompactSpace S := centralAxesHom_range_isClosed.locallyCompactSpace
  exact (f).isOpenMap_of_sigmaCompact (MonoidHom.rangeRestrict_surjective _)
    centralAxes_range_continuous

lemma centralAxes_range_ker_discrete : IsDiscrete ((f).ker : Set (Multiplicative C)) := by
  rw [SetLike.isDiscrete_iff_discreteTopology, discreteTopology_iff_isOpen_singleton_one]
  obtain ⟨W,hCW⟩ := Submodule.exists_isCompl C
  obtain ⟨e,h0,he⟩ := exists_productSlice_localChart (G := G) W C hCW.symm
  have hc : Continuous (fun x : (f).ker => ((0 : W), x.val.toAdd)) :=
    continuous_const.prodMk continuous_subtype_val
  convert e.open_source.preimage hc using 1
  ext x
  change x = 1 ↔ ((0 : W), x.val.toAdd) ∈ e.source
  constructor
  · rintro rfl
    exact h0
  · intro hx
    apply Subtype.ext
    change x.val.toAdd = 0
    have hp : ((0 : W),x.val.toAdd) = 0 := by
      apply e.injOn hx h0
      rw [he hx,he h0,productSlice_zero]
      simp only [productSlice, subspaceAxes_zero, one_mul]
      exact congrArg Subtype.val x.property
    exact congrArg Prod.snd hp

lemma centralAxes_range_covering : IsCoveringMap f :=
  ((centralAxes_range_isOpenMap).isQuotientMap centralAxes_range_continuous
    (MonoidHom.rangeRestrict_surjective _)).isQuotientCoveringMap_of_isDiscrete_ker_monoidHom
      centralAxes_range_ker_discrete |>.isCoveringMap

lemma centralAxes_range_locallyPathConnected : LocallyPathConnectedSpace S := by
  let : LocallyPathConnectedSpace (Multiplicative C) := inferInstanceAs (LocallyPathConnectedSpace C)
  exact ((centralAxes_range_isOpenMap).isQuotientMap centralAxes_range_continuous
    (MonoidHom.rangeRestrict_surjective _)).locallyPathConnectedSpace

 

lemma centralAxes_injective [SimplyConnectedSpace S] : Injective f := by
  let : LocallyPathConnectedSpace S := centralAxes_range_locallyPathConnected
  let : PreconnectedSpace (Multiplicative C) := inferInstanceAs (PreconnectedSpace C)
  have hcov := centralAxes_range_covering (G := G) (E₀ := E₀)
  obtain ⟨F,⟨hF1,hF⟩,_⟩ := hcov.existsUnique_continuousMap_lifts
    (ContinuousMap.id S) (1 : S) 1 (map_one f)
  have hleft : (F : S → Multiplicative C) ∘ f = id := by
    apply hcov.eq_of_comp_eq (F.continuous.comp centralAxes_range_continuous) continuous_id
      ?_ (1 : Multiplicative C) ?_
    · funext x
      exact congrFun hF (f x)
    · simpa only [Function.comp_apply,map_one,id_eq] using hF1
  exact (show LeftInverse F f from fun x => congrFun hleft x).injective

end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]
local notation "C" => RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)
local notation "S" => MonoidHom.range (centralAxesHom (G := G) (E₀ := E₀))

 

theorem exists_central_quotient_submersion (W : Submodule ℝ E₀) (hWC : IsCompl W C) :
    ∃ cs : ChartedSpace W (G ⧸ S),
      letI := cs
      LieGroup 𝓘(ℝ,W) ∞ (G ⧸ S) ∧
      ContMDiff 𝓘(ℝ,E₀) 𝓘(ℝ,W) ∞ (QuotientGroup.mk' S) ∧
      Surjective (mfderiv 𝓘(ℝ,E₀) 𝓘(ℝ,W) (QuotientGroup.mk' S) 1 : E₀ →L[ℝ] W) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E₀) ∞
  obtain ⟨q,hq0,hq,hcoord⟩ := exists_central_quotient_smoothChart (G := G) W hWC
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

 

def centralHomeomorph [SimplyConnectedSpace S] : C ≃ₜ S :=
  (Equiv.ofBijective (fun v : C => (centralAxesHom (G := G) (E₀ := E₀)).rangeRestrict
      (Multiplicative.ofAdd v))
    ⟨fun _ _ h => centralAxes_injective (G := G) (E₀ := E₀) h,
      fun z => by
        obtain ⟨v,rfl⟩ := MonoidHom.rangeRestrict_surjective (centralAxesHom (G := G) (E₀ := E₀)) z
        exact ⟨v.toAdd,rfl⟩⟩).toHomeomorphOfContinuousOpen
      centralAxes_range_continuous centralAxes_range_isOpenMap

end RawLieIntegration
end

end OAI
