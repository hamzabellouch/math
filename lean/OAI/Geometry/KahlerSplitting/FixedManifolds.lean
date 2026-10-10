import OAI.Geometry.KahlerSplitting.RetractCharts

namespace OAI

section

noncomputable section
open Set Filter Topology Metric
open scoped Manifold ContDiff
namespace UniversalCoverSplitting
namespace RetractChart
variable {n r s : ℕ} {Z : ComplexManifold n} {Q : Z.Carrier → Z.Carrier}

lemma differentiableOn_transition (e d : RetractChart Z Q r s) :
    DifferentiableOn ℂ (e.fixedChart.symm.trans d.fixedChart)
      (e.fixedChart.symm.trans d.fixedChart).source := by
  intro a ha
  have hat : (a,(0 : Model s)) ∈ e.chart.target := by
    rw [e.product_range]; exact ⟨ha.1,mem_ball_self e.radius_pos⟩
  have had : e.chart.symm (a,0) ∈ d.chart.source := by
    have hh := ha.2
    change (e.fixedInv a).val ∈ d.chart.source at hh
    rwa [e.fixedInv_val ha.1] at hh
  have he := (e.inverse_holomorphic _ hat).mdifferentiableAt (e.chart.open_target.mem_nhds hat)
  have hd := (d.holomorphic _ had).mdifferentiableAt (d.chart.open_source.mem_nhds had)
  have hins : MDifferentiableAt (model r) 𝓘(ℂ,Model r × Model s) (fun a : Model r ↦ (a,(0 : Model s))) a :=
    mdifferentiableAt_iff_differentiableAt.mpr (by fun_prop)
  have hdcomp := (mdifferentiableAt_iff_differentiableAt.mp ((hd.comp _ he).comp a hins)).fst
  apply DifferentiableAt.differentiableWithinAt
  apply hdcomp.congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds ha.1] with b hb
  change (d.chart (e.fixedInv b).val).1=(d.chart (e.chart.symm (b,0))).1
  rw [e.fixedInv_val hb]

lemma contDiffOn_transition (e d : RetractChart Z Q r s) :
    ContDiffOn ℂ ∞ (e.fixedChart.symm.trans d.fixedChart)
      (e.fixedChart.symm.trans d.fixedChart).source :=
  finite_holomorphic_contDiffOn (e.fixedChart.symm.trans d.fixedChart).open_source
    (differentiableOn_transition e d)

variable (c : Fixed Q → RetractChart Z Q r s)
    (hc : ∀ x, x.val ∈ (c x).chart.source)

@[instance_reducible] def fixedChartedSpace : ChartedSpace (Model r) (Fixed Q) where
  atlas := Set.range (fun x ↦ (c x).fixedChart)
  chartAt := fun x ↦ (c x).fixedChart
  mem_chart_source := hc
  chart_mem_atlas := fun x ↦ ⟨x,rfl⟩

lemma fixedIsManifold : letI := fixedChartedSpace c hc;
    IsManifold (model r) ∞ (Fixed Q) := by
  let := fixedChartedSpace c hc
  apply isManifold_of_contDiffOn
  intro e d he hd
  obtain ⟨x,rfl⟩ := he
  obtain ⟨y,rfl⟩ := hd
  simpa only [model,modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.comp_id,Function.id_comp,preimage_id,range_id,inter_univ] using
    contDiffOn_transition (c x) (c y)

def fixedManifold : ComplexManifold r where
  Carrier := Fixed Q
  topology := inferInstance
  hausdorff := inferInstance
  secondCountable := @TopologicalSpace.Subtype.secondCountableTopology Z.Carrier Z.topology {z | Q z=z} Z.secondCountable
  charted := fixedChartedSpace c hc
  complexSmooth := fixedIsManifold c hc

end RetractChart
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology Metric
open scoped Manifold
namespace UniversalCoverSplitting
namespace RetractChart
variable {n r s : ℕ} {Z : ComplexManifold n} {Q : Z.Carrier → Z.Carrier}
variable (c : Fixed Q → RetractChart Z Q r s) (hc : ∀ x, x.val ∈ (c x).chart.source)

lemma fixed_inclusion_holomorphic :
    MDifferentiable (model r) (model n) (show (fixedManifold c hc).Carrier → Z.Carrier from Subtype.val) := by
  intro x
  let Y := fixedManifold c hc
  let e := c x
  have hxs : x.val ∈ e.chart.source := hc x
  have hxt : (e.chart x.val).1 ∈ ball 0 e.radius := (e.product_range ▸ e.chart.map_source hxs).1
  rw [mdifferentiableAt_iff_source_of_mem_source (mem_chart_source (Model r) x)]
  simp only [model,modelWithCornersSelf_coe,range_id,mdifferentiableWithinAt_univ]
  have hat : ((e.chart x.val).1,(0 : Model s)) ∈ e.chart.target := by
    rw [e.product_range]; exact ⟨hxt,mem_ball_self e.radius_pos⟩
  have he := (e.inverse_holomorphic _ hat).mdifferentiableAt (e.chart.open_target.mem_nhds hat)
  have hins : MDifferentiableAt (model r) 𝓘(ℂ,Model r × Model s)
      (fun a : Model r ↦ (a,(0 : Model s))) (e.chart x.val).1 :=
    mdifferentiableAt_iff_differentiableAt.mpr (by fun_prop)
  change MDifferentiableAt (model r) (model n) (fun a ↦ (e.fixedInv a).val) (e.chart x.val).1
  apply (he.comp (e.chart x.val).1 hins).congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds hxt] with a ha
  change (e.fixedInv a).val=e.chart.symm (a,0)
  exact e.fixedInv_val ha

lemma fixed_projection_holomorphic (hQ : MDifferentiable (model n) (model n) Q)
    (hid : ∀ z, Q (Q z)=Q z) :
    MDifferentiable (model n) (model r)
      (show Z.Carrier → (fixedManifold c hc).Carrier from fun z ↦ ⟨Q z,hid z⟩) := by
  let q : Z.Carrier → (fixedManifold c hc).Carrier := fun z ↦ ⟨Q z,hid z⟩
  have hqc : Continuous q := hQ.continuous.subtype_mk _
  intro z
  rw [mdifferentiableAt_iff_target]
  refine ⟨hqc.continuousAt,?_⟩
  let e := c (q z)
  have hmem : Q z ∈ e.chart.source := hc (q z)
  have he := (e.holomorphic _ hmem).mdifferentiableAt (e.chart.open_source.mem_nhds hmem)
  change MDifferentiableAt (model n) (model r) (fun y ↦ (e.chart (Q y)).1) z
  exact (mdifferentiableAt_iff_differentiableAt.mpr differentiableAt_fst).comp z (he.comp z (hQ z))

end RetractChart
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology Metric
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s k : ℕ} {X Z : ComplexManifold n} {Y : ComplexManifold k}
    {S : HolomorphicSplitting X r s} {π : OrdinaryUniversalCover X Z}

lemma CoverProductChart.surjective_derivative (e : CoverProductChart π S)
    {z : Z.Carrier} (hz : z ∈ e.chart.source) :
    Function.Surjective (mfderiv (model n) 𝓘(ℂ,Model r × Model s) e.chart z) := by
  have ht := e.chart.map_source hz
  have he := e.holomorphic.mdifferentiableAt (e.chart.open_source.mem_nhds hz)
  have hi := e.inverse_holomorphic.mdifferentiableAt (e.chart.open_target.mem_nhds ht)
  have H := mfderiv_comp (I := 𝓘(ℂ,Model r × Model s)) (I' := model n)
    (I'' := 𝓘(ℂ,Model r × Model s)) (e.chart z) (by simpa only [e.chart.left_inv hz] using he) hi
  have hid : e.chart ∘ e.chart.symm =ᶠ[𝓝 (e.chart z)] id := by
    filter_upwards [e.chart.open_target.mem_nhds ht] with p hp
    exact e.chart.right_inv hp
  rw [hid.mfderiv_eq,mfderiv_id,e.chart.left_inv hz] at H
  intro v
  refine ⟨mfderiv 𝓘(ℂ,Model r × Model s) (model n) e.chart.symm (e.chart z) v,?_⟩
  exact (congrArg (fun L : (Model r × Model s) →L[ℂ] (Model r × Model s) ↦ L v) H).symm

lemma CoverProductChart.surjective_first_derivative (e : CoverProductChart π S)
    {z : Z.Carrier} (hz : z ∈ e.chart.source) :
    Function.Surjective (mfderiv (model n) (model r) (fun w ↦ (e.chart w).1) z) := by
  have he := e.holomorphic.mdifferentiableAt (e.chart.open_source.mem_nhds hz)
  have hf : MDifferentiableAt 𝓘(ℂ,Model r × Model s) (model r) Prod.fst (e.chart z) :=
    mdifferentiableAt_iff_differentiableAt.mpr differentiableAt_fst
  have H := mfderiv_comp (I := model n) (I' := 𝓘(ℂ,Model r × Model s))
    (I'' := model r) z hf he
  rw [mfderiv_eq_fderiv,hasFDerivAt_fst.fderiv] at H
  change mfderiv (model n) (model r) (fun w ↦ (e.chart w).1) z = _ at H
  rw [H]
  intro a
  obtain ⟨v,hv⟩ := e.surjective_derivative hz (a,0)
  refine ⟨v,?_⟩
  change (mfderiv (model n) 𝓘(ℂ,Model r × Model s) e.chart z v).1=a
  rw [hv]

lemma CoverProductChart.surjective_factor_iff (e : CoverProductChart π S)
    {f : Z.Carrier → Y.Carrier} (hf : MDifferentiable (model n) (model k) f)
    (hfact : EqOn f (fun z ↦ f (e.chart.symm ((e.chart z).1,0))) e.chart.source)
    {z : Z.Carrier} (hz : z ∈ e.chart.source) :
    Function.Surjective (mfderiv (model n) (model k) f z) ↔
      Function.Surjective (mfderiv (model r) (model k)
        (fun a ↦ f (e.chart.symm (a,(0 : Model s)))) (e.chart z).1) := by
  let h : Model r → Y.Carrier := fun a ↦ f (e.chart.symm (a,0))
  let a := (e.chart z).1
  have ht := e.chart.map_source hz
  rw [e.product_range] at ht
  have hta : (a,(0 : Model s)) ∈ e.chart.target := by
    rw [e.product_range]; exact ⟨ht.1,mem_ball_self e.radius_pos⟩
  have hi := e.inverse_holomorphic.mdifferentiableAt (e.chart.open_target.mem_nhds hta)
  have hin : MDifferentiableAt (model r) 𝓘(ℂ,Model r × Model s)
      (fun a : Model r ↦ (a,(0 : Model s))) a :=
    mdifferentiableAt_iff_differentiableAt.mpr (by fun_prop)
  have hh : MDifferentiableAt (model r) (model k) h a :=
    (hf (e.chart.symm (a,0))).comp a (hi.comp a hin)
  have he := e.holomorphic.mdifferentiableAt (e.chart.open_source.mem_nhds hz)
  have hfirst : MDifferentiableAt (model n) (model r) (fun w ↦ (e.chart w).1) z :=
    (mdifferentiableAt_iff_differentiableAt.mpr differentiableAt_fst).comp z he
  have H := mfderiv_comp (I := model n) (I' := model r) (I'' := model k) z hh hfirst
  have heq : f =ᶠ[𝓝 z] h ∘ (fun w ↦ (e.chart w).1) := by
    filter_upwards [e.chart.open_source.mem_nhds hz] with w hw
    exact hfact hw
  have hderiv : mfderiv (model n) (model k) f z =
      mfderiv (model n) (model k) (h ∘ fun w ↦ (e.chart w).1) z := heq.mfderiv_eq
  rw [hderiv, H]
  exact ⟨fun hsur ↦ fun b ↦ by
    obtain ⟨v,hv⟩ := hsur b
    exact ⟨mfderiv (model n) (model r) (fun w ↦ (e.chart w).1) z v,hv⟩,
    fun hsur ↦ hsur.comp (e.surjective_first_derivative hz)⟩

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
namespace FirstGerm
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z} {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}

lemma GlobalProjection.vertical_reach [CompactSpace X.Carrier] (g : KahlerMetric X)
    (Q : GlobalProjection π o h₁ h₂) (z : Z.Carrier) :
    ∃ β : C(I,Z.Carrier), β 0=Q.toFun z ∧ β 1=z ∧
      ProductBoxTopology.IsVertical (splittingAtlas S) (π.projection ∘ β) := by
  let := π.simplyConnected
  let γ := PathConnectedSpace.somePath o z
  obtain ⟨R,hR,hdiag⟩ := path_diagonal g h₁ h₂ (π.covering.continuous.comp γ.continuous)
  have hR0 : π.projection o=R (0,0) := by
    rw [hdiag]
    change π.projection o=π.projection (γ 0)
    rw [γ.source]
  let : LocallyPathConnectedSpace I := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  let : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0,by simp⟩
  obtain ⟨L,⟨hL0,hLb⟩,_⟩ := π.covering.existsUnique_continuousMap_lifts ⟨R,hR.1⟩ (0,0) o hR0
  have hcont : Continuous (fun t : I ↦ L (t,t)) := L.continuous.comp (continuous_id.prodMk continuous_id)
  have hLdiag : (fun t : I ↦ L (t,t))=γ := by
    refine π.covering.isSeparatedMap.eq_of_comp_eq π.covering.isLocalHomeomorph.isLocallyInjective
      hcont γ.continuous ?_ 0 ?_
    · ext t
      exact (congrFun hLb (t,t)).trans (hdiag t)
    · exact hL0.trans γ.source.symm
  let α : C(I,Z.Carrier) := ⟨fun t ↦ L (t,0),L.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hα : ProductBoxTopology.IsHorizontal (splittingAtlas S) (π.projection ∘ α) := by
    have he : π.projection ∘ α=(fun t ↦ R (t,0)) := by ext t; exact congrFun hLb (t,0)
    rw [he]; exact hR.horizontal 0
  have hQα := Q.horizontal_fixed α.continuous hL0 hα 1
  have hv : ProductBoxTopology.IsVertical (splittingAtlas S) (fun t ↦ π.projection (L (1,t))) := by
    have he : (fun t ↦ π.projection (L (1,t)))=(fun t ↦ R (1,t)) := by
      ext t; exact congrFun hLb (1,t)
    rw [he]; exact hR.vertical 1
  have hQv := Q.vertical_constant (L.continuous.comp (continuous_const.prodMk continuous_id)) hv 1
  have hz : L (1,1)=z := (congrFun hLdiag 1).trans γ.target
  change Q.toFun (L (1,1))=Q.toFun (L (1,0)) at hQv
  rw [hz] at hQv
  exact ⟨⟨fun t ↦ L (1,t),L.continuous.comp (continuous_const.prodMk continuous_id)⟩,
    (hQv.trans hQα).symm,hz,hv⟩

end FirstGerm
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s k : ℕ} {X Z : ComplexManifold n} {Y : ComplexManifold k}
    {S : HolomorphicSplitting X r s} {π : OrdinaryUniversalCover X Z}

lemma surjective_mfderiv_of_rightInverse {f : Z.Carrier → Y.Carrier} {j : Y.Carrier → Z.Carrier}
    (hf : MDifferentiable (model n) (model k) f) (hj : MDifferentiable (model k) (model n) j)
    (hij : ∀ y, f (j y)=y) (y : Y.Carrier) :
    Function.Surjective (mfderiv (model n) (model k) f (j y)) := by
  have H := mfderiv_comp (I := model k) (I' := model n) (I'' := model k) y (hf _) (hj y)
  have heq : f ∘ j=id := funext hij
  rw [heq,mfderiv_id] at H
  intro v
  refine ⟨mfderiv (model k) (model n) j y v,?_⟩
  exact (congrArg (fun L : Model k →L[ℂ] Model k ↦ L v) H).symm

open scoped unitInterval

lemma surjective_along_vertical
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    {f : Z.Carrier → Y.Carrier} (hf : MDifferentiable (model n) (model k) f)
    (hfact : ∀ e : CoverProductChart π S,
      EqOn f (fun z ↦ f (e.chart.symm ((e.chart z).1,0))) e.chart.source)
    {β : I → Z.Carrier} (hc : Continuous β)
    (hv : ProductBoxTopology.IsVertical (splittingAtlas S) (π.projection ∘ β)) :
    ∀ t, Function.Surjective (mfderiv (model n) (model k) f (β t)) ↔
      Function.Surjective (mfderiv (model n) (model k) f (β 0)) := by
  have hl : IsLocallyConstant (fun t ↦ Function.Surjective (mfderiv (model n) (model k) f (β t))) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro t
    obtain ⟨e,he,_⟩ := exists_coverProductChart π S h₁ h₂ (β t)
    let W := (π.projection ∘ β) ⁻¹' e.downstairs.chart.source
    have htW : t ∈ W := e.maps he
    have hW : IsOpen W := e.downstairs.chart.open_source.preimage hv.1
    have hlc := (hv.2 e.downstairs.chart ⟨e.downstairs,rfl⟩).eventually_eq (⟨t,htW⟩ : W)
    obtain ⟨V,hV,hsub⟩ := (mem_nhds_subtype W ⟨t,htW⟩ _).mp hlc
    filter_upwards [hV,hW.mem_nhds htW,hc.continuousAt (e.chart.open_source.mem_nhds he)] with u huV huW hue
    apply propext
    rw [e.surjective_factor_iff hf (hfact e) hue,e.surjective_factor_iff hf (hfact e) he]
    have hh := hsub (show (⟨u,huW⟩ : W) ∈ Subtype.val ⁻¹' V from huV)
    change (e.downstairs.chart (π.projection (β u))).1=(e.downstairs.chart (π.projection (β t))).1 at hh
    rw [e.coordinates _ hue,e.coordinates _ he,hh]
  intro t
  exact (hl.apply_eq_of_preconnectedSpace t 0).to_iff

namespace FirstGerm
variable {o : Z.Carrier} {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}

lemma GlobalProjection.submersion [CompactSpace X.Carrier] (g : KahlerMetric X)
    (Q : GlobalProjection π o h₁ h₂)
    (c : RetractChart.Fixed Q.toFun → RetractChart Z Q.toFun r s)
    (hc : ∀ x, x.val ∈ (c x).chart.source) (z : Z.Carrier) :
    Function.Surjective (mfderiv (model n) (model r)
      (show Z.Carrier → (RetractChart.fixedManifold c hc).Carrier from
        fun w ↦ ⟨Q.toFun w,Q.idempotent g w⟩) z) := by
  let Y := RetractChart.fixedManifold c hc
  let q : Z.Carrier → Y.Carrier := fun w ↦ ⟨Q.toFun w,Q.idempotent g w⟩
  have hq := RetractChart.fixed_projection_holomorphic c hc Q.holomorphic (Q.idempotent g)
  have hj := RetractChart.fixed_inclusion_holomorphic c hc
  have hri : ∀ y : Y.Carrier, q y.val=y := fun y ↦ Subtype.ext y.property
  have hs := surjective_mfderiv_of_rightInverse hq hj hri (q z)
  obtain ⟨β,hβ0,hβ1,hβ⟩ := Q.vertical_reach g z
  have hfact (e : CoverProductChart π S) :
      EqOn q (fun w ↦ q (e.chart.symm ((e.chart w).1,0))) e.chart.source := by
    intro w hw
    exact Subtype.ext (Q.chart_factor e hw)
  have H := surjective_along_vertical h₁ h₂ hq hfact β.continuous hβ 1
  rw [hβ0,hβ1] at H
  exact H.mpr hs

end FirstGerm
end UniversalCoverSplitting
end
end

end OAI
