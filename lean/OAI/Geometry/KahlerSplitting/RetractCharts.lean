import OAI.Geometry.KahlerSplitting.ProjectionImages

namespace OAI

section

noncomputable section
open Set Filter Topology Metric
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {Z : ComplexManifold n}

structure RetractChart (Z : ComplexManifold n) (Q : Z.Carrier → Z.Carrier) (r s : ℕ) where
  chart : OpenPartialHomeomorph Z.Carrier (Model r × Model s)
  radius : ℝ
  radius_pos : 0 < radius
  product_range : chart.target=ball 0 radius ×ˢ ball 0 radius
  holomorphic : MDifferentiableOn (model n) 𝓘(ℂ,Model r × Model s) chart chart.source
  inverse_holomorphic : MDifferentiableOn 𝓘(ℂ,Model r × Model s) (model n) chart.symm chart.target
  maps : MapsTo Q chart.source chart.source
  projects : ∀ z ∈ chart.source, chart (Q z)=((chart z).1,0)

lemma restrict_retract_chart {Q : Z.Carrier → Z.Carrier}
    (e : OpenPartialHomeomorph Z.Carrier (Model r × Model s))
    (he : MDifferentiableOn (model n) 𝓘(ℂ,Model r × Model s) e e.source)
    (hei : MDifferentiableOn 𝓘(ℂ,Model r × Model s) (model n) e.symm e.target)
    {x : Z.Carrier} (hx : x ∈ e.source) (h0 : e x=0)
    (hl : ∀ᶠ y in 𝓝 x, Q y ∈ e.source ∧ e (Q y)=((e y).1,0)) :
    ∃ b : RetractChart Z Q r s, x ∈ b.chart.source ∧ b.chart x=0 := by
  obtain ⟨N,hN,hNo,hxN⟩ := mem_nhds_iff.mp hl
  have h0t : (0 : Model r × Model s) ∈ e.target := h0 ▸ e.map_source hx
  have he0 : e.symm 0=x := by rw [←h0,e.left_inv hx]
  have hNb : e.target ∩ e.symm ⁻¹' N ∈ 𝓝 (0 : Model r × Model s) :=
    inter_mem (e.open_target.mem_nhds h0t) ((e.symm.continuousAt h0t) (by simpa [he0] using hNo.mem_nhds hxN))
  obtain ⟨ε,hε,hεN⟩ := Metric.mem_nhds_iff.mp hNb
  let V : Set (Model r × Model s) := ball 0 ε ×ˢ ball 0 ε
  have hVN : V ⊆ e.target ∩ e.symm ⁻¹' N := by
    rw [show V=ball (0 : Model r × Model s) ε from ball_prod_same _ _ _]
    exact hεN
  let b := (e.symm.restrOpen V (isOpen_ball.prod isOpen_ball)).symm
  have hbtarget : b.target=V := inter_eq_right.mpr (fun _ hy ↦ (hVN hy).1)
  have hxb : x ∈ b.source := by
    change x ∈ e.source ∧ e x ∈ V
    exact ⟨hx,by rw [h0]; exact ⟨mem_ball_self hε,mem_ball_self hε⟩⟩
  have hbproj (y : Z.Carrier) (hy : y ∈ b.source) : Q y ∈ e.source ∧ e (Q y)=((e y).1,0) := by
    apply hN
    have hh := (hVN hy.2).2
    change e.symm (e y) ∈ N at hh
    simpa only [e.left_inv hy.1] using hh
  have hbmaps : MapsTo Q b.source b.source := by
    intro y hy
    refine ⟨(hbproj y hy).1,?_⟩
    change e (Q y) ∈ V
    rw [(hbproj y hy).2]
    exact ⟨hy.2.1,mem_ball_self hε⟩
  exact ⟨⟨b,ε,hε,hbtarget,he.mono inter_subset_left,hei.mono inter_subset_left,
    hbmaps,fun y hy ↦ (hbproj y hy).2⟩,hxb,h0⟩

namespace RetractChart
variable {Q : Z.Carrier → Z.Carrier} (e : RetractChart Z Q r s)
abbrev Fixed (Q : Z.Carrier → Z.Carrier) := {z : Z.Carrier // Q z=z}

lemma fixed_iff {z : Z.Carrier} (hz : z ∈ e.chart.source) :
    Q z=z ↔ (e.chart z).2=0 := by
  constructor
  · intro h
    have hh := congrArg Prod.snd (e.projects z hz)
    simpa only [h] using hh
  · intro h
    apply e.chart.injOn (e.maps hz) hz
    rw [e.projects z hz,←h]

lemma fixed_inverse {a : Model r} (ha : a ∈ ball 0 e.radius) :
    Q (e.chart.symm (a,0))=e.chart.symm (a,0) := by
  have hat : (a,(0 : Model s)) ∈ e.chart.target := by
    rw [e.product_range]; exact ⟨ha,mem_ball_self e.radius_pos⟩
  apply (e.fixed_iff (e.chart.map_target hat)).mpr
  rw [e.chart.right_inv hat]

def fixedInv (a : Model r) : Fixed Q := by
  classical
  exact if h : a ∈ ball 0 e.radius then ⟨e.chart.symm (a,0),e.fixed_inverse h⟩
  else ⟨e.chart.symm (0,0),e.fixed_inverse (mem_ball_self e.radius_pos)⟩

lemma fixedInv_val {a : Model r} (ha : a ∈ ball 0 e.radius) :
    (e.fixedInv a).val=e.chart.symm (a,0) := by simp only [fixedInv,dite_eq_left ha]

lemma continuousOn_fixedInv : ContinuousOn e.fixedInv (ball 0 e.radius) := by
  apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
  apply (e.chart.symm.continuousOn.comp (show Continuous (fun a : Model r ↦ (a,(0 : Model s))) from by fun_prop).continuousOn
    (fun a ha ↦ by change (a,(0 : Model s)) ∈ e.chart.target; rw [e.product_range]; exact ⟨ha,mem_ball_self e.radius_pos⟩)).congr
  exact fun a ha ↦ e.fixedInv_val ha

def fixedChart : OpenPartialHomeomorph (Fixed Q) (Model r) where
  toFun := fun z ↦ (e.chart z.val).1
  invFun := e.fixedInv
  source := Subtype.val ⁻¹' e.chart.source
  target := ball 0 e.radius
  map_source' := fun z hz ↦ (e.product_range ▸ e.chart.map_source hz).1
  map_target' := fun a ha ↦ by
    change (e.fixedInv a).val ∈ e.chart.source
    rw [e.fixedInv_val ha]
    apply e.chart.map_target
    rw [e.product_range]; exact ⟨ha,mem_ball_self e.radius_pos⟩
  left_inv' := fun z hz ↦ by
    apply Subtype.ext
    rw [e.fixedInv_val ((e.product_range ▸ e.chart.map_source hz).1)]
    have hh := (e.fixed_iff hz).mp z.property
    rw [←hh,Prod.eta,e.chart.left_inv hz]
  right_inv' := fun a ha ↦ by
    rw [e.fixedInv_val ha,e.chart.right_inv (by
      rw [e.product_range]; exact ⟨ha,mem_ball_self e.radius_pos⟩)]
  open_source := e.chart.open_source.preimage continuous_subtype_val
  open_target := isOpen_ball
  continuousOn_toFun := (e.chart.continuousOn.comp continuous_subtype_val.continuousOn (fun _ h ↦ h)).fst
  continuousOn_invFun := e.continuousOn_fixedInv

end RetractChart
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology Metric
open scoped Manifold
namespace UniversalCoverSplitting
namespace FirstGerm
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z} {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}

lemma GlobalProjection.exists_retractChart [CompactSpace X.Carrier] (g : KahlerMetric X)
    (Q : GlobalProjection π o h₁ h₂) {x : Z.Carrier} (hfix : Q.toFun x=x) :
    ∃ e : RetractChart Z Q.toFun r s, x ∈ e.chart.source ∧ e.chart x=0 := by
  obtain ⟨c,hxc,hc,hcd,hcdi⟩ := π.liftedComplexStructure x
  obtain ⟨d,hxd,hd0⟩ := exists_splittingChart S h₁ h₂ (π.projection x)
  let e := c.trans d.chart
  have hxe : x ∈ e.source := ⟨hxc,by change c x ∈ d.chart.source; rw [hc x hxc]; exact hxd⟩
  have he0 : e x=0 := by change d.chart (c x)=0; rw [hc x hxc,hd0]
  have he : MDifferentiableOn (model n) 𝓘(ℂ,Model r × Model s) e e.source :=
    d.holomorphic.comp (hcd.mono inter_subset_left) (fun _ hy ↦ hy.2)
  have hei : MDifferentiableOn 𝓘(ℂ,Model r × Model s) (model n) e.symm e.target :=
    hcdi.comp (d.inverse_holomorphic.mono inter_subset_left) (fun _ hy ↦ hy.2)
  have hlocal := Q.image_local g x d (by rwa [hfix])
  rw [hfix,hd0] at hlocal
  have hQx : Q.toFun x ∈ e.source := by rwa [hfix]
  apply restrict_retract_chart e he hei hxe he0
  filter_upwards [e.open_source.mem_nhds hxe,
    Q.holomorphic.continuous.continuousAt (e.open_source.mem_nhds hQx),hlocal] with y hy hQy hyeq
  refine ⟨hQy,?_⟩
  change d.chart (c (Q.toFun y))=((d.chart (c y)).1,0)
  rw [hc _ hQy.1,hc _ hy.1]
  have hyπ : π.projection y ∈ d.chart.source := by rw [←hc _ hy.1]; exact hy.2
  change π.projection (Q.toFun y)=d.firstProjection 0 (π.projection y) at hyeq
  rw [hyeq,d.firstProjection_coordinates (mem_ball_self d.radius_pos) hyπ]

end FirstGerm
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology Metric
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}

structure CoverProductChart (π : OrdinaryUniversalCover X Z) (S : HolomorphicSplitting X r s) where
  chart : OpenPartialHomeomorph Z.Carrier (Model r × Model s)
  radius : ℝ
  radius_pos : 0 < radius
  product_range : chart.target=ball 0 radius ×ˢ ball 0 radius
  holomorphic : MDifferentiableOn (model n) 𝓘(ℂ,Model r × Model s) chart chart.source
  inverse_holomorphic : MDifferentiableOn 𝓘(ℂ,Model r × Model s) (model n) chart.symm chart.target
  downstairs : SplittingChart S
  maps : MapsTo π.projection chart.source downstairs.chart.source
  coordinates : ∀ z ∈ chart.source, chart z=downstairs.chart (π.projection z)

lemma exists_coverProductChart (π : OrdinaryUniversalCover X Z) (S : HolomorphicSplitting X r s)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S)) (x : Z.Carrier) :
    ∃ e : CoverProductChart π S, x ∈ e.chart.source ∧ e.chart x=0 := by
  obtain ⟨c,hxc,hc,hcd,hcdi⟩ := π.liftedComplexStructure x
  obtain ⟨d,hxd,hd0⟩ := exists_splittingChart S h₁ h₂ (π.projection x)
  let e := c.trans d.chart
  have hxe : x ∈ e.source := ⟨hxc,by change c x ∈ d.chart.source; rw [hc x hxc]; exact hxd⟩
  have he0 : e x=0 := by change d.chart (c x)=0; rw [hc x hxc,hd0]
  have he : MDifferentiableOn (model n) 𝓘(ℂ,Model r × Model s) e e.source :=
    d.holomorphic.comp (hcd.mono inter_subset_left) (fun _ hy ↦ hy.2)
  have hei : MDifferentiableOn 𝓘(ℂ,Model r × Model s) (model n) e.symm e.target :=
    hcdi.comp (d.inverse_holomorphic.mono inter_subset_left) (fun _ hy ↦ hy.2)
  have h0t : (0 : Model r × Model s) ∈ e.target := he0 ▸ e.map_source hxe
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds h0t)
  let V : Set (Model r × Model s) := ball 0 ε ×ˢ ball 0 ε
  have hVU : V ⊆ e.target := by
    rw [show V=ball (0 : Model r × Model s) ε from ball_prod_same _ _ _]
    exact hεU
  let b := (e.symm.restrOpen V (isOpen_ball.prod isOpen_ball)).symm
  have hbtarget : b.target=V := inter_eq_right.mpr hVU
  have hxb : x ∈ b.source := by
    change x ∈ e.source ∧ e x ∈ V
    exact ⟨hxe,by rw [he0]; exact ⟨mem_ball_self hε,mem_ball_self hε⟩⟩
  refine ⟨⟨b,ε,hε,hbtarget,he.mono inter_subset_left,hei.mono inter_subset_left,d,?_,?_⟩,hxb,he0⟩
  · intro z hz
    rw [←hc _ hz.1.1]
    exact hz.1.2
  · intro z hz
    change d.chart (c z)=d.chart (π.projection z)
    rw [hc _ hz.1.1]

namespace CoverProductChart
variable {π : OrdinaryUniversalCover X Z} (e : CoverProductChart π S)
lemma down_inverse {p : Model r × Model s} (hp : p ∈ e.chart.target) :
    π.projection (e.chart.symm p)=e.downstairs.chart.symm p := by
  have hepi := e.coordinates _ (e.chart.map_target hp)
  rw [e.chart.right_inv hp] at hepi
  exact (e.downstairs.chart.left_inv (e.maps (e.chart.map_target hp))).symm.trans
    (congrArg e.downstairs.chart.symm hepi.symm)

end CoverProductChart
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology Metric
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
namespace FirstGerm
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z} {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}

lemma GlobalProjection.plaque_constant (Q : GlobalProjection π o h₁ h₂)
    (e : CoverProductChart π S) {a : Model r} (ha : a ∈ ball 0 e.radius)
    {b c : Model s} (hb : b ∈ ball 0 e.radius) (hc : c ∈ ball 0 e.radius) :
    Q.toFun (e.chart.symm (a,b))=Q.toFun (e.chart.symm (a,c)) := by
  let B := ball (0 : Model s) e.radius
  have hpc : PathConnectedSpace B := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_ball (0 : Model s) e.radius).isPathConnected ⟨0,mem_ball_self e.radius_pos⟩)
  let : PathConnectedSpace B := hpc
  let β := PathConnectedSpace.somePath (⟨c,hc⟩ : B) (⟨b,hb⟩ : B)
  have htar (t : I) : (a,(β t).val) ∈ e.chart.target := by
    rw [e.product_range]; exact ⟨ha,(β t).property⟩
  let L : I → Z.Carrier := fun t ↦ e.chart.symm (a,(β t).val)
  have hLc : Continuous L := e.chart.symm.continuousOn.comp_continuous
    (continuous_const.prodMk (continuous_subtype_val.comp β.continuous)) htar
  have hdown (t : I) : (a,(β t).val) ∈ e.downstairs.chart.target := by
    rw [←e.chart.right_inv (htar t),e.coordinates _ (e.chart.map_target (htar t))]
    exact e.downstairs.chart.map_source (e.maps (e.chart.map_target (htar t)))
  have haD : a ∈ ball 0 e.downstairs.radius := by
    have h := hdown 0
    rw [e.downstairs.product_range] at h
    exact h.1
  let q : I → ball (0 : Model s) e.downstairs.radius := fun t ↦ ⟨(β t).val,by
    have h := hdown t
    rw [e.downstairs.product_range] at h
    exact h.2⟩
  have hq : Continuous q := (continuous_subtype_val.comp β.continuous).subtype_mk _
  have heq : π.projection ∘ L=(fun t ↦ e.downstairs.chart.symm (a,(q t).val)) := by
    ext t; exact e.down_inverse (htar t)
  have hv : ProductBoxTopology.IsVertical (splittingAtlas S) (π.projection ∘ L) := by
    rw [heq]
    exact (e.downstairs.productChart.inverse_box.vertical ⟨a,haD⟩).precomp hq
  have H := Q.vertical_constant hLc hv 1
  change Q.toFun (e.chart.symm (a,(β 1).val))=Q.toFun (e.chart.symm (a,(β 0).val)) at H
  simpa only [β.target,β.source] using H

lemma GlobalProjection.chart_factor (Q : GlobalProjection π o h₁ h₂)
    (e : CoverProductChart π S) :
    EqOn Q.toFun (fun z ↦ Q.toFun (e.chart.symm ((e.chart z).1,0))) e.chart.source := by
  intro z hz
  have ht := e.chart.map_source hz
  rw [e.product_range] at ht
  have H := Q.plaque_constant e ht.1 ht.2 (mem_ball_self e.radius_pos)
  rwa [Prod.eta,e.chart.left_inv hz] at H

end FirstGerm
end UniversalCoverSplitting
end
end

end OAI
