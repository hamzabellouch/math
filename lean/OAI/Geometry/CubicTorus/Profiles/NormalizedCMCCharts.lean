import Mathlib
import OAI.Geometry.CubicTorus.Profiles.SiblingCmcSecant

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem sibling_normalGraph_regraph_normal {n m : Cover} (hn : ‖n‖=1) (hm : ‖m‖=1)
    {g h : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (_hg0 : g 0=0) (hh0 : h 0=0)
    {I : Plane → Plane} (hIc : ContinuousAt I 0) (hI0 : I 0=0)
    (he : ∀ᶠ y in 𝓝 (0 : Plane),normalGraph m h y=normalGraph n g (I y))
    {a : Cover} {N : Cover → Cover} (hN : Continuous N) (hNm : N a=m)
    {σ : ℝ} (hσ : σ=1 ∨ σ= -1)
    (hmatch : ∀ᶠ y in 𝓝 (0 : Plane),N (a+normalGraph n g y)=σ • graphSlopeNormal n (gradient g y)) :
    gradient h 0=0 ∧
      ∀ᶠ y in 𝓝 (0 : Plane),N (a+normalGraph m h y)=graphSlopeNormal m (gradient h y) := by
  let G := normalGraph n g
  let K := normalGraph m h
  have hG := normalGraph_contDiff hg (n := n)
  have hK := normalGraph_contDiff hh (n := m)
  have hK0 : K 0=0 := by
    change (normalPlaneLinearIsometry m) 0+h 0 • m=0
    rw [map_zero,hh0,zero_smul,add_zero]
  have hi : Tendsto I (𝓝 (0 : Plane)) (𝓝 (0 : Plane)) := by simpa only [hI0] using hIc.tendsto
  have he' : ∀ᶠ y in 𝓝 (0 : Plane),G (normalPlaneCoordinates n (K y))=K y := by
    filter_upwards [he] with y hy
    change normalGraph n g (normalPlaneCoordinates n (normalGraph m h y))=normalGraph m h y
    rw [hy,normalPlaneCoordinates_graph hn]
  have hmt : ∀ᶠ y in 𝓝 (0 : Plane),‖N (a+K y)‖=1 ∧
      ∀ w : Plane,⟪N (a+K y),fderiv ℝ K y w⟫=0 := by
    filter_upwards [he,hi.eventually hmatch,he'.eventually_nhds] with y hy hmy hye
    have hNy : N (a+K y)=σ • graphSlopeNormal n (gradient g (I y)) := by change N (a+normalGraph m h y)=_; rw [hy]; exact hmy
    refine ⟨?_,?_⟩
    · rw [hNy]; rcases hσ with rfl|rfl <;> simpa only [one_smul,neg_one_smul,norm_neg] using graphSlopeNormal_unit hn _
    · intro w
      have hye' : (fun z ↦ G (normalPlaneCoordinates n (K z)))=ᶠ[𝓝 y] K := hye
      have hd := hye'.fderiv_eq (𝕜 := ℝ)
      have hdP := (normalPlaneCoordinates n).hasFDerivAt.comp y (hK.differentiable (by simp) y).hasFDerivAt
      have hdG := ((hG.differentiable (by simp) _).hasFDerivAt.comp y hdP).fderiv
      change fderiv ℝ (normalGraph n g ∘ normalPlaneCoordinates n ∘ normalGraph m h) y=fderiv ℝ K y at hd
      rw [hdG] at hd
      have hc : normalPlaneCoordinates n (K y)=I y := by change normalPlaneCoordinates n (normalGraph m h y)=_; rw [hy,normalPlaneCoordinates_graph hn]
      change (fderiv ℝ G (normalPlaneCoordinates n (K y))).comp ((normalPlaneCoordinates n).comp (fderiv ℝ K y)) = fderiv ℝ K y at hd
      rw [← hd,ContinuousLinearMap.comp_apply,hc,hNy,real_inner_smul_left]
      rw [normalGraph_tangent_normal hn hg,mul_zero]
  have htan0 := hmt.self_of_nhds.2
  rw [hK0,add_zero,hNm] at htan0
  have hgrad := normalGraph_gradient_zero_of_normal hm hh 0 htan0
  have hnormal0 : graphSlopeNormal m (gradient h 0)=m := by
    rw [hgrad,graphSlopeNormal_weight hm]
    change (cmcWeight 0)⁻¹ • (m-(normalPlaneLinearIsometry m) 0)=m
    simp [cmcWeight]
  have hpos : ∀ᶠ y in 𝓝 (0 : Plane),0<⟪graphSlopeNormal m (gradient h y),N (a+K y)⟫ := by
    have hc : Continuous (fun y : Plane ↦ ⟪graphSlopeNormal m (gradient h y),N (a+K y)⟫) :=
      (((graphSlopeNormal_contDiff hm).comp (plane_gradient_contDiff hh)).continuous.inner
      (hN.comp (continuous_const.add hK.continuous)))
    apply hc.continuousAt.eventually (lt_mem_nhds ?_)
    change 0 < ⟪graphSlopeNormal m (gradient h 0),N (a+K 0)⟫
    rw [hK0,add_zero,hNm,hnormal0,real_inner_self_eq_norm_sq,hm,one_pow]; norm_num
  refine ⟨hgrad,?_⟩
  filter_upwards [hmt,hpos] with y hy hpy
  exact graph_normal_tangent_positive hm hh y hy.1 hy.2 hpy

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_normalized_CMC_chart {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {H : ℝ} (hboundary : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H)
    (a : Cover) (ha : quotientMap a∈frontier (openRepresentative E)) :
    ∃ f : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) f ∧ f 0=0 ∧ gradient f 0=0 ∧
      (∀ᶠ y in 𝓝 (0 : Plane),
        N (a+normalGraph (N a) f y)=graphSlopeNormal (N a) (gradient f y) ∧
        quotientMap (a+normalGraph (N a) f y)∈frontier (openRepresentative E) ∧
        planeCMC f y= -H) ∧
      ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (a+v)∈frontier (openRepresentative E) ↔
        normalGraph (N a) f (normalPlaneCoordinates (N a) v)=v := by
  obtain ⟨n,g,σ,hn,hg,hg0,hσ,hmatch,hcover⟩ :=
    isMinimizerAt_normal_graph_chart hV hE hmin hμ hN hp hae a ha
  have hm : ‖N a‖=1 := (hboundary a ha).1.self_of_nhds
  have hgG0 : normalGraph n g 0=0 := by
    change (normalPlaneLinearIsometry n) 0+g 0 • n=0
    rw [map_zero,hg0,zero_smul,add_zero]
  have hNa : N a=σ • graphSlopeNormal n (gradient g 0) := by
    simpa only [hgG0,add_zero] using hmatch.self_of_nhds.1
  have ht : ⟪graphSlopeNormal n (gradient g 0),N a⟫≠0 := by
    rw [hNa,real_inner_smul_right,real_inner_self_eq_norm_sq,graphSlopeNormal_unit hn,
      one_pow,mul_one]
    rcases hσ with rfl|rfl <;> norm_num
  obtain ⟨f,I,hf,hf0,hIc,hI0,heq,hcov⟩ := sibling_normalGraph_regraph hn hm hg hg0 ht
  have hnorm := sibling_normalGraph_regraph_normal hn hm hg hf hg0 hf0 hIc hI0 heq hN.continuous rfl
    hσ (hmatch.mono (fun _ hy ↦ hy.1))
  have hi : Tendsto I (𝓝 (0 : Plane)) (𝓝 (0 : Plane)) := by simpa only [hI0] using hIc.tendsto
  have hmem : ∀ᶠ y in 𝓝 (0 : Plane),
      quotientMap (a+normalGraph (N a) f y)∈frontier (openRepresentative E) := by
    filter_upwards [heq,hi.eventually hmatch] with y hy hm
    rw [hy]
    exact hm.2
  refine ⟨f,hf,hf0,hnorm.1,?_,?_⟩
  · filter_upwards [hnorm.2,hmem,hnorm.2.eventually_nhds] with y hy hmy hny
    refine ⟨hy,hmy,?_⟩
    have hny' : ∀ᶠ z in 𝓝 y,N (a+normalGraph (N a) f z)=
        (1 : ℝ) • graphSlopeNormal (N a) (gradient f z) := by simpa only [one_smul] using hny
    have hd := graph_normal_extension_divergence a hm hf y (Or.inl rfl) hN
      (hboundary _ hmy).1 hny'
    rw [(hboundary _ hmy).2] at hd
    change H= -(1 : ℝ)*planeCMC f y at hd
    linarith
  · filter_upwards [hcover,hcov] with v hv hc
    exact hv.trans hc.symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_injective {m : Cover} (hm : ‖m‖=1) (g : Plane → ℝ) :
    Function.Injective (normalGraph m g) := by
  intro x y he
  have hh := congrArg (normalPlaneCoordinates m) he
  simpa only [normalPlaneCoordinates_graph hm] using hh

lemma normalGraph_height_eq {m : Cover} (hm : ‖m‖=1) {f g : Plane → ℝ}
    {y : Plane} (he : normalGraph m f y=normalGraph m g y) : f y=g y := by
  have hh := congrArg (fun v : Cover ↦ ⟪m,v⟫) he
  simp only [normalGraph,inner_add_right,normalPlaneEmbedding_inner hm,
    real_inner_smul_right,real_inner_self_eq_norm_sq,hm,one_pow,mul_one,zero_add] at hh
  exact hh

theorem normal_graph_germ_coincidence {m : Cover} (hm : ‖m‖=1)
    {f g : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hf0 : f 0=0) (hg0 : g 0=0)
    {B C : Set Cover}
    (hB : ∀ᶠ v in 𝓝 (0 : Cover),v∈B ↔ normalGraph m f (normalPlaneCoordinates m v)=v)
    (hC : ∀ᶠ v in 𝓝 (0 : Cover),v∈C ↔ normalGraph m g (normalPlaneCoordinates m v)=v)
    (hcmc : ∀ᶠ y in 𝓝 (0 : Plane),planeCMC f y=planeCMC g y)
    (hcl : (0 : Cover)∈closure (B∩{v | ∀ᶠ w in 𝓝 v,w∈B ↔ w∈C})) :
    f=ᶠ[𝓝 (0 : Plane)]g := by
  have hF := normalGraph_contDiff hf (n := m)
  have hG := normalGraph_contDiff hg (n := m)
  have hF0 : normalGraph m f 0=0 := by
    change (normalPlaneLinearIsometry m) 0+f 0 • m=0
    rw [map_zero,hf0,zero_smul,add_zero]
  have hG0 : normalGraph m g 0=0 := by
    change (normalPlaneLinearIsometry m) 0+g 0 • m=0
    rw [map_zero,hg0,zero_smul,add_zero]
  have hFt : Tendsto (normalGraph m f) (𝓝 0) (𝓝 0) := by simpa only [hF0] using (hF.continuous.continuousAt (x := 0)).tendsto
  have hBC : ∀ᶠ y in 𝓝 (0 : Plane),normalGraph m f y∈B ∧
      (normalGraph m f y∈C ↔ normalGraph m g y=normalGraph m f y) := by
    filter_upwards [hFt.eventually hB,hFt.eventually hC] with y hyB hyC
    rw [normalPlaneCoordinates_graph hm] at hyB hyC
    exact ⟨hyB.mpr rfl,hyC⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hcmc.and hBC)
  have hP0 : normalPlaneCoordinates m (0 : Cover)=0 := map_zero _
  have hnh : {v : Cover | normalPlaneCoordinates m v∈Metric.ball (0 : Plane) r}∈𝓝 0 := by
    exact (normalPlaneCoordinates m).continuous.continuousAt.preimage_mem_nhds
      (by simpa only [hP0] using Metric.ball_mem_nhds (normalPlaneCoordinates m 0) hr)
  have hex : ((B∩{v | ∀ᶠ w in 𝓝 v,w∈B ↔ w∈C})∩
      {v | (v∈B ↔ normalGraph m f (normalPlaneCoordinates m v)=v) ∧
        normalPlaneCoordinates m v∈Metric.ball (0 : Plane) r}).Nonempty := by
    obtain ⟨v,hv₁,hv₂⟩ := mem_closure_iff_nhds.mp hcl _ (hB.and hnh)
    exact ⟨v,hv₂,hv₁⟩
  obtain ⟨v,⟨hvB,hvag⟩,hvch,hvy⟩ := hex
  let y := normalPlaneCoordinates m v
  have hFy : normalGraph m f y=v := hvch.mp hvB
  have hev : ∀ᶠ z in 𝓝 y,normalGraph m f z∈B ↔ normalGraph m f z∈C :=
    (show Tendsto (normalGraph m f) (𝓝 y) (𝓝 v) from by
      simpa only [hFy] using (hF.continuous.continuousAt (x := y)).tendsto).eventually hvag
  have hyeq : y∈interior {z | f z=g z} := by
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hev,Metric.isOpen_ball.mem_nhds hvy] with z hz hzball
    have hmem := (hball hzball).2
    apply normalGraph_height_eq hm
    exact ((hmem.2.mp (hz.mp hmem.1))).symm
  have heq := smooth_CMC_graph_coincidence hf hg Metric.isOpen_ball
    (convex_ball (0 : Plane) r).isPreconnected (fun _ hz ↦ (hball hz).1) ⟨y,hvy,hyeq⟩
  exact Filter.mem_of_superset (Metric.ball_mem_nhds 0 hr) heq

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isOpenMap_quotientMap : IsOpenMap quotientMap := by
  have ho : IsOpenMap (Pi.map (fun _ : Fin 3 ↦ fun t : ℝ ↦ (t : AddCircle (1 : ℝ)))) :=
    IsOpenMap.piMap (fun _ ↦ QuotientAddGroup.isOpenMap_coe)
      (Eventually.of_forall (fun _ ↦ QuotientAddGroup.mk_surjective))
  exact (PiLp.homeomorph 2 (fun _ : Fin 3 ↦ AddCircle (1 : ℝ))).symm.isOpenMap.comp
    (ho.comp (PiLp.homeomorph 2 (fun _ : Fin 3 ↦ ℝ)).isOpenMap)

lemma isOpenMap_shiftedQuotient (a : Cover) : IsOpenMap (fun v ↦ quotientMap (a+v)) :=
  isOpenMap_quotientMap.comp (Homeomorph.addLeft a).isOpenMap

lemma shiftedQuotient_nhds (a : Cover) :
    Filter.map (fun v ↦ quotientMap (a+v)) (𝓝 (0 : Cover))=𝓝 (quotientMap a) := by
  simpa only [add_zero] using (isOpenMap_shiftedQuotient a).map_nhds_eq
    ((continuous_quotientMap.comp (continuous_const.add continuous_id)).continuousAt (x := 0))

def HasNormalizedCMCCharts (B : Set Torus) (N : Cover → Cover) (H : ℝ) : Prop :=
  ∀ a : Cover,quotientMap a∈B → ‖N a‖=1 ∧
    ∃ f : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) f ∧ f 0=0 ∧ gradient f 0=0 ∧
      (∀ᶠ y in 𝓝 (0 : Plane),
        N (a+normalGraph (N a) f y)=graphSlopeNormal (N a) (gradient f y) ∧
        quotientMap (a+normalGraph (N a) f y)∈B ∧ planeCMC f y= -H) ∧
      ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (a+v)∈B ↔
        normalGraph (N a) f (normalPlaneCoordinates (N a) v)=v

lemma isMinimizerAt_hasNormalizedCMCCharts {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {H : ℝ} (hboundary : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H) :
    HasNormalizedCMCCharts (frontier (openRepresentative E)) N H := by
  intro a ha
  exact ⟨(hboundary a ha).1.self_of_nhds,
    isMinimizerAt_normalized_CMC_chart hV hE hmin hμ hN hp hae hboundary a ha⟩

def orientedSurfaceAgreement (B C : Set Torus) (N M : Cover → Cover) : Set Torus :=
  {x | ∀ᶠ y in 𝓝 x,(y∈B ↔ y∈C) ∧ (y∈B → N (representative y)=M (representative y))}

lemma isOpen_orientedSurfaceAgreement (B C : Set Torus) (N M : Cover → Cover) :
    IsOpen (orientedSurfaceAgreement B C N M) := isOpen_setOfPred_eventually_nhds

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cmc_strong_minimum {p : Plane → Plane} {f : Plane → ℝ}
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {Ω : Set Plane} (hΩ : IsOpen Ω) (hc : IsPreconnected Ω)
    (hpb : ∀ y∈Ω,‖p y‖≤1) (hpos : ∀ y∈Ω,0≤f y)
    (hL : ∀ y∈Ω,planeDivergence (fun z ↦ cmcJacobian (p z) (gradient f z)) y=0)
    {z : Plane} (hz : z∈Ω) (hfz : f z=0) : ∀ y∈Ω,f y=0 := by
  let O : Set Plane := Ω∩{x | 0<f x}
  have hO : IsOpen O := hΩ.inter (isOpen_lt continuous_const hf.continuous)
  by_cases hn : O.Nonempty
  · have hsub : Ω⊆O := hc.subset_of_closure_inter_subset hO
      (by obtain ⟨x,hx⟩ := hn; exact ⟨x,hx.1,hx⟩) (by
        rintro x ⟨hxcl,hxΩ⟩
        by_contra hxO
        obtain ⟨s,hs,hsΩ⟩ := Metric.isOpen_iff.mp hΩ x hxΩ
        obtain ⟨a,b,R,hR,hbR,hbcl,hbO,hball,hclosed⟩ :=
          plane_interior_tangent_ball_at hO hxcl hxO hs
        have hbΩ : b∈Ω := hsΩ (hclosed (by
          simp only [Metric.mem_closedBall,dist_eq_norm,hbR,le_refl]))
        have hfb : f b=0 := le_antisymm (le_of_not_gt (fun hh ↦ hbO ⟨hbΩ,hh⟩)) (hpos b hbΩ)
        have hd := cmc_hopf_inward_derivative hp hf hR hbR hfb
          (fun y hy ↦ hpb y (hsΩ (hclosed hy)))
          (fun y hy ↦ (hball hy).2)
          (fun y hy ↦ hL y (hsΩ (hclosed (Metric.ball_subset_closedBall hy))))
        have hm : IsLocalMin f b := by
          filter_upwards [hΩ.mem_nhds hbΩ] with y hy
          rw [hfb]
          exact hpos y hy
        have hzero := hm.fderiv_eq_zero
        rw [hzero] at hd
        exact (lt_irrefl (0:ℝ)) hd)
    have hh := (hsub hz).2
    change 0<f z at hh
    rw [hfz] at hh
    exact (lt_irrefl (0:ℝ) hh).elim
  · intro y hy
    exact le_antisymm (le_of_not_gt (fun hh ↦ hn ⟨y,hy,hh⟩)) (hpos y hy)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def boundaryZeroGerm (S : Set Torus) (F : Torus → ℝ) : Set Torus :=
  {x | ∀ᶠ y in 𝓝 x,y∈S → F y=0}

lemma boundaryZeroGerm_open (S : Set Torus) (F : Torus → ℝ) :
    IsOpen (boundaryZeroGerm S F) := isOpen_setOfPred_eventually_nhds

lemma CenteredJacobiChart.zero_trace_germ
    {E : Set Torus} {μ : FiniteMeasure NormalBundle} {N : Cover → Cover}
    (c : CenteredJacobiChart E μ N) (f : smoothPeriodicScalars)
    (hz : ∀ᶠ y in 𝓝 (0 : Plane),f.val (c.parameter y)=0) :
    quotientMap cubeCenter∈boundaryZeroGerm (frontier (openRepresentative E))
      (fun x ↦ f.val (representative x)) := by
  change ∀ᶠ x in 𝓝 (quotientMap cubeCenter),x∈frontier (openRepresentative E) →
    f.val (representative x)=0
  rw [←shiftedQuotient_nhds cubeCenter]
  change ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (cubeCenter+v)∈frontier (openRepresentative E) →
    f.val (representative (quotientMap (cubeCenter+v)))=0
  have hP : Tendsto (normalPlaneCoordinates c.n) (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) := by
    simpa only [map_zero] using ((normalPlaneCoordinates c.n).continuous.continuousAt (x := 0)).tendsto
  filter_upwards [c.cover_germ,hP.eventually hz] with v hv hzv hB
  rw [periodic_representative f.property.2]
  have he := hv.mp hB
  change f.val (cubeCenter+normalGraph c.n c.g (normalPlaneCoordinates c.n v))=0 at hzv
  rwa [he] at hzv

theorem CenteredJacobiChart.zero_germ_closed
    {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (haeN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (c : CenteredJacobiChart E μ N)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (f : smoothPeriodicScalars)
    (hjf : ∀ v∈surfaceH1 μ,surfaceJacobiB μ q (surfaceSmoothJet μ f) v=0)
    (hjw : ∀ v∈surfaceH1 μ,surfaceJacobiB μ q
      (surfaceSmoothJet μ (directionalNormalScalar N hN hp c.n)) v=0)
    (hcl : quotientMap cubeCenter∈closure (frontier (openRepresentative E)∩
      boundaryZeroGerm (frontier (openRepresentative E)) (fun x ↦ f.val (representative x)))) :
    quotientMap cubeCenter∈boundaryZeroGerm (frontier (openRepresentative E))
      (fun x ↦ f.val (representative x)) := by
  let F : Plane → ℝ := fun y ↦ c.weight y*f.val (c.parameter y)
  let A : Plane → Plane →L[ℝ] Plane := fun y ↦ cmcJacobian (gradient c.g y)
  let r := c.r/2
  have hr : 0<r := half_pos c.r_pos
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := c.weight_smooth.mul (f.property.1.comp c.parameter_smooth)
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := cmcJacobian_contDiff.comp (plane_gradient_contDiff c.smooth)
  have hL := c.classical_ground_state hE hμ hN hp haeN q f hjf hjw
  have hzero : (Metric.ball (0 : Plane) r∩interior {y | F y=0}).Nonempty := by
    have hc := c.closure_pullback inter_subset_left hcl hr
    obtain ⟨y,hy,hy0⟩ := Metric.mem_closure_iff.mp hc r hr
    refine ⟨y,hy.1,mem_interior_iff_mem_nhds.mpr ?_⟩
    have hz := (continuous_quotientMap.comp c.parameter_smooth.continuous).continuousAt.eventually hy.2.2
    filter_upwards [hz,Metric.isOpen_ball.mem_nhds hy.1] with z hz hzball
    have hB := c.boundary_disk z (Metric.ball_subset_closedBall
      (Metric.ball_subset_ball (by dsimp [r]; linarith [c.r_pos]) hzball))
    have he := hz hB
    simp only [Function.comp_apply,periodic_representative f.property.2] at he
    change c.weight z*f.val (c.parameter z)=0
    rw [he,mul_zero]
  have hz := plane_elliptic_unique_continuation hA
    (fun y v w ↦ (cmcJacobian_symmetric _ v w).trans (real_inner_comm _ _)) hF
    Metric.isOpen_ball (convex_ball (0 : Plane) r).isPreconnected
    (fun y hy ↦ ⟨1/8,by norm_num,fun v ↦ by
      have hs := (c.slope_disk y (Metric.ball_subset_closedBall
        (Metric.ball_subset_ball (by dsimp [r]; linarith [c.r_pos]) hy))).trans (by norm_num : (1/4:ℝ)≤1)
      simpa only [A,real_inner_comm] using cmcJacobian_coercive hs v⟩)
    (fun y hy ↦ hL y hy) hzero
  apply c.zero_trace_germ f
  filter_upwards [Metric.ball_mem_nhds (0 : Plane) hr] with y hy
  have he := hz y hy
  exact (mul_eq_zero.mp he).resolve_left (cmcWeight_pos _).ne'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def sibling_smoothScalarTranslate (a : Cover) (f : smoothPeriodicScalars) : smoothPeriodicScalars :=
  ⟨fun x ↦ f.val (x+a),f.property.1.comp (contDiff_id.add contDiff_const),by
    intro m x
    dsimp
    rw [add_right_comm,f.property.2]⟩

lemma smoothScalarTranslate_gradient (a : Cover) (f : smoothPeriodicScalars) (x : Cover) :
    gradient (sibling_smoothScalarTranslate a f).val x=gradient f.val (x+a) := by
  have he : fderiv ℝ (sibling_smoothScalarTranslate a f).val x=fderiv ℝ f.val (x+a) := by
    have hd := (f.property.1.differentiable (by simp) (x+a)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).add_const a)
    simpa only [ContinuousLinearMap.comp_id,Function.comp_def,id_eq,sibling_smoothScalarTranslate] using hd.fderiv
  simp only [gradient,he]

lemma sibling_translateNormal_measurePreserving (μ : FiniteMeasure NormalBundle) (a : Cover) :
    MeasurePreserving (translateNormal a) (μ : Measure NormalBundle)
      (μ.map (translateNormal a) : Measure NormalBundle) :=
  ⟨measurable_translateNormal a,rfl⟩

def normalTranslatePullback (μ : FiniteMeasure NormalBundle) (a : Cover) (W : Type*)
    [NormedAddCommGroup W] [NormedSpace ℝ W] :
    Lp W 2 (μ.map (translateNormal a) : Measure NormalBundle) →ₗᵢ[ℝ]
      Lp W 2 (μ : Measure NormalBundle) :=
  Lp.compMeasurePreservingₗᵢ ℝ (translateNormal a) (sibling_translateNormal_measurePreserving μ a)

def normalTranslateJet (μ : FiniteMeasure NormalBundle) (a : Cover) :
    SurfaceJet (μ.map (translateNormal a)) →L[ℝ] SurfaceJet μ :=
  (normalTranslatePullback μ a ℝ).toContinuousLinearMap.prodMap
    (normalTranslatePullback μ a Cover).toContinuousLinearMap

lemma normalTranslateJet_ae (μ : FiniteMeasure NormalBundle) (a : Cover)
    (u : SurfaceJet (μ.map (translateNormal a))) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),
      (normalTranslateJet μ a u).1 z=u.1 (translateNormal a z) ∧
      (normalTranslateJet μ a u).2 z=u.2 (translateNormal a z) :=
  (Lp.coeFn_compMeasurePreserving u.1 (sibling_translateNormal_measurePreserving μ a)).and
    (Lp.coeFn_compMeasurePreserving u.2 (sibling_translateNormal_measurePreserving μ a))

lemma normalTranslateJet_smooth (μ : FiniteMeasure NormalBundle) (a : Cover)
    (f : smoothPeriodicScalars) :
    normalTranslateJet μ a (surfaceSmoothJet (μ.map (translateNormal a)) f)=
      surfaceSmoothJet μ (sibling_smoothScalarTranslate (-a) f) := by
  have hscalar := ae_of_ae_map (measurable_translateNormal a).aemeasurable
    ((smoothScalarValue f).coeFn_toLp (p := 2) (𝕜 := ℝ)
      (μ.map (translateNormal a) : Measure NormalBundle))
  have hgrad := ae_of_ae_map (measurable_translateNormal a).aemeasurable
    ((smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ)
      (μ.map (translateNormal a) : Measure NormalBundle))
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [normalTranslateJet_ae μ a (surfaceSmoothJet (μ.map (translateNormal a)) f),
      hscalar,(smoothScalarValue (sibling_smoothScalarTranslate (-a) f)).coeFn_toLp
        (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)] with z hz h₁ h₂
    rw [hz.1]
    change (surfaceSmoothJet (μ.map (translateNormal a)) f).1 (translateNormal a z)=
      f.val (translateNormal a z).1 at h₁
    change (surfaceSmoothJet μ (sibling_smoothScalarTranslate (-a) f)).1 z=f.val ((z.1 : Cover)+(-a)) at h₂
    rw [h₁,h₂,translateNormal_periodic_eval f.property.2]
    rfl
  · apply Lp.ext
    filter_upwards [normalTranslateJet_ae μ a (surfaceSmoothJet (μ.map (translateNormal a)) f),
      hgrad,(smoothScalarGradient (sibling_smoothScalarTranslate (-a) f)).coeFn_toLp
        (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)] with z hz h₁ h₂
    rw [hz.2]
    change (surfaceSmoothJet (μ.map (translateNormal a)) f).2 (translateNormal a z)=
      smoothScalarGradient f (translateNormal a z) at h₁
    change (surfaceSmoothJet μ (sibling_smoothScalarTranslate (-a) f)).2 z=
      smoothScalarGradient (sibling_smoothScalarTranslate (-a) f) z at h₂
    rw [h₁,h₂]
    change gradient f.val (translateNormal a z).1-
      ⟪(z.2 : Cover),gradient f.val (translateNormal a z).1⟫ • (z.2 : Cover)=_
    rw [translateNormal_periodic_eval (gradient_periodic f.property.2)]
    change _=gradient (sibling_smoothScalarTranslate (-a) f).val z.1-
      ⟪(z.2 : Cover),gradient (sibling_smoothScalarTranslate (-a) f).val z.1⟫ • (z.2 : Cover)
    rw [smoothScalarTranslate_gradient]
    rfl

lemma normalTranslateJet_mem_surfaceH1 (μ : FiniteMeasure NormalBundle) (a : Cover)
    {u : SurfaceJet (μ.map (translateNormal a))} (hu : u∈surfaceH1 (μ.map (translateNormal a))) :
    normalTranslateJet μ a u∈surfaceH1 μ := by
  have hc : IsClosed ((normalTranslateJet μ a) ⁻¹' (surfaceH1 μ : Set (SurfaceJet μ))) :=
    (show IsClosed (surfaceH1 μ : Set (SurfaceJet μ)) from isClosed_closure).preimage
      (normalTranslateJet μ a).continuous
  apply closure_minimal (t := (normalTranslateJet μ a) ⁻¹' (surfaceH1 μ : Set (SurfaceJet μ))) ?_ hc hu
  rintro _ ⟨f,rfl⟩
  change normalTranslateJet μ a (surfaceSmoothJet (μ.map (translateNormal a)) f)∈surfaceH1 μ
  rw [normalTranslateJet_smooth]
  exact subset_closure (LinearMap.mem_range_self _ _)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalTranslate_multiplier (μ : FiniteMeasure NormalBundle) (a : Cover)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle))
    (q' : Lp ℝ ∞ (μ.map (translateNormal a) : Measure NormalBundle))
    (hq : ∀ᵐ z ∂(μ : Measure NormalBundle),q' (translateNormal a z)=q z)
    (u : Lp ℝ 2 (μ.map (translateNormal a) : Measure NormalBundle)) :
    normalTranslatePullback μ a ℝ (surfaceMultiplier _ q' u)=
      surfaceMultiplier μ q (normalTranslatePullback μ a ℝ u) := by
  apply Lp.ext
  have hm := ae_of_ae_map (measurable_translateNormal a).aemeasurable
    (Lp.coeFn_lpSMul (r := 2) q' u)
  filter_upwards [Lp.coeFn_compMeasurePreserving (surfaceMultiplier _ q' u)
    (sibling_translateNormal_measurePreserving μ a),
    Lp.coeFn_compMeasurePreserving u (sibling_translateNormal_measurePreserving μ a),
    Lp.coeFn_lpSMul (r := 2) q (normalTranslatePullback μ a ℝ u),hm,hq] with z hz hu hv hm hq
  change (normalTranslatePullback μ a ℝ (surfaceMultiplier _ q' u)) z=_ at hz
  change (normalTranslatePullback μ a ℝ u) z=_ at hu
  change (surfaceMultiplier _ q (normalTranslatePullback μ a ℝ u)) z=_ at hv
  change (surfaceMultiplier _ q' u) (translateNormal a z)=_ at hm
  rw [hz]
  simp only [Function.comp_apply]
  rw [hm,hv]
  simp only [smul_eq_mul,Pi.mul_apply,hq,hu,Function.comp_apply]

lemma normalTranslate_Jacobi (μ : FiniteMeasure NormalBundle) (a : Cover)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle))
    (q' : Lp ℝ ∞ (μ.map (translateNormal a) : Measure NormalBundle))
    (hq : ∀ᵐ z ∂(μ : Measure NormalBundle),q' (translateNormal a z)=q z)
    (u v : SurfaceJet (μ.map (translateNormal a))) :
    surfaceJacobiB μ q (normalTranslateJet μ a u) (normalTranslateJet μ a v)=
      surfaceJacobiB (μ.map (translateNormal a)) q' u v := by
  change ⟪normalTranslatePullback μ a Cover u.2,normalTranslatePullback μ a Cover v.2⟫-
    ⟪surfaceMultiplier μ q (normalTranslatePullback μ a ℝ u.1),
      normalTranslatePullback μ a ℝ v.1⟫=_
  rw [← normalTranslate_multiplier μ a q q' hq u.1,
    (normalTranslatePullback μ a Cover).inner_map_map,
    (normalTranslatePullback μ a ℝ).inner_map_map]
  rfl

lemma normalTranslate_one (μ : FiniteMeasure NormalBundle) (a : Cover) :
    normalTranslateJet μ a (surfaceOne (μ.map (translateNormal a)))=surfaceOne μ := by
  rw [surfaceOne,normalTranslateJet_smooth]
  rfl

lemma normalTranslate_mean (μ : FiniteMeasure NormalBundle) (a : Cover)
    (u : SurfaceJet (μ.map (translateNormal a))) :
    surfaceMean μ (normalTranslateJet μ a u)=surfaceMean (μ.map (translateNormal a)) u := by
  change ⟪(surfaceOne μ).1,normalTranslatePullback μ a ℝ u.1⟫=_
  have h := congrArg Prod.fst (normalTranslate_one μ a)
  change normalTranslatePullback μ a ℝ (surfaceOne (μ.map (translateNormal a))).1=(surfaceOne μ).1 at h
  rw [← h,(normalTranslatePullback μ a ℝ).inner_map_map]
  rfl

def normalTranslateField (a : Cover) (N : Cover → Cover) : Cover → Cover := fun x ↦ N (x+a)

lemma normalTranslateField_smooth (a : Cover) {N : Cover → Cover}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) : ContDiff ℝ (⊤ : ℕ∞) (normalTranslateField a N) :=
  hN.comp (contDiff_id.add contDiff_const)

lemma normalTranslateField_periodic (a : Cover) {N : Cover → Cover}
    (hp : ∀ m x,N (x+latticeVector m)=N x) :
    ∀ m x,normalTranslateField a N (x+latticeVector m)=normalTranslateField a N x := by
  intro m x
  dsimp [normalTranslateField]
  rw [add_right_comm,hp]

lemma normalTranslateField_fderiv (a : Cover) {N : Cover → Cover}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (x : Cover) :
    fderiv ℝ (normalTranslateField a N) x=fderiv ℝ N (x+a) := by
  have hd := (hN.differentiable (by simp) (x+a)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).add_const a)
  change fderiv ℝ (fun y : Cover ↦ N (y+a)) x=_
  simpa only [ContinuousLinearMap.comp_id,Function.comp_def,id_eq] using hd.fderiv

lemma normalTranslate_curvature (μ : FiniteMeasure NormalBundle) (a : Cover)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),
      surfaceCurvatureLp (μ.map (translateNormal a)) (normalTranslateField a N)
        (normalTranslateField_smooth a hN) (translateNormal a z)=surfaceCurvatureLp μ N hN z := by
  have hq := (show C(NormalBundle,ℝ) from ⟨_,
    (normal_curvature_continuous hN).comp (continuous_subtype_val.comp continuous_fst)⟩).coeFn_toLp
    (p := ∞) (𝕜 := ℝ) (μ : Measure NormalBundle)
  have hq' := (show C(NormalBundle,ℝ) from ⟨_,
    (normal_curvature_continuous (normalTranslateField_smooth a hN)).comp
      (continuous_subtype_val.comp continuous_fst)⟩).coeFn_toLp
    (p := ∞) (𝕜 := ℝ) (μ.map (translateNormal a) : Measure NormalBundle)
  have he := ae_of_ae_map (measurable_translateNormal a).aemeasurable hq'
  filter_upwards [hq,he] with z hz hz'
  change surfaceCurvatureLp μ N hN z=_ at hz
  change surfaceCurvatureLp (μ.map (translateNormal a)) (normalTranslateField a N)
    (normalTranslateField_smooth a hN) (translateNormal a z)=_ at hz'
  rw [hz,hz']
  change coverTrace ((fderiv ℝ (normalTranslateField a N) (translateNormal a z).1).comp
    (fderiv ℝ (normalTranslateField a N) (translateNormal a z).1))=
    coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1))
  have hper := fderiv_periodic (normalTranslateField_periodic a hp)
  rw [translateNormal_periodic_eval hper,normalTranslateField_fderiv a hN]
  simp only [sub_add_cancel]

lemma normalTranslate_smooth_inverse (a : Cover) (f : smoothPeriodicScalars) :
    sibling_smoothScalarTranslate (-a) (sibling_smoothScalarTranslate a f)=f := by
  apply Subtype.ext
  funext x
  simp only [sibling_smoothScalarTranslate,neg_add_cancel_right]

lemma normalTranslate_directional (a : Cover) {N : Cover → Cover}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hp : ∀ m x,N (x+latticeVector m)=N x) (v : Cover) :
    directionalNormalScalar (normalTranslateField a N) (normalTranslateField_smooth a hN)
      (normalTranslateField_periodic a hp) v=sibling_smoothScalarTranslate a (directionalNormalScalar N hN hp v) := by
  apply Subtype.ext
  funext x
  change _=(directionalNormalScalar N hN hp v).val (x+a)
  rw [directionalNormalScalar_apply,directionalNormalScalar_apply]
  rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalTranslateJet_isometry (μ : FiniteMeasure NormalBundle) (a : Cover) :
    Isometry (normalTranslateJet μ a) := by
  apply AddMonoidHomClass.isometry_of_norm (normalTranslateJet μ a)
  intro u
  change max ‖normalTranslatePullback μ a ℝ u.1‖ ‖normalTranslatePullback μ a Cover u.2‖=
    max ‖u.1‖ ‖u.2‖
  rw [(normalTranslatePullback μ a ℝ).norm_map,(normalTranslatePullback μ a Cover).norm_map]

lemma normalTranslateJet_surjective_H1 (μ : FiniteMeasure NormalBundle) (a : Cover)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) :
    ∃ u' : SurfaceJet (μ.map (translateNormal a)),u'∈surfaceH1 (μ.map (translateNormal a)) ∧
      normalTranslateJet μ a u'=u := by
  have hc : IsClosed ((normalTranslateJet μ a) ''
      (surfaceH1 (μ.map (translateNormal a)) : Set (SurfaceJet (μ.map (translateNormal a))))) :=
    (normalTranslateJet_isometry μ a).isClosedEmbedding.isClosedMap _ isClosed_closure
  apply closure_minimal (t := (normalTranslateJet μ a) ''
      (surfaceH1 (μ.map (translateNormal a)) : Set (SurfaceJet (μ.map (translateNormal a))))) ?_ hc hu
  rintro _ ⟨f,rfl⟩
  refine ⟨surfaceSmoothJet (μ.map (translateNormal a)) (sibling_smoothScalarTranslate a f),
    subset_closure (LinearMap.mem_range_self _ _),?_⟩
  rw [normalTranslateJet_smooth,normalTranslate_smooth_inverse]

lemma sibling_normalProjection_translate (a : Cover) (z : NormalBundle) :
    normalProjection (translateNormal a z)+quotientMap a=normalProjection z := by
  change quotientMap (representative (quotientMap z.1-quotientMap a))+quotientMap a=quotientMap z.1
  rw [quotientMap_representative,sub_add_cancel]

lemma normalTranslateField_ae (μ : FiniteMeasure NormalBundle) (a : Cover)
    {N : Cover → Cover} (hN : Continuous N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    ∀ᵐ z ∂(μ.map (translateNormal a) : Measure NormalBundle),
      normalTranslateField a N z.1=(z.2 : Cover) := by
  apply (ae_map_iff (measurable_translateNormal a).aemeasurable
    (measurableSet_eq_fun ((hN.comp (continuous_id.add continuous_const)).measurable.comp
      (measurable_subtype_coe.comp measurable_fst))
      (measurable_subtype_coe.comp measurable_snd))).mpr
  filter_upwards [hae] with z hz
  change normalTranslateField a N (translateNormal a z).1=(z.2 : Cover)
  rw [translateNormal_periodic_eval (normalTranslateField_periodic a hp)]
  simpa only [normalTranslateField,sub_add_cancel] using hz

lemma normalTranslateJet_scalar_representative (μ : FiniteMeasure NormalBundle) (a : Cover)
    {u : SurfaceJet μ} {u' : SurfaceJet (μ.map (translateNormal a))}
    (he : normalTranslateJet μ a u'=u) {F : Torus → ℝ} (hF : Measurable F)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),u.1 z=F (normalProjection z)) :
    ∀ᵐ z ∂(μ.map (translateNormal a) : Measure NormalBundle),
      u'.1 z=F (normalProjection z+quotientMap a) := by
  apply (ae_map_iff (measurable_translateNormal a).aemeasurable
    (measurableSet_eq_fun (Lp.stronglyMeasurable u'.1).measurable
      (hF.comp (normalProjection_continuous.measurable.add measurable_const)))).mpr
  filter_upwards [normalTranslateJet_ae μ a u',hae] with z hz hf
  rw [he] at hz
  change u'.1 (translateNormal a z)=F (normalProjection (translateNormal a z)+quotientMap a)
  rw [← hz.1,hf,sibling_normalProjection_translate]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma smoothScalarTranslate_descent (a : Cover) (f : smoothPeriodicScalars) (b : Torus) :
    (sibling_smoothScalarTranslate a f).val (representative b)=
      f.val (representative (b+quotientMap a)) := by
  have h := periodic_representative f.property.2 (representative b+a)
  rw [quotientMap_add,quotientMap_representative] at h
  exact h.symm

lemma positiveNodalPiece_translation (a : Cover) (f : smoothPeriodicScalars)
    {S D : Set Torus} (hD : IsPositiveNodalPiece f S D) :
    IsPositiveNodalPiece (sibling_smoothScalarTranslate a f)
      ((fun b ↦ b+quotientMap a) ⁻¹' S) ((fun b ↦ b+quotientMap a) ⁻¹' D) := by
  obtain ⟨⟨U,hU,hDU⟩,⟨C,hC,hDC⟩⟩ := hD
  constructor
  · refine ⟨(fun b ↦ b+quotientMap a) ⁻¹' U,hU.preimage (continuous_id.add continuous_const),?_⟩
    ext b
    simp only [mem_preimage,hDU,mem_inter_iff,mem_ofPred_eq,smoothScalarTranslate_descent]
  · refine ⟨(fun b ↦ b+quotientMap a) ⁻¹' C,hC.preimage (continuous_id.add continuous_const),?_⟩
    ext b
    simp only [mem_preimage,hDC,mem_inter_iff,mem_ofPred_eq,smoothScalarTranslate_descent]

lemma normalTranslate_weakJacobi (μ : FiniteMeasure NormalBundle) (a : Cover)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    {u : SurfaceJet μ} (hju : ∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u v=0)
    {u' : SurfaceJet (μ.map (translateNormal a))} (he : normalTranslateJet μ a u'=u) :
    ∀ v∈surfaceH1 (μ.map (translateNormal a)),surfaceJacobiB (μ.map (translateNormal a))
      (surfaceCurvatureLp _ (normalTranslateField a N) (normalTranslateField_smooth a hN)) u' v=0 := by
  intro v hv
  rw [← normalTranslate_Jacobi μ a _ _ (normalTranslate_curvature μ a hN hp),he]
  exact hju _ (normalTranslateJet_mem_surfaceH1 μ a hv)

lemma normalTranslate_smooth_weakJacobi (μ : FiniteMeasure NormalBundle) (a : Cover)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x) (f : smoothPeriodicScalars)
    (hj : ∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ f) v=0) :
    ∀ v∈surfaceH1 (μ.map (translateNormal a)),surfaceJacobiB (μ.map (translateNormal a))
      (surfaceCurvatureLp _ (normalTranslateField a N) (normalTranslateField_smooth a hN))
      (surfaceSmoothJet _ (sibling_smoothScalarTranslate a f)) v=0 := by
  apply normalTranslate_weakJacobi μ a hN hp hj
  rw [normalTranslateJet_smooth,normalTranslate_smooth_inverse]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem orientedSurfaceAgreement_closed_at {B C : Set Torus} (hC : IsClosed C)
    {N M : Cover → Cover} (hN : Continuous N) (hM : Continuous M)
    (hpN : ∀ m x,N (x+latticeVector m)=N x)
    (hpM : ∀ m x,M (x+latticeVector m)=M x)
    {H : ℝ} (hBch : HasNormalizedCMCCharts B N H) (hCch : HasNormalizedCMCCharts C M H)
    {x : Torus} (hxB : x∈B) (hx : x∈closure (B∩orientedSurfaceAgreement B C N M)) :
    x∈orientedSurfaceAgreement B C N M := by
  have hclosed : IsClosed {y : Torus | y∈C ∧ N (representative y)=M (representative y)} :=
    hC.inter (isClosed_eq (continuous_periodic_descent hN hpN) (continuous_periodic_descent hM hpM))
  have hxc : x∈C ∧ N (representative x)=M (representative x) :=
    closure_minimal (fun y hy ↦ by
      have hy' := hy.2.self_of_nhds
      exact ⟨hy'.1.mp hy.1,hy'.2 hy.1⟩) hclosed hx
  obtain ⟨a,rfl⟩ := quotientMap_surjective x
  have hNM : N a=M a := by simpa only [periodic_representative hpN,periodic_representative hpM] using hxc.2
  obtain ⟨hn,f,hf,hf0,hdf0,hfm,hfc⟩ := hBch a hxB
  obtain ⟨_,g,hg,hg0,hdg0,hgm,hgc⟩ := hCch a hxc.1
  rw [←hNM] at hgm hgc
  let q : Cover → Torus := fun v ↦ quotientMap (a+v)
  have hq : Continuous q := continuous_quotientMap.comp (continuous_const.add continuous_id)
  have hq0 : q 0=quotientMap a := by simp only [q,add_zero]
  have hcl : (0 : Cover)∈closure
      (q ⁻¹' B∩{v : Cover | ∀ᶠ w in 𝓝 v,w∈q ⁻¹' B ↔ w∈q ⁻¹' C}) := by
    apply closure_mono (show q ⁻¹' (B∩orientedSurfaceAgreement B C N M)⊆
      q ⁻¹' B∩{v : Cover | ∀ᶠ w in 𝓝 v,w∈q ⁻¹' B ↔ w∈q ⁻¹' C} from ?_) ?_
    · intro v hv
      refine ⟨hv.1,?_⟩
      exact (hq.continuousAt.eventually hv.2).mono (fun _ hy ↦ hy.1)
    · exact (isOpenMap_shiftedQuotient a).preimage_closure_subset_closure_preimage
        (by change q 0∈closure (B∩orientedSurfaceAgreement B C N M); rwa [hq0])
  have hfg : f=ᶠ[𝓝 (0 : Plane)]g := normal_graph_germ_coincidence hn hf hg hf0 hg0 hfc hgc
    (by filter_upwards [hfm,hgm] with y hfy hgy; exact hfy.2.2.trans hgy.2.2.symm) hcl
  have hPc : Tendsto (normalPlaneCoordinates (N a)) (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) := by
    simpa only [map_zero] using ((normalPlaneCoordinates (N a)).continuous.continuousAt (x := 0)).tendsto
  change ∀ᶠ y in 𝓝 (quotientMap a),(y∈B ↔ y∈C) ∧
    (y∈B → N (representative y)=M (representative y))
  rw [← shiftedQuotient_nhds a]
  change ∀ᶠ v in 𝓝 (0 : Cover),
    (quotientMap (a+v)∈B ↔ quotientMap (a+v)∈C) ∧
    (quotientMap (a+v)∈B → N (representative (quotientMap (a+v)))=M (representative (quotientMap (a+v))))
  filter_upwards [hfc,hgc,hPc.eventually hfg,hPc.eventually hfg.gradient,
    hPc.eventually hfm,hPc.eventually hgm] with v hvB hvC hvfg hvgrad hvN hvM
  have hgraphs : normalGraph (N a) f (normalPlaneCoordinates (N a) v)=
      normalGraph (N a) g (normalPlaneCoordinates (N a) v) := by
    simp only [normalGraph,hvfg]
  refine ⟨hvB.trans ((congrArg (fun z : Cover ↦ z=v) hgraphs).to_iff.trans hvC.symm),?_⟩
  intro hv
  rw [periodic_representative hpN,periodic_representative hpM]
  have hFv := hvB.mp hv
  have hGv := hgraphs.symm.trans hFv
  calc N (a+v)=graphSlopeNormal (N a) (gradient f (normalPlaneCoordinates (N a) v)) := by
        simpa only [hFv] using hvN.1
    _=graphSlopeNormal (N a) (gradient g (normalPlaneCoordinates (N a) v)) := congrArg _ hvgrad
    _=M (a+v) := by simpa only [hGv] using hvM.1.symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma preconnected_subset_of_relative_germ_closed {X : Type*} [TopologicalSpace X]
    {B O : Set X} (hB : IsPreconnected B) (hO : IsOpen O) (hne : (B∩O).Nonempty)
    (hc : closure (B∩O)∩B⊆O) : B⊆O := by
  let : PreconnectedSpace B := isPreconnected_iff_preconnectedSpace.mp hB
  let U : Set B := Subtype.val ⁻¹' O
  have hUo : IsOpen U := hO.preimage continuous_subtype_val
  have hUc : IsClosed U := isClosed_of_closure_subset (by
    intro x hx
    have hx' : (x : X)∈closure (B∩O) := closure_mono
      (by rintro y ⟨z,hz,rfl⟩; exact ⟨z.property,hz⟩) (closure_subtype.mp hx)
    exact hc ⟨hx',x.property⟩)
  have hUn : U.Nonempty := by obtain ⟨x,hxB,hxO⟩ := hne; exact ⟨⟨x,hxB⟩,hxO⟩
  have he := (show IsClopen U from ⟨hUc,hUo⟩).eq_univ hUn
  intro x hx
  exact show (⟨x,hx⟩ : B)∈U by rw [he]; trivial

lemma orientedSurfaceAgreement_symm {B C : Set Torus} {N M : Cover → Cover}
    {x : Torus} (hx : x∈orientedSurfaceAgreement B C N M) :
    x∈orientedSurfaceAgreement C B M N := by
  filter_upwards [hx] with y hy
  exact ⟨hy.1.symm,fun hyC ↦ (hy.2 (hy.1.mpr hyC)).symm⟩

end CubicTorus
end
end
end

end OAI
