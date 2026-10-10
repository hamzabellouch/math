import Mathlib
import OAI.Geometry.CubicTorus.Profiles.NormalizedCMCCharts

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalized_CMC_common_patch_curvature {B C : Set Torus}
    {N M : Cover → Cover} (hpN : ∀ m x,N (x+latticeVector m)=N x)
    (hpM : ∀ m x,M (x+latticeVector m)=M x)
    {H K : ℝ} (hBch : HasNormalizedCMCCharts B N H) (hCch : HasNormalizedCMCCharts C M K)
    {x : Torus} (hxB : x∈B) (hx : x∈orientedSurfaceAgreement B C N M) : H=K := by
  obtain ⟨a,rfl⟩ := quotientMap_surjective x
  have hxC := hx.self_of_nhds.1.mp hxB
  have hNM : N a=M a := by
    simpa only [periodic_representative hpN,periodic_representative hpM] using hx.self_of_nhds.2 hxB
  obtain ⟨hn,f,hf,hf0,_,hfm,_⟩ := hBch a hxB
  obtain ⟨_,g,hg,hg0,_,hgm,hgc⟩ := hCch a hxC
  rw [←hNM] at hgm hgc
  have hF0 : normalGraph (N a) f 0=0 := by
    change (normalPlaneLinearIsometry (N a)) 0+f 0 • N a=0
    rw [map_zero,hf0,zero_smul,add_zero]
  have hFt : Tendsto (normalGraph (N a) f) (𝓝 (0 : Plane)) (𝓝 (0 : Cover)) := by
    simpa only [hF0] using ((normalGraph_contDiff hf (n := N a)).continuous.continuousAt (x := 0)).tendsto
  have hq : Tendsto (fun y : Plane ↦ quotientMap (a+normalGraph (N a) f y))
      (𝓝 0) (𝓝 (quotientMap a)) := by
    have hc := (continuous_quotientMap.comp ( (continuous_const (y := a)).add (normalGraph_contDiff hf (n := N a)).continuous)).continuousAt (x := 0)
    simpa only [Function.comp_def,Pi.add_apply,hF0,add_zero] using hc.tendsto
  have hfg : f=ᶠ[𝓝 (0 : Plane)]g := by
    filter_upwards [hfm,hq.eventually hx,hFt.eventually hgc] with y hfy hxy hgy
    rw [normalPlaneCoordinates_graph hn] at hgy
    exact normalGraph_height_eq hn ((hgy.mp (hxy.1.mp hfy.2.1)).symm)
  have hc := planeCMC_germ hfg
  rw [hfm.self_of_nhds.2.2,hgm.self_of_nhds.2.2] at hc
  exact neg_injective hc

theorem CMC_surfaces_identity {B C : Set Torus} (hBc : IsClosed B) (hCc : IsClosed C)
    (hBconn : IsPreconnected B) (hCconn : IsPreconnected C)
    {N M : Cover → Cover} (hN : Continuous N) (hM : Continuous M)
    (hpN : ∀ m x,N (x+latticeVector m)=N x)
    (hpM : ∀ m x,M (x+latticeVector m)=M x)
    {H K : ℝ} (hBch : HasNormalizedCMCCharts B N H) (hCch : HasNormalizedCMCCharts C M K)
    (hpatch : (B∩orientedSurfaceAgreement B C N M).Nonempty) :
    B=C ∧ H=K ∧ ∀ x∈B,N (representative x)=M (representative x) := by
  obtain ⟨x,hxB,hxag⟩ := hpatch
  have hHK := normalized_CMC_common_patch_curvature hpN hpM hBch hCch hxB hxag
  subst K
  have hAB : B⊆orientedSurfaceAgreement B C N M :=
    preconnected_subset_of_relative_germ_closed hBconn (isOpen_orientedSurfaceAgreement _ _ _ _)
      ⟨x,hxB,hxag⟩ (fun _ hy ↦ orientedSurfaceAgreement_closed_at hCc hN hM hpN hpM hBch hCch hy.2 hy.1)
  have hxC := hxag.self_of_nhds.1.mp hxB
  have hAC : C⊆orientedSurfaceAgreement C B M N :=
    preconnected_subset_of_relative_germ_closed hCconn (isOpen_orientedSurfaceAgreement _ _ _ _)
      ⟨x,hxC,orientedSurfaceAgreement_symm hxag⟩
      (fun _ hy ↦ orientedSurfaceAgreement_closed_at hBc hM hN hpM hpN hCch hBch hy.2 hy.1)
  refine ⟨Subset.antisymm (fun y hy ↦ (hAB hy).self_of_nhds.1.mp hy)
    (fun y hy ↦ (hAC hy).self_of_nhds.1.mp hy),rfl,?_⟩
  exact fun y hy ↦ (hAB hy).self_of_nhds.2 hy

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma boundaryZeroGerm_homeomorph (e : Torus ≃ₜ Torus) (S : Set Torus) (F : Torus → ℝ) :
    boundaryZeroGerm (e ⁻¹' S) (F∘e)=e ⁻¹' boundaryZeroGerm S F := by
  ext x
  change (∀ᶠ y in 𝓝 x,e y∈S → F (e y)=0) ↔
    (∀ᶠ y in 𝓝 (e x),y∈S → F y=0)
  rw [←e.map_nhds_eq x]
  rfl

lemma boundaryZeroGerm_translation (a : Cover) (S : Set Torus) (f : smoothPeriodicScalars) :
    boundaryZeroGerm ((fun b ↦ b+quotientMap a) ⁻¹' S)
      (fun b ↦ (sibling_smoothScalarTranslate a f).val (representative b))=
      (fun b ↦ b+quotientMap a) ⁻¹' boundaryZeroGerm S (fun b ↦ f.val (representative b)) := by
  simp only [smoothScalarTranslate_descent]
  exact boundaryZeroGerm_homeomorph (Homeomorph.addRight (quotientMap a)) S
    (fun b ↦ f.val (representative b))

theorem isMinimizerAt_Jacobi_zero_germ_closed {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (haeN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hjN : ∀ w : Cover,∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ (directionalNormalScalar N hN hp w)) v=0)
    (f : smoothPeriodicScalars)
    (hjf : ∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ f) v=0)
    (x : Torus) (hx : x∈frontier (openRepresentative E))
    (hcl : x∈closure (frontier (openRepresentative E)∩
      boundaryZeroGerm (frontier (openRepresentative E)) (fun x ↦ f.val (representative x)))) :
    x∈boundaryZeroGerm (frontier (openRepresentative E)) (fun x ↦ f.val (representative x)) := by
  let a : Cover := representative x-cubeCenter
  have hshift : quotientMap cubeCenter+quotientMap a=x := by
    dsimp [a]
    rw [quotientMap_sub,quotientMap_representative]
    abel
  let E' : Set Torus := (fun b ↦ b+quotientMap a) ⁻¹' E
  let μ' := μ.map (translateNormal a)
  let N' := normalTranslateField a N
  let hN' := normalTranslateField_smooth a hN
  let hp' := normalTranslateField_periodic a hp
  let f' := sibling_smoothScalarTranslate a f
  have hE' : MeasurableSet E' := hE.preimage (measurable_id.add measurable_const)
  have hmin' : IsMinimizerAt V E' := isMinimizerAt_translation hmin (quotientMap a)
  have hμ' : IsNormalMeasure E' μ' := isNormalMeasure_translation hE hμ a
  have haeN' := normalTranslateField_ae μ a hN.continuous hp haeN
  have hS' : frontier (openRepresentative E')=(fun b ↦ b+quotientMap a) ⁻¹'
      frontier (openRepresentative E) := frontier_openRepresentative_translation hE _
  have hcenter : quotientMap cubeCenter∈frontier (openRepresentative E') := by
    rw [hS']
    change quotientMap cubeCenter+quotientMap a∈frontier (openRepresentative E)
    rwa [hshift]
  obtain ⟨c⟩ := isMinimizerAt_centeredJacobiChart hV hE' hmin' hcenter hμ' hN' hp' haeN'
  have hcl' : quotientMap cubeCenter∈closure (frontier (openRepresentative E')∩
      boundaryZeroGerm (frontier (openRepresentative E')) (fun b ↦ f'.val (representative b))) := by
    rw [hS',boundaryZeroGerm_translation,←preimage_inter]
    change quotientMap cubeCenter∈closure ((Homeomorph.addRight (quotientMap a)) ⁻¹' _)
    rw [←(Homeomorph.addRight (quotientMap a)).preimage_closure]
    change quotientMap cubeCenter+quotientMap a∈closure _
    rwa [hshift]
  have hz := c.zero_germ_closed hE' hμ' hN' hp' haeN' (surfaceCurvatureLp μ' N' hN') f'
    (normalTranslate_smooth_weakJacobi μ a hN hp f hjf) (by
      rw [normalTranslate_directional a hN hp]
      exact normalTranslate_smooth_weakJacobi μ a hN hp _ (hjN c.n)) hcl'
  rw [hS',boundaryZeroGerm_translation] at hz
  change quotientMap cubeCenter+quotientMap a∈boundaryZeroGerm _ _ at hz
  rwa [hshift] at hz

theorem isMinimizerAt_Jacobi_identity {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hconn : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (haeN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hjN : ∀ w : Cover,∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ (directionalNormalScalar N hN hp w)) v=0)
    (f : smoothPeriodicScalars)
    (hjf : ∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ f) v=0)
    (hpatch : (frontier (openRepresentative E)∩
      boundaryZeroGerm (frontier (openRepresentative E)) (fun x ↦ f.val (representative x))).Nonempty) :
    ∀ x∈frontier (openRepresentative E),f.val (representative x)=0 := by
  have hsub := preconnected_subset_of_relative_germ_closed hconn (boundaryZeroGerm_open _ _) hpatch
    (fun x hx ↦ isMinimizerAt_Jacobi_zero_germ_closed hV hE hmin hμ hN hp haeN hjN f hjf x hx.2 hx.1)
  exact fun x hx ↦ (hsub hx).self_of_nhds hx

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem CenteredJacobiChart.zero_germ_of_local_nonneg
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
    (hpos : ∀ᶠ x in 𝓝 (quotientMap cubeCenter),x∈frontier (openRepresentative E) →
      0≤f.val (representative x))
    (hz : f.val cubeCenter=0) :
    quotientMap cubeCenter∈boundaryZeroGerm (frontier (openRepresentative E))
      (fun x ↦ f.val (representative x)) := by
  let F : Plane → ℝ := fun y ↦ c.weight y*f.val (c.parameter y)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := c.weight_smooth.mul (f.property.1.comp c.parameter_smooth)
  have hpos' : ∀ᶠ y in 𝓝 (0 : Plane),0≤f.val (c.parameter y) := by
    have ht : Tendsto (fun y ↦ quotientMap (c.parameter y)) (𝓝 (0 : Plane))
        (𝓝 (quotientMap cubeCenter)) := by
      have ht := (show Continuous (fun y : Plane ↦ quotientMap (c.parameter y)) from
        continuous_quotientMap.comp c.parameter_smooth.continuous).tendsto (0 : Plane)
      rw [c.parameter_zero] at ht
      exact ht
    filter_upwards [ht.eventually hpos,Metric.ball_mem_nhds (0 : Plane) c.r_pos] with y hy hr
    simpa only [periodic_representative f.property.2] using hy (c.boundary_disk y (Metric.ball_subset_closedBall hr))
  obtain ⟨s,hs,hsp⟩ := Metric.eventually_nhds_iff.mp hpos'
  let r := min s (c.r/2)
  have hr : 0<r := lt_min hs (half_pos c.r_pos)
  have hrr : r≤c.r := (min_le_right _ _).trans (by linarith [c.r_pos])
  have hL := c.classical_ground_state hE hμ hN hp haeN q f hjf hjw
  have hzero := cmc_strong_minimum (plane_gradient_contDiff c.smooth) hF
    Metric.isOpen_ball (convex_ball (0 : Plane) r).isPreconnected
    (fun y hy ↦ (c.slope_disk y (Metric.ball_subset_closedBall
      (Metric.ball_subset_ball hrr hy))).trans (by norm_num : (1/4:ℝ)≤1))
    (fun y hy ↦ mul_nonneg (cmcWeight_pos _).le (hsp (lt_of_lt_of_le hy (min_le_left _ _))))
    (fun y hy ↦ hL y (Metric.ball_subset_ball (min_le_right _ _) hy))
    (Metric.mem_ball_self hr) (show F 0=0 by simp [F,c.parameter_zero,hz])
  apply c.zero_trace_germ f
  filter_upwards [Metric.ball_mem_nhds (0 : Plane) hr] with y hy
  exact (mul_eq_zero.mp (hzero y hy)).resolve_left (cmcWeight_pos _).ne'

theorem isMinimizerAt_Jacobi_strong_minimum {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hconn : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (haeN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hjN : ∀ w : Cover,∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ (directionalNormalScalar N hN hp w)) v=0)
    (f : smoothPeriodicScalars)
    (hjf : ∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ f) v=0)
    {x : Torus} (hx : x∈frontier (openRepresentative E))
    (hpos : ∀ᶠ y in 𝓝 x,y∈frontier (openRepresentative E) → 0≤f.val (representative y))
    (hz : f.val (representative x)=0) :
    ∀ y∈frontier (openRepresentative E),f.val (representative y)=0 := by
  let a : Cover := representative x-cubeCenter
  have hshift : quotientMap cubeCenter+quotientMap a=x := by
    dsimp [a]
    rw [quotientMap_sub,quotientMap_representative]
    abel
  let E' : Set Torus := (fun b ↦ b+quotientMap a) ⁻¹' E
  let μ' := μ.map (translateNormal a)
  let N' := normalTranslateField a N
  let hN' := normalTranslateField_smooth a hN
  let hp' := normalTranslateField_periodic a hp
  let f' := sibling_smoothScalarTranslate a f
  have hE' : MeasurableSet E' := hE.preimage (measurable_id.add measurable_const)
  have hmin' : IsMinimizerAt V E' := isMinimizerAt_translation hmin (quotientMap a)
  have hμ' : IsNormalMeasure E' μ' := isNormalMeasure_translation hE hμ a
  have haeN' := normalTranslateField_ae μ a hN.continuous hp haeN
  have hS' : frontier (openRepresentative E')=(fun b ↦ b+quotientMap a) ⁻¹'
      frontier (openRepresentative E) := frontier_openRepresentative_translation hE _
  have hcenter : quotientMap cubeCenter∈frontier (openRepresentative E') := by
    rw [hS']
    change quotientMap cubeCenter+quotientMap a∈frontier (openRepresentative E)
    rwa [hshift]
  obtain ⟨c⟩ := isMinimizerAt_centeredJacobiChart hV hE' hmin' hcenter hμ' hN' hp' haeN'
  have hpos' : ∀ᶠ b in 𝓝 (quotientMap cubeCenter),b∈frontier (openRepresentative E') →
      0≤f'.val (representative b) := by
    have ht : Tendsto (fun b : Torus ↦ b+quotientMap a) (𝓝 (quotientMap cubeCenter)) (𝓝 x) := by
      simpa only [hshift] using
        (show Continuous (fun b : Torus ↦ b+quotientMap a) from continuous_id.add continuous_const).continuousAt.tendsto (x := quotientMap cubeCenter)
    filter_upwards [ht.eventually hpos] with b hb hB
    rw [hS'] at hB
    simpa only [f',smoothScalarTranslate_descent] using hb hB
  have hz' : f'.val cubeCenter=0 := by
    have he := smoothScalarTranslate_descent a f (quotientMap cubeCenter)
    rw [periodic_representative f'.property.2,hshift] at he
    exact he.trans hz
  have hg := c.zero_germ_of_local_nonneg hE' hμ' hN' hp' haeN' (surfaceCurvatureLp μ' N' hN') f'
    (normalTranslate_smooth_weakJacobi μ a hN hp f hjf) (by
      rw [normalTranslate_directional a hN hp]
      exact normalTranslate_smooth_weakJacobi μ a hN hp _ (hjN c.n)) hpos' hz'
  rw [hS',boundaryZeroGerm_translation] at hg
  change quotientMap cubeCenter+quotientMap a∈boundaryZeroGerm _ _ at hg
  rw [hshift] at hg
  exact isMinimizerAt_Jacobi_identity hV hE hmin hconn hμ hN hp haeN hjN f hjf ⟨x,hx,hg⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_center_normal_unique {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E)) :
    ∃ w : Cover,∀ (μ : FiniteMeasure NormalBundle),IsNormalMeasure E μ →
      ∀ (N : Cover → Cover),ContDiff ℝ (⊤ : ℕ∞) N →
      (∀ m x,N (x+latticeVector m)=N x) →
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) → N cubeCenter=w := by
  obtain ⟨n,g,r,H,hn,hr,hg,hg0,hgc,hi,hcover,_,_⟩ :=
    isMinimizerAt_smooth_CMC hV hE hmin (quotientMap cubeCenter) hcenter
  obtain ⟨f,hf,hfg⟩ := smooth_graph_extension hr hgc
  have hcover' (x : Cover) (hx : x∈Metric.ball (0 : Cover) (r/2)) :
      quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n x)=x := by
    rw [quotientMap_add]
    exact hcover x ((Metric.ball_subset_ball (by linarith)) hx)
  obtain ⟨R,ρ,U,hRr,_,_,_,hR,hρ,hgC,hU,hρU,hUR,hUO,_,hphase⟩ :=
    actual_centered_graph_phase_patch hV hE hmin hcenter hn (by linarith : 0<r/2)
      hg hg0 ((hgc.of_le (by simp)).mono (Metric.ball_subset_ball (by linarith))) hcover'
  let φ := radialHeightCutoff cubeCenter ρ
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := radialDensityWeight_contDiff _ _ _
  have hsφ : HasCompactSupport φ := radialDensityWeight_hasCompactSupport (by positivity) (by positivity)
  have hφs : tsupport φ⊆Metric.closedBall cubeCenter (2*ρ) :=
    radialDensityWeight_tsupport (by positivity) (by positivity)
  have hφU := hφs.trans hρU
  have hφO := hφU.trans hUO
  have hφR := hφU.trans (hUR.trans Metric.ball_subset_closedBall)
  have hφb (x : Cover) : φ x∈Icc 0 1 :=
    ⟨radialDensityWeight_nonneg _ _ _ _,radialDensityWeight_le_one _ _ _ _⟩
  have hdc (y : Plane) (hy : y∈Metric.closedBall (0 : Plane) R) : ContinuousAt (fderiv ℝ g) y :=
    (hgC y hy).continuousAt_fderiv (by norm_num)
  have hNfg (x : Cover) (hx : x∈tsupport φ) :
      graphUnitNormalExtension cubeCenter n f x=graphUnitNormalExtension cubeCenter n g x := by
    have hpp : normalPlaneCoordinates n (x-cubeCenter)∈Metric.ball (0 : Plane) (r/2) := by
      rw [Metric.mem_ball,dist_zero_right]
      have hnorm : ‖x-cubeCenter‖<R := by
        simpa only [Metric.mem_ball,dist_eq_norm] using hUR (hφU hx)
      exact (normalPlaneCoordinates_norm_le _ _).trans_lt (hnorm.trans hRr)
    have he : f=ᶠ[𝓝 (normalPlaneCoordinates n (x-cubeCenter))]g := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hpp] with y hy
      exact hfg hy
    simp only [graphUnitNormalExtension,gradient,he.fderiv_eq]
  have hsign : ∃ σ : ℝ,(σ=1 ∨ σ= -1) ∧
      ∀ (μ : FiniteMeasure NormalBundle),IsNormalMeasure E μ →
      ∀ᵐ z ∂(μ : Measure NormalBundle),0<φ z.1 →
        σ • graphUnitNormalExtension cubeCenter n f z.1=(z.2 : Cover) := by
    rcases hphase with hphase|hphase
    · have hh : ∀ᵐ x : Cover ∂volume,x∈U →
          (quotientMap x∈E ↔ ⟪n,x-cubeCenter⟫<graphHeightExtension cubeCenter n g x) := by
        simpa only [graphSignedHeight,sub_neg] using hphase
      refine ⟨1,Or.inl rfl,?_⟩
      intro μ hμ
      filter_upwards [normalMeasure_graph_normal_ae hE hμ cubeCenter hn hg hdc hh
        hφ hsφ hφU hφO hφR hφb] with z hz hpos
      rw [one_smul,hNfg _ (subset_tsupport _ hpos.ne')]
      exact (hz hpos).symm
    · have hh : ∀ᵐ x : Cover ∂volume,x∈U →
          (x∈quotientMap ⁻¹' E ↔ graphHeightExtension cubeCenter n g x<⟪n,x-cubeCenter⟫) := by
        simpa only [graphSignedHeight,sub_pos,mem_preimage] using hphase
      have hh' := graph_superlevel_compl_ae cubeCenter hn hg.continuous hh
      refine ⟨-1,Or.inr rfl,?_⟩
      intro μ hμ
      have hh'' := normalMeasure_graph_normal_ae hE.compl (isNormalMeasure_compl hE hμ)
        cubeCenter hn hg hdc hh' hφ hsφ hφU hφO hφR hφb
      have hm : ∀ᵐ z ∂(μ : Measure NormalBundle),0<φ z.1 →
          -(z.2 : Cover)=graphUnitNormalExtension cubeCenter n g z.1 :=
        ae_of_ae_map continuous_reverseNormal.measurable.aemeasurable hh''
      filter_upwards [hm] with z hz hpos
      rw [neg_one_smul,hNfg _ (subset_tsupport _ hpos.ne'),← hz hpos,neg_neg]
  obtain ⟨σ,hσ,hσae⟩ := hsign
  refine ⟨σ • graphUnitNormalExtension cubeCenter n f cubeCenter,?_⟩
  intro μ hμ N hN hp hae
  let F : Cover → Cover := fun x ↦ φ x • (N x-σ • graphUnitNormalExtension cubeCenter n f x)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := hφ.smul
    (hN.sub ((graphUnitNormalExtension_contDiff _ hn hf).const_smul σ))
  have hsF : HasCompactSupport F := hsφ.smul_right
  have hFO : tsupport F⊆{x | ∀ i,0<x i ∧ x i<1} :=
    (tsupport_smul_subset_left _ _).trans hφO
  have he := latticePeriodize_eventuallyEq hsF hFO
    (show ∀ i,0≤cubeCenter i ∧ cubeCenter i≤1 by intro i; norm_num [cubeCenter])
  have hz : ∀ᵐ z ∂(μ : Measure NormalBundle),latticePeriodize F z.1=(0 : Cover) := by
    filter_upwards [hae,hσae μ hμ] with z hz hloc
    rw [(latticePeriodize_eventuallyEq hsF hFO (compactCell_coordinates z.1)).eq_of_nhds]
    change φ z.1 • (N z.1-σ • graphUnitNormalExtension cubeCenter n f z.1)=0
    by_cases hpos : 0<φ z.1
    · rw [hz,hloc hpos,sub_self,smul_zero]
    · have hzφ : φ z.1=0 := le_antisymm (le_of_not_gt hpos) (hφb z.1).1
      rw [hzφ,zero_smul]
  have hb (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
      latticePeriodize F x=0 :=
    isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ
      (latticePeriodize_contDiff hF hsF).continuous continuous_const
      (latticePeriodize_periodic F) (fun _ _ ↦ rfl) hz x hx
  have hzero := hb cubeCenter hcenter
  rw [he.self_of_nhds] at hzero
  change φ cubeCenter • (N cubeCenter-σ • graphUnitNormalExtension cubeCenter n f cubeCenter)=0 at hzero
  have hone : φ cubeCenter=1 := radialHeightCutoff_one hρ (by simp [hρ.le])
  rw [hone,one_smul] at hzero
  exact sub_eq_zero.mp hzero

theorem isMinimizerAt_normal_unique {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
    ∃ w : Cover,∀ (μ : FiniteMeasure NormalBundle),IsNormalMeasure E μ →
      ∀ (N : Cover → Cover),ContDiff ℝ (⊤ : ℕ∞) N →
      (∀ m x,N (x+latticeVector m)=N x) →
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) → N x=w := by
  let a := x-cubeCenter
  let E' := (fun z : Torus ↦ z+quotientMap a) ⁻¹' E
  have hE' : MeasurableSet E' := (continuous_add_const _).measurable hE
  have hmin' : IsMinimizerAt V E' := isMinimizerAt_translation hmin _
  have hc : quotientMap cubeCenter∈frontier (openRepresentative E') := by
    rw [frontier_openRepresentative_translation hE]
    change quotientMap cubeCenter+quotientMap a∈frontier (openRepresentative E)
    rw [←quotientMap_add,show cubeCenter+a=x by dsimp [a]; abel]
    exact hx
  obtain ⟨w,hw⟩ := isMinimizerAt_center_normal_unique hV hE' hmin' hc
  refine ⟨w,?_⟩
  intro μ hμ N hN hp hae
  let N' : Cover → Cover := fun y ↦ N (y+a)
  have hN' : ContDiff ℝ (⊤ : ℕ∞) N' := hN.comp (contDiff_id.add contDiff_const)
  have hp' : ∀ m y,N' (y+latticeVector m)=N' y := by
    intro m y
    change N ((y+latticeVector m)+a)=N (y+a)
    rw [add_right_comm,hp]
  have hae' : ∀ᵐ z ∂((μ.map (translateNormal a)) : Measure NormalBundle),N' z.1=(z.2 : Cover) := by
    change ∀ᵐ z ∂Measure.map (translateNormal a) (μ : Measure NormalBundle),N' z.1=(z.2 : Cover)
    apply (ae_map_iff (measurable_translateNormal a).aemeasurable
      (isClosed_eq (hN'.continuous.comp normalEmbedding_continuous.fst) continuous_normalUnit).measurableSet).mpr
    filter_upwards [hae] with z hz
    change N' (translateNormal a z).1=(z.2 : Cover)
    rw [translateNormal_periodic_eval hp']
    change N (((z.1 : Cover)-a)+a)=(z.2 : Cover)
    simpa only [sub_add_cancel] using hz
  have hh := hw (μ.map (translateNormal a)) (isNormalMeasure_translation hE hμ a)
    N' hN' hp' hae'
  change N (cubeCenter+a)=w at hh
  simpa only [show cubeCenter+a=x by dsimp [a]; abel] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def sibling_reflectNormal (z : NormalBundle) : NormalBundle :=
  (cubeRepresentative (torusFirstReflection (quotientMap z.1)),
    ⟨firstReflection (z.2 : Cover),by rw [LinearIsometryEquiv.norm_map,z.2.property]⟩)

lemma sibling_measurable_reflectNormal : Measurable sibling_reflectNormal := by
  apply Measurable.prodMk
  · exact measurable_cubeRepresentative.comp (torusFirstReflection.continuous.measurable.comp
      (measurable_quotientMap.comp (measurable_subtype_coe.comp measurable_fst)))
  · exact (firstReflection.continuous.measurable.comp
      (measurable_subtype_coe.comp measurable_snd)).subtype_mk

lemma sibling_reflectNormal_periodic_eval {Y : Type*} {F : Cover → Y}
    (hp : ∀ m x,F (x+latticeVector m)=F x) (z : NormalBundle) :
    F (sibling_reflectNormal z).1=F (firstReflection z.1) := by
  change F (representative (torusFirstReflection (quotientMap z.1)))=_
  rw [←firstReflection_quotient,periodic_representative hp]

theorem isNormalMeasure_firstReflection {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    IsNormalMeasure (torusFirstReflection ⁻¹' E) (μ.map sibling_reflectNormal) := by
  constructor
  · have hm : ((μ.map sibling_reflectNormal).mass : ℝ)=(μ.mass : ℝ) := by
      have hh := congrArg ENNReal.toReal (Measure.map_apply sibling_measurable_reflectNormal
        MeasurableSet.univ (μ := (μ : Measure NormalBundle)))
      simpa only [preimage_univ,FiniteMeasure.mass,FiniteMeasure.coeFn_def,
        FiniteMeasure.toMeasure_map,Measure.real,ENNReal.toReal] using hh
    rw [hm,hμ.1,perimeter_firstReflection hE]
  · intro F hF
    change (∫ z,normalTest F hF.1.continuous z
      ∂Measure.map sibling_reflectNormal (μ : Measure NormalBundle))=_
    rw [integral_map sibling_measurable_reflectNormal.aemeasurable
      (normalTest F hF.1.continuous).continuous.aestronglyMeasurable,
      flux_firstReflection hF hE,←hμ.2 _ (reflectionPullback_admissible hF)]
    apply integral_congr_ae
    exact Eventually.of_forall fun z ↦ by
      change ⟪firstReflection (z.2 : Cover),F (sibling_reflectNormal z).1⟫=
        ⟪(z.2 : Cover),firstReflection (F (firstReflection z.1))⟫
      rw [sibling_reflectNormal_periodic_eval hF.2.1]
      simpa only [firstReflection_involutive] using
        (firstReflection.inner_map_map (z.2 : Cover) (firstReflection (F (firstReflection z.1))))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graph_tangent_of_graph_containment {n m : Cover} (hm : ‖m‖=1)
    {f g : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hf0 : f 0=0)
    (he : ∀ᶠ y in 𝓝 (0 : Plane),
      normalGraph m g (normalPlaneCoordinates m (normalGraph n f y))=normalGraph n f y)
    (w : Plane) : ⟪graphSlopeNormal m (gradient g 0),fderiv ℝ (normalGraph n f) 0 w⟫=0 := by
  have hF := normalGraph_contDiff hf (n := n)
  have hG := normalGraph_contDiff hg (n := m)
  have hF0 : normalGraph n f 0=0 := by
    change (normalPlaneLinearIsometry n) 0+f 0 • n=0
    rw [map_zero,hf0,zero_smul,add_zero]
  have hdP := (normalPlaneCoordinates m).hasFDerivAt.comp 0 (hF.differentiable (by simp) 0).hasFDerivAt
  have hdG := ((hG.differentiable (by simp) _).hasFDerivAt.comp 0 hdP).fderiv
  have he' : (fun y ↦ normalGraph m g (normalPlaneCoordinates m (normalGraph n f y)))=ᶠ[𝓝 (0 : Plane)]normalGraph n f := he
  have hd := he'.fderiv_eq (𝕜 := ℝ)
  change fderiv ℝ (normalGraph m g ∘ normalPlaneCoordinates m ∘ normalGraph n f) 0=_ at hd
  rw [hdG] at hd
  change (fderiv ℝ (normalGraph m g) (normalPlaneCoordinates m (normalGraph n f 0))).comp
    ((normalPlaneCoordinates m).comp (fderiv ℝ (normalGraph n f) 0))=fderiv ℝ (normalGraph n f) 0 at hd
  rw [hF0,map_zero] at hd
  rw [←hd,ContinuousLinearMap.comp_apply]
  exact normalGraph_tangent_normal hm hg 0 _

lemma graphSlopeNormal_gradient_zero {n : Cover} (hn : ‖n‖=1) : graphSlopeNormal n (0 : Plane)=n := by
  rw [graphSlopeNormal_weight hn]
  change (cmcWeight 0)⁻¹ • (n-(normalPlaneLinearIsometry n) 0)=n
  simp [cmcWeight]

theorem normalized_CMC_common_germ_normals {B C : Set Torus}
    {N M : Cover → Cover} {H K : ℝ}
    (hBch : HasNormalizedCMCCharts B N H) (hCch : HasNormalizedCMCCharts C M K)
    {a : Cover} (ha : quotientMap a∈B)
    (he : ∀ᶠ z in 𝓝 (quotientMap a),z∈B ↔ z∈C) : N a=M a ∨ N a= -M a := by
  obtain ⟨hn,f,hf,hf0,hdf0,hfm,_⟩ := hBch a ha
  obtain ⟨hm,g,hg,hg0,hdg0,hgm,hgc⟩ := hCch a (he.self_of_nhds.mp ha)
  have hF0 : normalGraph (N a) f 0=0 := by
    change (normalPlaneLinearIsometry (N a)) 0+f 0 • N a=0
    rw [map_zero,hf0,zero_smul,add_zero]
  have hFt : Tendsto (normalGraph (N a) f) (𝓝 (0 : Plane)) (𝓝 (0 : Cover)) := by
    simpa only [hF0] using ((normalGraph_contDiff hf (n := N a)).continuous.continuousAt (x := 0)).tendsto
  have hq : Tendsto (fun y : Plane ↦ quotientMap (a+normalGraph (N a) f y))
      (𝓝 0) (𝓝 (quotientMap a)) := by
    have hc : Continuous (fun y : Plane ↦ quotientMap (a+normalGraph (N a) f y)) :=
      continuous_quotientMap.comp (continuous_const.add (normalGraph_contDiff hf).continuous)
    simpa only [hF0,add_zero] using (hc.continuousAt (x := 0)).tendsto
  have hcontain : ∀ᶠ y in 𝓝 (0 : Plane),
      normalGraph (M a) g (normalPlaneCoordinates (M a) (normalGraph (N a) f y))=normalGraph (N a) f y := by
    filter_upwards [hfm,hq.eventually he,hFt.eventually hgc] with y hfy hey hgy
    exact hgy.mp (hey.mp hfy.2.1)
  have ht (w : Plane) : ⟪M a,fderiv ℝ (normalGraph (N a) f) 0 w⟫=0 := by
    simpa only [hdg0,graphSlopeNormal_gradient_zero hm] using
      graph_tangent_of_graph_containment hm hf hg hf0 hcontain w
  have hcol := graph_normal_tangent_vector_eq hn hf 0 ht
  rw [hdf0,graphSlopeNormal_gradient_zero hn] at hcol
  have hnorm := congrArg norm hcol
  rw [hm,norm_smul,Real.norm_eq_abs,hn,mul_one] at hnorm
  rcases (abs_eq (by norm_num : (0 : ℝ)≤1)).mp hnorm.symm with hplus|hminus
  · rw [hplus,one_smul] at hcol
    exact Or.inl hcol.symm
  · rw [hminus,neg_one_smul] at hcol
    exact Or.inr (by rw [hcol,neg_neg])

theorem normalized_CMC_common_germ_oriented {B C : Set Torus}
    {N M : Cover → Cover} (hN : Continuous N) (hM : Continuous M)
    (hpN : ∀ m x,N (x+latticeVector m)=N x)
    (hpM : ∀ m x,M (x+latticeVector m)=M x)
    {H K : ℝ} (hBch : HasNormalizedCMCCharts B N H) (hCch : HasNormalizedCMCCharts C M K)
    {x : Torus} (hx : x∈B) (he : ∀ᶠ z in 𝓝 x,z∈B ↔ z∈C)
    (hNM : N (representative x)=M (representative x)) :
    x∈orientedSurfaceAgreement B C N M := by
  have hn : ‖N (representative x)‖=1 := (hBch _ (by simpa only [quotientMap_representative] using hx)).1
  have hc : Continuous (fun z : Torus ↦ ⟪N (representative z),M (representative z)⟫) :=
    (continuous_periodic_descent hN hpN).inner (continuous_periodic_descent hM hpM)
  have hpos : ∀ᶠ z in 𝓝 x,0<⟪N (representative z),M (representative z)⟫ := by
    apply hc.continuousAt.eventually (lt_mem_nhds ?_)
    change 0<⟪N (representative x),M (representative x)⟫
    rw [←hNM,real_inner_self_eq_norm_sq,hn,one_pow]; norm_num
  filter_upwards [he,he.eventually_nhds,hpos] with z hze hzeg hzpos
  refine ⟨hze,fun hzB ↦ ?_⟩
  have hzB' : quotientMap (representative z)∈B := by simpa only [quotientMap_representative] using hzB
  rcases normalized_CMC_common_germ_normals hBch hCch hzB'
    (by simpa only [quotientMap_representative] using hzeg) with hsame|hop
  · exact hsame
  · have hm := (hCch (representative z) (by simpa only [quotientMap_representative] using hze.mp hzB)).1
    rw [hop,inner_neg_left,real_inner_self_eq_norm_sq,hm,one_pow] at hzpos
    linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem HasNormalizedCMCCharts.neg {B : Set Torus} {N : Cover → Cover} {H : ℝ}
    (hch : HasNormalizedCMCCharts B N H) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hbd : ∀ a : Cover,quotientMap a∈B →
      (∀ᶠ v in 𝓝 a,‖N v‖=1) ∧ divergence N a=H) :
    HasNormalizedCMCCharts B (fun x ↦ -N x) (-H) := by
  intro a ha
  obtain ⟨hn,f,hf,hf0,hdf0,hfm,hfc⟩ := hch a ha
  have hm : ‖-N a‖=1 := by simpa only [norm_neg] using hn
  have ht : ⟪graphSlopeNormal (N a) (gradient f 0),-N a⟫≠0 := by
    rw [hdf0,graphSlopeNormal_gradient_zero hn,inner_neg_right,real_inner_self_eq_norm_sq,hn,one_pow]
    norm_num
  obtain ⟨g,I,hg,hg0,hIc,hI0,hgf,hcov⟩ := sibling_normalGraph_regraph hn hm hf hf0 ht
  have hnmatch : ∀ᶠ y in 𝓝 (0 : Plane),-N (a+normalGraph (N a) f y)=
      (-1 : ℝ) • graphSlopeNormal (N a) (gradient f y) := by
    filter_upwards [hfm] with y hy
    rw [hy.1,neg_one_smul]
  have hnorm := sibling_normalGraph_regraph_normal hn hm hf hg hf0 hg0 hIc hI0 hgf hN.continuous.neg
    rfl (Or.inr rfl) hnmatch
  have hi : Tendsto I (𝓝 (0 : Plane)) (𝓝 (0 : Plane)) := by simpa only [hI0] using hIc.tendsto
  have hmem : ∀ᶠ y in 𝓝 (0 : Plane),quotientMap (a+normalGraph (-N a) g y)∈B := by
    filter_upwards [hgf,hi.eventually hfm] with y hy hmy
    rw [hy]; exact hmy.2.1
  refine ⟨hm,g,hg,hg0,hnorm.1,?_,?_⟩
  · filter_upwards [hnorm.2,hmem,hnorm.2.eventually_nhds] with y hy hby hny
    refine ⟨hy,hby,?_⟩
    have hny' : ∀ᶠ z in 𝓝 y,-N (a+normalGraph (-N a) g z)=
        (1 : ℝ) • graphSlopeNormal (-N a) (gradient g z) := by simpa only [one_smul,Pi.neg_apply] using hny
    have hd := graph_normal_extension_divergence a hm hg y (Or.inl rfl) hN.neg
      (by simpa only [norm_neg] using (hbd _ hby).1) hny'
    rw [divergence_neg,(hbd _ hby).2] at hd
    change -H= -(1 : ℝ)*planeCMC g y at hd
    linarith
  · filter_upwards [hfc,hcov] with v hv hc
    exact hv.trans hc.symm

theorem CMC_surfaces_unoriented_identity {B C : Set Torus} (hBc : IsClosed B) (hCc : IsClosed C)
    (hBconn : IsPreconnected B) (hCconn : IsPreconnected C)
    {N M : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hM : ContDiff ℝ (⊤ : ℕ∞) M)
    (hpN : ∀ m x,N (x+latticeVector m)=N x)
    (hpM : ∀ m x,M (x+latticeVector m)=M x)
    {H K : ℝ} (hBch : HasNormalizedCMCCharts B N H) (hCch : HasNormalizedCMCCharts C M K)
    (hMbd : ∀ a : Cover,quotientMap a∈C →
      (∀ᶠ v in 𝓝 a,‖M v‖=1) ∧ divergence M a=K)
    (hpatch : ∃ x∈B,∀ᶠ z in 𝓝 x,z∈B ↔ z∈C) :
    B=C ∧ ((H=K ∧ ∀ x∈B,N (representative x)=M (representative x)) ∨
      (H= -K ∧ ∀ x∈B,N (representative x)= -M (representative x))) := by
  obtain ⟨x,hx,hxe⟩ := hpatch
  have hx' : quotientMap (representative x)∈B := by simpa only [quotientMap_representative] using hx
  have hxg : ∀ᶠ z in 𝓝 (quotientMap (representative x)),z∈B ↔ z∈C := by
    simpa only [quotientMap_representative] using hxe
  rcases normalized_CMC_common_germ_normals hBch hCch hx' hxg with hsame|hop
  · have hag := normalized_CMC_common_germ_oriented hN.continuous hM.continuous hpN hpM hBch hCch hx hxe hsame
    obtain ⟨he,hHK,hNM⟩ := CMC_surfaces_identity hBc hCc hBconn hCconn hN.continuous hM.continuous
      hpN hpM hBch hCch ⟨x,hx,hag⟩
    exact ⟨he,Or.inl ⟨hHK,hNM⟩⟩
  · have hneg := hCch.neg hM hMbd
    have hnegp : ∀ m x,-M (x+latticeVector m)= -M x := fun m x ↦ congrArg Neg.neg (hpM m x)
    have hag := normalized_CMC_common_germ_oriented hN.continuous hM.continuous.neg hpN hnegp hBch hneg hx hxe hop
    obtain ⟨he,hHK,hNM⟩ := CMC_surfaces_identity hBc hCc hBconn hCconn hN.continuous hM.continuous.neg
      hpN hnegp hBch hneg ⟨x,hx,hag⟩
    exact ⟨he,Or.inr ⟨hHK,hNM⟩⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem CMC_surface_oriented_subset {B C : Set Torus} (hCc : IsClosed C)
    (hBconn : IsPreconnected B)
    {N M : Cover → Cover} (hN : Continuous N) (hM : Continuous M)
    (hpN : ∀ m x,N (x+latticeVector m)=N x)
    (hpM : ∀ m x,M (x+latticeVector m)=M x)
    {H K : ℝ} (hBch : HasNormalizedCMCCharts B N H) (hCch : HasNormalizedCMCCharts C M K)
    (hpatch : (B∩orientedSurfaceAgreement B C N M).Nonempty) :
    B⊆orientedSurfaceAgreement B C N M ∧ H=K := by
  obtain ⟨x,hx,hag⟩ := hpatch
  have he := normalized_CMC_common_patch_curvature hpN hpM hBch hCch hx hag
  subst K
  exact ⟨preconnected_subset_of_relative_germ_closed hBconn (isOpen_orientedSurfaceAgreement _ _ _ _)
    ⟨x,hx,hag⟩ (fun _ hy ↦ orientedSurfaceAgreement_closed_at hCc hN hM hpN hpM hBch hCch hy.2 hy.1),rfl⟩

theorem CMC_surface_unoriented_subset {B C : Set Torus} (hCc : IsClosed C)
    (hBconn : IsPreconnected B)
    {N M : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hM : ContDiff ℝ (⊤ : ℕ∞) M)
    (hpN : ∀ m x,N (x+latticeVector m)=N x)
    (hpM : ∀ m x,M (x+latticeVector m)=M x)
    {H K : ℝ} (hBch : HasNormalizedCMCCharts B N H) (hCch : HasNormalizedCMCCharts C M K)
    (hMbd : ∀ a : Cover,quotientMap a∈C →
      (∀ᶠ v in 𝓝 a,‖M v‖=1) ∧ divergence M a=K)
    (hpatch : ∃ x∈B,∀ᶠ z in 𝓝 x,z∈B ↔ z∈C) :
    ∀ x∈B,∀ᶠ z in 𝓝 x,z∈B ↔ z∈C := by
  obtain ⟨x,hx,hxe⟩ := hpatch
  have hx' : quotientMap (representative x)∈B := by simpa only [quotientMap_representative] using hx
  have hxg : ∀ᶠ z in 𝓝 (quotientMap (representative x)),z∈B ↔ z∈C := by
    simpa only [quotientMap_representative] using hxe
  rcases normalized_CMC_common_germ_normals hBch hCch hx' hxg with hsame|hop
  · have hag := normalized_CMC_common_germ_oriented hN.continuous hM.continuous hpN hpM hBch hCch hx hxe hsame
    have he := CMC_surface_oriented_subset hCc hBconn hN.continuous hM.continuous hpN hpM hBch hCch ⟨x,hx,hag⟩
    exact fun y hy ↦ (he.1 hy).mono (fun _ h ↦ h.1)
  · have hneg := hCch.neg hM hMbd
    have hnegp : ∀ m x,-M (x+latticeVector m)= -M x := fun m x ↦ congrArg Neg.neg (hpM m x)
    have hag := normalized_CMC_common_germ_oriented hN.continuous hM.continuous.neg hpN hnegp hBch hneg hx hxe hop
    have he := CMC_surface_oriented_subset hCc hBconn hN.continuous hM.continuous.neg hpN hnegp hBch hneg ⟨x,hx,hag⟩
    exact fun y hy ↦ (he.1 hy).mono (fun _ h ↦ h.1)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_lifted_boundary_global {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) (a : Cover) :
    a∈coverEssentialBoundary (quotientMap ⁻¹' E) ↔
      quotientMap a∈frontier (openRepresentative E) := by
  let b := a-cubeCenter
  let F := (fun z : Torus ↦ z+quotientMap b) ⁻¹' E
  have hF : MeasurableSet F := hE.preimage (continuous_id.add continuous_const).measurable
  have hminF := isMinimizerAt_translation hmin (quotientMap b)
  have hcent := isMinimizerAt_lifted_boundary hV hF hminF (x := cubeCenter) (by intro i; norm_num [cubeCenter])
  have he : quotientMap ⁻¹' F=(Homeomorph.addRight b) ⁻¹' (quotientMap ⁻¹' E) := by
    ext x
    change quotientMap x+quotientMap b∈E ↔ quotientMap (x+b)∈E
    rw [quotientMap_add]
  rw [he,cover_boundary_measurePreserving_homeomorph (Homeomorph.addRight b)
    (measurePreserving_add_right volume b),frontier_openRepresentative_translation hE] at hcent
  have hb : cubeCenter+b=a := by dsimp [b]; abel
  change cubeCenter+b∈coverEssentialBoundary (quotientMap ⁻¹' E) ↔
    quotientMap cubeCenter+quotientMap b∈frontier (openRepresentative E) at hcent
  rw [←quotientMap_add,hb] at hcent
  exact hcent

lemma lifted_ae_eq_torus {E F : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (h : quotientMap ⁻¹' E=ᵐ[volume]quotientMap ⁻¹' F) : E=ᵐ[torusVolume]F := by
  have hr : ∀ᵐ x ∂volume.restrict fundamentalCube,quotientMap x∈E ↔ quotientMap x∈F := by
    filter_upwards [ae_restrict_of_ae h] with x hx
    exact Iff.of_eq hx
  have hm : MeasurableSet {x : Torus | x∈E ↔ x∈F} := by measurability
  have ht := (ae_map_iff measurable_quotientMap.aemeasurable hm).mpr hr
  change ∀ᵐ x ∂torusVolume,x∈E ↔ x∈F at ht
  filter_upwards [ht] with x hx
  exact propext hx

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def coverAEAgreement (A B : Set Cover) : Set Cover :=
  (volume.restrict {x | ¬(x∈A ↔ x∈B)}).supportᶜ

lemma isOpen_coverAEAgreement (A B : Set Cover) : IsOpen (coverAEAgreement A B) :=
  Measure.isOpen_compl_support

lemma mem_coverAEAgreement_iff {A B : Set Cover} {x : Cover} :
    x∈coverAEAgreement A B ↔ ∃ O : Set Cover,IsOpen O ∧ x∈O ∧
      ∀ᵐ y ∂volume,y∈O → (y∈A ↔ y∈B) := by
  change x∉(volume.restrict {y | ¬(y∈A ↔ y∈B)}).support ↔ _
  rw [(nhds_basis_opens x).notMem_measureSupport]
  constructor
  · rintro ⟨O,⟨hx,hO⟩,hz⟩
    refine ⟨O,hO,hx,?_⟩
    rw [ae_iff]
    rw [Measure.restrict_apply hO.measurableSet] at hz
    convert hz using 1
    congr 1
    ext y
    simp only [mem_ofPred_eq,Classical.not_imp,mem_inter_iff]
  · rintro ⟨O,hO,hx,hae⟩
    refine ⟨O,⟨hx,hO⟩,?_⟩
    rw [Measure.restrict_apply hO.measurableSet]
    rw [ae_iff] at hae
    convert hae using 1
    congr 1
    ext y
    simp only [mem_ofPred_eq,Classical.not_imp,mem_inter_iff]

lemma coverAEAgreement_trans {A B C : Set Cover} {x : Cover}
    (h : x∈coverAEAgreement A B) (k : x∈coverAEAgreement B C) :
    x∈coverAEAgreement A C := by
  obtain ⟨O,hO,hx,hae⟩ := mem_coverAEAgreement_iff.mp h
  obtain ⟨P,hP,hxp,hbe⟩ := mem_coverAEAgreement_iff.mp k
  apply mem_coverAEAgreement_iff.mpr
  refine ⟨O∩P,hO.inter hP,⟨hx,hxp⟩,?_⟩
  filter_upwards [hae,hbe] with y hy hz hOP
  exact (hy hOP.1).trans (hz hOP.2)

lemma coverAEAgreement_symm {A B : Set Cover} {x : Cover}
    (h : x∈coverAEAgreement A B) : x∈coverAEAgreement B A := by
  obtain ⟨O,hO,hx,hae⟩ := mem_coverAEAgreement_iff.mp h
  exact mem_coverAEAgreement_iff.mpr ⟨O,hO,hx,hae.mono (fun _ h hy ↦ (h hy).symm)⟩

lemma coverAEAgreement_compl {A B : Set Cover} {x : Cover}
    (h : x∈coverAEAgreement A B) : x∈coverAEAgreement Aᶜ Bᶜ := by
  obtain ⟨O,hO,hx,hae⟩ := mem_coverAEAgreement_iff.mp h
  exact mem_coverAEAgreement_iff.mpr ⟨O,hO,hx,hae.mono (fun _ h hy ↦ not_congr (h hy))⟩

lemma coverAEAgreement_disjoint {A B : Set Cover} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Disjoint (coverAEAgreement A B) (coverAEAgreement A Bᶜ) := by
  have hm : MeasurableSet {x | ¬(x∈A ↔ x∈B)} := by measurability
  have he : {x : Cover | ¬(x∈A ↔ x∈Bᶜ)}={x | ¬(x∈A ↔ x∈B)}ᶜ := by
    ext x; simp only [mem_ofPred_eq,mem_compl_iff]; tauto
  rw [Set.disjoint_iff_inter_eq_empty]
  change (volume.restrict {x | ¬(x∈A ↔ x∈B)}).supportᶜ ∩
    (volume.restrict {x | ¬(x∈A ↔ x∈Bᶜ)}).supportᶜ=∅
  rw [he,←compl_union,←Measure.support_add,Measure.restrict_add_restrict_compl hm,
    Measure.support_eq_univ,compl_univ]

lemma ae_eq_of_coverAEAgreement_univ {A B : Set Cover}
    (h : coverAEAgreement A B=univ) : A=ᵐ[volume]B := by
  have hs : (volume.restrict {x | ¬(x∈A ↔ x∈B)}).support=∅ := by
    have hh := congrArg (fun S : Set Cover ↦ Sᶜ) h
    simpa only [coverAEAgreement,compl_compl,compl_univ] using hh
  have hz := Measure.restrict_eq_zero.mp (Measure.support_eq_empty_iff.mp hs)
  have hae : ∀ᵐ x ∂volume,x∈A ↔ x∈B := ae_iff.mpr hz
  filter_upwards [hae] with x hx
  exact propext hx

theorem cover_local_phase_global {A B : Set Cover} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hcov : ∀ x,x∈coverAEAgreement A B ∨ x∈coverAEAgreement A Bᶜ) :
    A=ᵐ[volume]B ∨ A=ᵐ[volume]Bᶜ := by
  by_cases hn : (coverAEAgreement A B).Nonempty
  · left
    have hsub : (univ : Set Cover)⊆coverAEAgreement A B :=
      isPreconnected_univ.subset_left_of_subset_union (isOpen_coverAEAgreement _ _)
        (isOpen_coverAEAgreement _ _) (coverAEAgreement_disjoint hA hB)
        (fun x _ ↦ hcov x) (by simpa only [univ_inter] using hn)
    exact ae_eq_of_coverAEAgreement_univ (univ_subset_iff.mp hsub)
  · right
    apply ae_eq_of_coverAEAgreement_univ
    apply eq_univ_of_forall
    intro x
    exact (hcov x).resolve_left (fun hx ↦ hn ⟨x,hx⟩)

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
