import Mathlib
import OAI.Geometry.CubicTorus.Profiles.Endpoint

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

structure CenteredJacobiChart (E : Set Torus) (μ : FiniteMeasure NormalBundle)
    (N : Cover → Cover) where
  n : Cover
  g : Plane → ℝ
  sign : ℝ
  K : ℝ≥0
  R : ℝ
  ρ : ℝ
  r : ℝ
  U : Set Cover
  C : ℝ≥0∞
  n_unit : ‖n‖=1
  smooth : ContDiff ℝ (⊤ : ℕ∞) g
  compact : HasCompactSupport g
  lip : LipschitzWith K g
  zero : g 0=0
  sign_eq : sign=1 ∨ sign= -1
  R_pos : 0<R
  rho_pos : 0<ρ
  r_pos : 0<r
  open_U : IsOpen U
  patch_in_U : Metric.closedBall cubeCenter (2*ρ)⊆U
  U_in_ball : U⊆Metric.ball cubeCenter R
  U_in_cell : U⊆{x | ∀ i,0<x i ∧ x i<1}
  phase : (∀ᵐ x : Cover ∂volume,x∈U →
      (quotientMap x∈E ↔ graphSignedHeight cubeCenter n g x<0)) ∨
    (∀ᵐ x : Cover ∂volume,x∈U →
      (quotientMap x∈E ↔ 0<graphSignedHeight cubeCenter n g x))
  normal_disk : ∀ y∈Metric.closedBall (0 : Plane) r,
    N (cubeCenter+normalGraph n g y)=sign•graphSlopeNormal n (gradient g y)
  boundary_disk : ∀ y∈Metric.closedBall (0 : Plane) r,
    quotientMap (cubeCenter+normalGraph n g y)∈frontier (openRepresentative E)
  image_disk : ∀ y∈Metric.closedBall (0 : Plane) r,
    cubeCenter+normalGraph n g y∈Metric.ball cubeCenter (ρ/2)
  slope_disk : ∀ y∈Metric.closedBall (0 : Plane) r,‖gradient g y‖≤(1/4 : ℝ)
  C_finite : C≠⊤
  domination : Measure.map (fun y : Plane ↦ quotientMap (cubeCenter+normalGraph n g y))
    (volume.restrict (Metric.closedBall 0 r))≤C•(spatialNormalMeasure μ : Measure Torus)
  cover_germ : ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (cubeCenter+v)∈frontier (openRepresentative E) ↔
    normalGraph n g (normalPlaneCoordinates n v)=v

theorem isMinimizerAt_centeredJacobiChart {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    Nonempty (CenteredJacobiChart E μ N) := by
  obtain ⟨n,g,σ,K,hn,hg,hgc,hgl,hg0,hσ,hsmall,hgraph,hcover⟩ :=
    actual_centered_compact_small_normal_chart hV hE hmin hcenter hμ hN hp hae
  obtain ⟨t,ht,htcov⟩ := Metric.mem_nhds_iff.mp hcover
  obtain ⟨R,ρ,U,_,_,_,_,hR,hρ,hgC,hU,hpatch,hUR,hUO,hcov,hphase⟩ :=
    centered_graph_phase_patch_of_boundary hV hE hmin hcenter hn ht hgl hg0
      (hg.of_le (by simp)).contDiffOn (fun x hx ↦ htcov hx)
  have hX : Continuous (fun y ↦ cubeCenter+normalGraph n g y) :=
    continuous_const.add ((normalPlaneLinearIsometry n).continuous.add (hg.continuous.smul continuous_const))
  have hz : cubeCenter+normalGraph n g 0=cubeCenter := by
    have he : normalPlaneEmbedding n (0 : Plane)=0 := (normalPlaneLinearIsometry n).map_zero
    simp only [normalGraph,he,hg0,zero_smul,add_zero]
  have hi : ∀ᶠ y in 𝓝 (0 : Plane),cubeCenter+normalGraph n g y∈Metric.ball cubeCenter (ρ/2) :=
    hX.continuousAt.preimage_mem_nhds (by rw [hz]; exact Metric.ball_mem_nhds _ (half_pos hρ))
  have hnorm : ∀ᶠ y in 𝓝 (0 : Plane),‖normalGraph n g y‖<(1/4 : ℝ) := by
    have ht : ∀ᶠ y in 𝓝 (0 : Plane),cubeCenter+normalGraph n g y∈Metric.ball cubeCenter (1/4 : ℝ) :=
      hX.continuousAt.preimage_mem_nhds (by rw [hz]; exact Metric.ball_mem_nhds _ (by norm_num : (0:ℝ)<1/4))
    simpa only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left] using ht
  obtain ⟨s,hs,hsub⟩ := Metric.mem_nhds_iff.mp (hgraph.and (hsmall.and (hi.and hnorm)))
  let r := s/2
  have hr : 0<r := half_pos hs
  have hrd : Metric.closedBall (0 : Plane) r⊆Metric.ball 0 s :=
    Metric.closedBall_subset_ball (by dsimp [r]; linarith)
  obtain ⟨R₀,c,hR₀,hc,hl⟩ := isMinimizerAt_perimeter_lower_density hV hE hmin
  let C : ℝ≥0∞ := (planeAreaFactor : ℝ≥0∞)*ENNReal.ofReal (64/c)
  have hF : Measurable (fun y ↦ quotientMap cubeCenter+quotientMap (normalGraph n g y)) := by
    simpa only [Function.comp_def,quotientMap_add] using (continuous_quotientMap.comp hX).measurable
  have hd := normalGraph_map_volume_le_of_lower_density (spatialNormalMeasure μ)
    (frontier (openRepresentative E)) hR₀ hc
    (fun a ha ↦ hl μ hμ a (by rwa [← isMinimizerAt_frontier_openRepresentative hV hE hmin]))
    hn g (quotientMap cubeCenter) (Metric.closedBall 0 r) hF
    (fun y hy ↦ (hsub (hrd hy)).2.2.2)
    (fun y hy ↦ by simpa only [← quotientMap_add] using (hsub (hrd hy)).1.2)
  refine ⟨{
    n := n
    g := g
    sign := σ
    K := K
    R := R
    ρ := ρ
    r := r
    U := U
    C := C
    n_unit := hn
    smooth := hg
    compact := hgc
    lip := hgl
    zero := hg0
    sign_eq := hσ
    R_pos := hR
    rho_pos := hρ
    r_pos := hr
    open_U := hU
    patch_in_U := hpatch
    U_in_ball := hUR
    U_in_cell := hUO
    phase := hphase
    normal_disk := fun y hy ↦ (hsub (hrd hy)).1.1
    boundary_disk := fun y hy ↦ (hsub (hrd hy)).1.2
    image_disk := fun y hy ↦ (hsub (hrd hy)).2.2.1
    slope_disk := fun y hy ↦ (hsub (hrd hy)).2.1
    C_finite := by dsimp [C]; finiteness
    domination := by simpa only [← quotientMap_add] using hd
    cover_germ := hcover }⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integral_normal_cover_position (μ : FiniteMeasure NormalBundle)
    {k : Cover → ℝ} (hk : Measurable k) :
    (∫ x,k x ∂Measure.map Prod.fst (normalCoverMeasure μ : Measure BlowupNormalBundle))=
      ∫ z,k z.1 ∂(μ : Measure NormalBundle) := by
  rw [integral_map measurable_fst.aemeasurable hk.stronglyMeasurable.aestronglyMeasurable]
  change (∫ z,k z.1 ∂Measure.map normalCoverMap (μ : Measure NormalBundle))=_
  have hkm : Measurable (fun z : BlowupNormalBundle ↦ k z.1) := hk.comp measurable_fst
  rw [integral_map continuous_normalCoverMap.measurable.aemeasurable
    hkm.stronglyMeasurable.aestronglyMeasurable]
  rfl

theorem normalMeasure_graph_integral {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y∈Metric.closedBall (0 : Plane) R,ContinuousAt (fderiv ℝ g) y)
    {U : Set Cover}
    (hphase : (∀ᵐ x : Cover ∂volume,x∈U → (quotientMap x∈E ↔ graphSignedHeight a n g x<0)) ∨
      (∀ᵐ x : Cover ∂volume,x∈U → (quotientMap x∈E ↔ 0<graphSignedHeight a n g x)))
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ⊆U) (hφO : tsupport φ⊆{x | ∀ i,0<x i ∧ x i<1})
    (hφR : tsupport φ⊆Metric.closedBall a R) (hφb : ∀ x,φ x∈Icc 0 1)
    {k : Cover → ℝ} (hk : Measurable k) (hφk : ∀ x,φ x*k x=k x) :
    (∫ z,k z.1 ∂(μ : Measure NormalBundle))=
      ∫ y,‖graphAreaVector n g y‖*k (a+normalGraph n g y) := by
  let O : Set Cover := {x | ∀ i,0<x i ∧ x i<1}
  let ν := Measure.map Prod.fst (normalCoverMeasure μ : Measure BlowupNormalBundle)
  let X : Plane → Cover := fun y ↦ a+normalGraph n g y
  have hX : Measurable X := (graph_trace_continuous a n hg.continuous continuous_id).measurable
  have hw := graph_weighted_continuous a hn hg.continuous hφ.continuous hφR
    (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).norm)
  have hm := normalMeasure_graph_patch_measure_eq hE hμ a hn hg hc hphase
    hφ hsφ hφU hφO hφR hφb
  have hi := congrArg (fun η : Measure Cover ↦ ∫ x,k x ∂η) hm
  rw [integral_withDensity_eq_integral_toReal_smul hφ.continuous.measurable.ennreal_ofReal
      (ae_of_all (ν.restrict O) fun _ ↦ ENNReal.ofReal_lt_top),
    integral_map hX.aemeasurable hk.stronglyMeasurable.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hw.measurable.ennreal_ofReal
      (ae_of_all volume fun _ ↦ ENNReal.ofReal_lt_top)] at hi
  simp_rw [ENNReal.toReal_ofReal (hφb _).1,
    ENNReal.toReal_ofReal (mul_nonneg (hφb _).1 (norm_nonneg _)),smul_eq_mul] at hi
  have hz (x : Cover) (hx : x∉O) : k x=0 := by
    have hnφ : x∉tsupport φ := fun h ↦ hx (hφO h)
    simpa only [image_eq_zero_of_notMem_tsupport hnφ,zero_mul] using (hφk x).symm
  change (∫ x in O,φ x*k x ∂ν)=_ at hi
  simp_rw [hφk] at hi
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    integral_normal_cover_position μ hk] at hi
  rw [hi]
  apply integral_congr_ae
  filter_upwards [] with y
  calc
    φ (X y)*‖graphAreaVector n g y‖*k (X y)=
      ‖graphAreaVector n g y‖*(φ (X y)*k (X y)) := by ring
    _=_ := by rw [hφk]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphSlopeNormal_inner_graphDerivative {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {y : Plane} (hg : DifferentiableAt ℝ g y) (w : Plane) :
    ⟪graphSlopeNormal n (gradient g y),fderiv ℝ (normalGraph n g) y w⟫=0 := by
  rw [(normalGraph_hasFDerivAt hg).fderiv]
  change ⟪graphSlopeNormal n (gradient g y),
    normalPlaneEmbedding n w+fderiv ℝ g y w•n⟫=0
  rw [graphSlopeNormal,real_inner_smul_left,inner_sub_left,inner_add_right,
    inner_add_right,real_inner_smul_right,real_inner_smul_right,
    normalPlaneEmbedding_inner hn,real_inner_self_eq_norm_sq,hn,one_pow]
  have hi : ⟪normalPlaneEmbedding n (gradient g y),normalPlaneEmbedding n w⟫=
      fderiv ℝ g y w := by
    rw [show normalPlaneEmbedding n (gradient g y)=normalPlaneLinearIsometry n (gradient g y) from rfl,
      show normalPlaneEmbedding n w=normalPlaneLinearIsometry n w from rfl,
      (normalPlaneLinearIsometry n).inner_map_map,inner_gradient_left]
  have hz : ⟪normalPlaneEmbedding n (gradient g y),n⟫=0 := by
    rw [real_inner_comm,normalPlaneEmbedding_inner hn]
  rw [hi,hz]
  ring

lemma normalGraph_translated_tangency {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (x : Cover) (s : ℝ) (y w : Plane) :
    ⟪s•graphSlopeNormal n (gradient g y),
      fderiv ℝ (fun z ↦ x+normalGraph n g z) y w⟫=0 := by
  have hd := normalGraph_hasFDerivAt (n := n) (hg.differentiable (by simp) y)
  rw [(hd.const_add x).fderiv,real_inner_smul_left]
  have ht := graphSlopeNormal_inner_graphDerivative hn (hg.differentiable (by simp) y) w
  rw [hd.fderiv] at ht
  rw [ht,mul_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_trace_gradient (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {F : Cover → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (y : Plane) :
    gradient (fun z ↦ F (a+normalGraph n g z)) y=
      normalPlaneCoordinates n (gradient F (a+normalGraph n g y))+
        ⟪n,gradient F (a+normalGraph n g y)⟫ • gradient g y := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,inner_add_left,real_inner_smul_left]
  have hX := (normalGraph_hasFDerivAt (n := n) (hg.differentiable (by simp) y)).const_add a
  have hd : fderiv ℝ (fun z ↦ F (a+normalGraph n g z)) y=
      (fderiv ℝ F (a+normalGraph n g y)).comp
        ((normalPlaneLinearIsometry n).toContinuousLinearMap+(fderiv ℝ g y).smulRight n) := by
    exact (hF.differentiable (by simp) _).hasFDerivAt.comp y hX |>.fderiv
  rw [hd]
  change fderiv ℝ F (a+normalGraph n g y)
    (normalPlaneEmbedding n v+fderiv ℝ g y v•n)=_
  rw [map_add,map_smul,← inner_gradient_left,← inner_gradient_left,
    real_inner_comm (gradient F _) n,← inner_gradient_left]
  congr 1
  · rw [real_inner_comm,normalPlaneEmbedding_inner_coordinates hn,real_inner_comm]
  · simp [smul_eq_mul,mul_comm]

theorem graphTangentialGradient_trace (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {F : Cover → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (y : Plane) :
    graphTangentialGradient n g (fun z ↦ F (a+normalGraph n g z)) y=
      gradient F (a+normalGraph n g y)-
        ⟪graphSlopeNormal n (gradient g y),gradient F (a+normalGraph n g y)⟫ •
          graphSlopeNormal n (gradient g y) := by
  rw [graphTangentialGradient,normalGraph_trace_gradient a hn hg hF,
    (normalGraph_hasFDerivAt (n := n) (hg.differentiable (by simp) y)).fderiv]
  change normalPlaneEmbedding n _+fderiv ℝ g y _•n=_
  rw [← inner_gradient_left]
  exact graph_metric_projection hn _ _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem graph_compact_test_extension (a p : Cover) {n : Cover} (hn : ‖n‖=1)
    (g : Plane → ℝ) {ρ : ℝ} (hρ : 0<ρ)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hsψ : ∀ y∈tsupport ψ,a+normalGraph n g y∈Metric.ball p (ρ/2)) :
    ∃ F : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧
      tsupport F⊆Metric.closedBall p ρ ∧
      (∀ y,F (a+normalGraph n g y)=ψ y) ∧
      (∀ y,F=ᶠ[𝓝 (a+normalGraph n g y)] graphHeightExtension a n ψ) := by
  let ζ := radialHeightCutoff p (ρ/2)
  let f := graphHeightExtension a n ψ
  let F : Cover → ℝ := fun x ↦ ζ x*f x
  have hζ : ContDiff ℝ (⊤ : ℕ∞) ζ := radialDensityWeight_contDiff _ _ _
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := graphHeightExtension_contDiff a n hψ
  have hsζ : HasCompactSupport ζ := radialDensityWeight_hasCompactSupport (by positivity) (by positivity)
  have hsb : tsupport ζ⊆Metric.closedBall p ρ := by
    have hh := radialDensityWeight_tsupport (a := p) (r := 2*(ρ/2))
      (ε := 3*(ρ/2)^2) (by positivity) (by positivity)
    convert hh using 1 <;> congr 1
    ring
  have hterm (y : Plane) : F=ᶠ[𝓝 (a+normalGraph n g y)] f := by
    let x := a+normalGraph n g y
    have hxy : normalPlaneCoordinates n (x-a)=y := by
      simp only [x,add_sub_cancel_left,normalPlaneCoordinates_graph hn]
    by_cases hy : y∈tsupport ψ
    · have hz : ζ=ᶠ[𝓝 x] fun _ ↦ (1 : ℝ) :=
        radialHeightCutoff_eventually_one (by positivity) (hsψ y hy)
      filter_upwards [hz] with z hz
      simp only [F,hz,one_mul]
    · have hψ0 : ψ=ᶠ[𝓝 y] fun _ ↦ (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.mp hy
      have ht : Tendsto (fun z : Cover ↦ normalPlaneCoordinates n (z-a)) (𝓝 x) (𝓝 y) := by
        have ht := ((normalPlaneCoordinates n).continuous.comp
          (continuous_id.sub (continuous_const (y := a)))).tendsto x
        change Tendsto (fun z : Cover ↦ normalPlaneCoordinates n (z-a)) (𝓝 x)
          (𝓝 (normalPlaneCoordinates n (x-a))) at ht
        rwa [hxy] at ht
      have hf0 : f=ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := ht.eventually hψ0
      filter_upwards [hf0] with z hz
      simp only [F,hz,mul_zero]
  refine ⟨F,hζ.mul hf,hsζ.mul_right,tsupport_mul_subset_left.trans hsb,?_,hterm⟩
  intro y
  rw [(hterm y).eq_of_nhds]
  simp only [f,graphHeightExtension,add_sub_cancel_left,normalPlaneCoordinates_graph hn]

theorem compact_test_periodization {F : Cover → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsF : HasCompactSupport F)
    (hO : tsupport F⊆{x | ∀ i,0<x i ∧ x i<1}) :
    ∃ f : smoothPeriodicScalars,∀ x : CompactCell,
      f.val=ᶠ[𝓝 (x : Cover)] F := by
  refine ⟨⟨latticePeriodize F,latticePeriodize_contDiff hF hsF,latticePeriodize_periodic F⟩,?_⟩
  intro x
  exact latticePeriodize_eventuallyEq hsF hO (compactCell_coordinates x)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma sibling_surfaceJacobiB_cutoff_commutator (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u v : SurfaceJet μ)
    (f : smoothPeriodicScalars) :
    surfaceJacobiB μ q u (surfaceCutoffJet μ f v)-
      surfaceJacobiB μ q v (surfaceCutoffJet μ f u)=
      ∫ z,⟪v.1 z • u.2 z-u.1 z • v.2 z,smoothScalarGradient f z⟫
        ∂(μ : Measure NormalBundle) := by
  unfold surfaceJacobiB
  simp only [L2.inner_def]
  rw [← integral_sub (L2.integrable_inner u.2 (surfaceCutoffJet μ f v).2)
      (L2.integrable_inner (surfaceMultiplier μ q u.1) (surfaceCutoffJet μ f v).1),
    ← integral_sub (L2.integrable_inner v.2 (surfaceCutoffJet μ f u).2)
      (L2.integrable_inner (surfaceMultiplier μ q v.1) (surfaceCutoffJet μ f u).1)]
  have hiu : Integrable (fun z : NormalBundle ↦
      ⟪u.2 z,(surfaceCutoffJet μ f v).2 z⟫-
      ⟪surfaceMultiplier μ q u.1 z,(surfaceCutoffJet μ f v).1 z⟫) (μ : Measure NormalBundle) :=
    (L2.integrable_inner u.2 (surfaceCutoffJet μ f v).2).sub
      (L2.integrable_inner (surfaceMultiplier μ q u.1) (surfaceCutoffJet μ f v).1)
  have hiv : Integrable (fun z : NormalBundle ↦
      ⟪v.2 z,(surfaceCutoffJet μ f u).2 z⟫-
      ⟪surfaceMultiplier μ q v.1 z,(surfaceCutoffJet μ f u).1 z⟫) (μ : Measure NormalBundle) :=
    (L2.integrable_inner v.2 (surfaceCutoffJet μ f u).2).sub
      (L2.integrable_inner (surfaceMultiplier μ q v.1) (surfaceCutoffJet μ f u).1)
  rw [← integral_sub hiu hiv]
  apply integral_congr_ae
  filter_upwards [surfaceCutoffJet_ae μ f u,surfaceCutoffJet_ae μ f v,
    Lp.coeFn_lpSMul (r := 2) q u.1,Lp.coeFn_lpSMul (r := 2) q v.1] with z hu hv hqu hqv
  change (surfaceMultiplier μ q u.1) z=q z*u.1 z at hqu
  change (surfaceMultiplier μ q v.1) z=q z*v.1 z at hqv
  rw [hu.1,hu.2,hv.1,hv.2,hqu,hqv]
  simp only [inner_add_right,inner_smul_right,inner_sub_left,real_inner_smul_left,
    RCLike.inner_apply,RCLike.conj_to_real]
  rw [real_inner_comm (v.2 z) (u.2 z)]
  ring

theorem surfaceH1_weak_wronskian (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) {u v : SurfaceJet μ}
    (hu : u∈surfaceH1 μ) (hv : v∈surfaceH1 μ)
    (hju : ∀ w∈surfaceH1 μ,surfaceJacobiB μ q u w=0)
    (hjv : ∀ w∈surfaceH1 μ,surfaceJacobiB μ q v w=0)
    (f : smoothPeriodicScalars) :
    (∫ z,⟪v.1 z • u.2 z-u.1 z • v.2 z,smoothScalarGradient f z⟫
        ∂(μ : Measure NormalBundle))=0 := by
  rw [← sibling_surfaceJacobiB_cutoff_commutator μ q u v f,
    hju _ (surfaceCutoffJet_mem_surfaceH1 μ f hv),
    hjv _ (surfaceCutoffJet_mem_surfaceH1 μ f hu),sub_self]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalProjection_measurePreserving (μ : FiniteMeasure NormalBundle) :
    MeasurePreserving normalProjection (μ : Measure NormalBundle)
      (spatialNormalMeasure μ : Measure Torus) :=
  ⟨normalProjection_continuous.measurable,rfl⟩

def spatialPullback (μ : FiniteMeasure NormalBundle) (W : Type*)
    [NormedAddCommGroup W] [NormedSpace ℝ W] :
    Lp W 2 (spatialNormalMeasure μ : Measure Torus) →ₗᵢ[ℝ]
      Lp W 2 (μ : Measure NormalBundle) :=
  Lp.compMeasurePreservingₗᵢ ℝ normalProjection (normalProjection_measurePreserving μ)

lemma spatialPullback_continuousMap (μ : FiniteMeasure NormalBundle) {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] (F : C(Torus,W)) :
    spatialPullback μ W (ContinuousMap.toLp 2 (spatialNormalMeasure μ : Measure Torus) ℝ F)=
      ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ
        (F.comp ⟨normalProjection,normalProjection_continuous⟩) := by
  apply Lp.ext
  have hF := F.coeFn_toLp (p := 2) (𝕜 := ℝ) (spatialNormalMeasure μ : Measure Torus)
  have hFp := ae_of_ae_map normalProjection_continuous.measurable.aemeasurable hF
  filter_upwards [Lp.coeFn_compMeasurePreserving
    (ContinuousMap.toLp 2 (spatialNormalMeasure μ : Measure Torus) ℝ F)
    (normalProjection_measurePreserving μ),hFp,
    (F.comp ⟨normalProjection,normalProjection_continuous⟩).coeFn_toLp
      (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)] with z h₁ h₂ h₃
  exact h₁.trans (h₂.trans h₃.symm)

lemma surfaceSmoothJet_value_spatial (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars) :
    (surfaceSmoothJet μ f).1∈Set.range (spatialPullback μ ℝ) := by
  let F : C(Torus,ℝ) := ⟨fun a ↦ f.val (representative a),
    continuous_periodic_descent f.property.1.continuous f.property.2⟩
  refine ⟨ContinuousMap.toLp 2 (spatialNormalMeasure μ : Measure Torus) ℝ F,?_⟩
  rw [spatialPullback_continuousMap]
  congr 1
  apply ContinuousMap.ext
  intro z
  exact periodic_representative f.property.2 z.1

lemma surfaceSmoothJet_gradient_spatial {μ : FiniteMeasure NormalBundle}
    {N : Cover → Cover} (hN : Continuous N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hn : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (f : smoothPeriodicScalars) :
    (surfaceSmoothJet μ f).2∈Set.range (spatialPullback μ Cover) := by
  let F₀ : Cover → Cover := fun x ↦
    gradient f.val x-⟪N x,gradient f.val x⟫ • N x
  have hF₀ : Continuous F₀ := by
    have hg := (gradient_contDiff f.property.1).continuous
    exact hg.sub ((hN.inner (𝕜 := ℝ) hg).smul hN)
  have hFp (m) (x) : F₀ (x+latticeVector m)=F₀ x := by
    simp only [F₀,hp,gradient_periodic f.property.2]
  let F : C(Torus,Cover) := ⟨fun a ↦ F₀ (representative a),continuous_periodic_descent hF₀ hFp⟩
  refine ⟨ContinuousMap.toLp 2 (spatialNormalMeasure μ : Measure Torus) ℝ F,?_⟩
  rw [spatialPullback_continuousMap]
  apply Lp.ext
  filter_upwards [(F.comp ⟨normalProjection,normalProjection_continuous⟩).coeFn_toLp
    (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle),
      (smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle),hn]
    with z h₁ h₂ h₃
  rw [h₁]
  change _=(surfaceSmoothJet μ f).2 z
  change (surfaceSmoothJet μ f).2 z=smoothScalarGradient f z at h₂
  rw [h₂]
  change F₀ (representative (quotientMap z.1))=_
  rw [periodic_representative hFp]
  change gradient f.val z.1-⟪N z.1,gradient f.val z.1⟫ • N z.1=_
  rw [h₃]
  rfl

theorem surfaceH1_spatial_descent {μ : FiniteMeasure NormalBundle}
    {N : Cover → Cover} (hN : Continuous N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hn : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) :
    ∃ (v : Lp ℝ 2 (spatialNormalMeasure μ : Measure Torus))
      (G : Lp Cover 2 (spatialNormalMeasure μ : Measure Torus)),
      spatialPullback μ ℝ v=u.1 ∧ spatialPullback μ Cover G=u.2 := by
  have hv : IsClosed (Set.range (spatialPullback μ ℝ)) :=
    (spatialPullback μ ℝ).isometry.isClosedEmbedding.isClosed_range
  have hg : IsClosed (Set.range (spatialPullback μ Cover)) :=
    (spatialPullback μ Cover).isometry.isClosedEmbedding.isClosed_range
  have hs : IsClosed {w : SurfaceJet μ | w.1∈Set.range (spatialPullback μ ℝ) ∧
      w.2∈Set.range (spatialPullback μ Cover)} :=
    (hv.preimage continuous_fst).inter (hg.preimage continuous_snd)
  have hr : Set.range (surfaceSmoothJet μ)⊆{w : SurfaceJet μ |
      w.1∈Set.range (spatialPullback μ ℝ) ∧ w.2∈Set.range (spatialPullback μ Cover)} := by
    rintro _ ⟨f,rfl⟩
    exact ⟨surfaceSmoothJet_value_spatial μ f,surfaceSmoothJet_gradient_spatial hN hp hn f⟩
  obtain ⟨⟨v,hv⟩,⟨G,hG⟩⟩ := closure_minimal hr hs hu
  exact ⟨v,G,hv,hG⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def dominatedL2Pullback {α β W : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (ν : Measure α) (μ : Measure β) (f : α → β) (hf : Measurable f)
    {C : ℝ≥0∞} (hC : C≠⊤) (hdom : Measure.map f ν≤C•μ) :
    Lp W 2 μ →L[ℝ] Lp W 2 ν :=
  (Lp.compMeasurePreservingₗᵢ ℝ f (show MeasurePreserving f ν (Measure.map f ν) from
    ⟨hf,rfl⟩)).toContinuousLinearMap.comp (Lp.LpToLpOfMeasureLeSMul hC hdom)

lemma dominatedL2Pullback_ae {α β W : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (ν : Measure α) (μ : Measure β) (f : α → β) (hf : Measurable f)
    {C : ℝ≥0∞} (hC : C≠⊤) (hdom : Measure.map f ν≤C•μ) (u : Lp W 2 μ) :
    dominatedL2Pullback ν μ f hf hC hdom u =ᵐ[ν] fun x ↦ u (f x) := by
  have h := Lp.coeFn_LpToLpOfMeasureLeSMul hC hdom u
  have hp := ae_of_ae_map hf.aemeasurable h
  have hc := Lp.coeFn_compMeasurePreserving (Lp.LpToLpOfMeasureLeSMul hC hdom u)
    (show MeasurePreserving f ν (Measure.map f ν) from ⟨hf,rfl⟩)
  exact hc.trans hp

def spatialPushdown (μ : FiniteMeasure NormalBundle) (W : Type*)
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] :
    Lp W 2 (μ : Measure NormalBundle) →L[ℝ]
      Lp W 2 (spatialNormalMeasure μ : Measure Torus) :=
  (spatialPullback μ W).toContinuousLinearMap.adjoint

@[simp] lemma spatialPushdown_pullback (μ : FiniteMeasure NormalBundle) (W : Type*)
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (u : Lp W 2 (spatialNormalMeasure μ : Measure Torus)) :
    spatialPushdown μ W (spatialPullback μ W u)=u := by
  exact congr($(spatialPullback μ W |>.adjoint_comp_self) u)

lemma spatialPullback_pushdown {μ : FiniteMeasure NormalBundle} {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    {u : Lp W 2 (μ : Measure NormalBundle)} (hu : u∈Set.range (spatialPullback μ W)) :
    spatialPullback μ W (spatialPushdown μ W u)=u := by
  rcases hu with ⟨v,rfl⟩
  rw [spatialPushdown_pullback]

def surfaceChartPullback (μ : FiniteMeasure NormalBundle) (W : Type*)
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (D : Set Plane) (F : Plane → Torus) (hF : Measurable F)
    {C : ℝ≥0∞} (hC : C≠⊤)
    (hdom : Measure.map F (volume.restrict D)≤C•(spatialNormalMeasure μ : Measure Torus)) :
    Lp W 2 (μ : Measure NormalBundle) →L[ℝ] Lp W 2 (volume.restrict D) :=
  (dominatedL2Pullback (volume.restrict D) (spatialNormalMeasure μ : Measure Torus)
    F hF hC hdom).comp (spatialPushdown μ W)

lemma surfaceChartPullback_continuousMap (μ : FiniteMeasure NormalBundle) {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (D : Set Plane) (F : Plane → Torus) (hF : Measurable F)
    {C : ℝ≥0∞} (hC : C≠⊤)
    (hdom : Measure.map F (volume.restrict D)≤C•(spatialNormalMeasure μ : Measure Torus))
    (f : C(Torus,W)) :
    surfaceChartPullback μ W D F hF hC hdom
      (ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ
        (f.comp ⟨normalProjection,normalProjection_continuous⟩))
      =ᵐ[volume.restrict D] fun x ↦ f (F x) := by
  rw [← spatialPullback_continuousMap]
  change dominatedL2Pullback (volume.restrict D) (spatialNormalMeasure μ : Measure Torus)
    F hF hC hdom (spatialPushdown μ W (spatialPullback μ W _)) =ᵐ[_] _
  rw [spatialPushdown_pullback]
  refine (dominatedL2Pullback_ae _ _ _ _ _ _ _).trans ?_
  have ha := (Measure.absolutelyContinuous_of_le_smul hdom).ae_eq
    (f.coeFn_toLp (p := 2) (𝕜 := ℝ) (spatialNormalMeasure μ : Measure Torus))
  exact ae_of_ae_map hF.aemeasurable ha

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceH1_spatial_representatives {μ : FiniteMeasure NormalBundle}
    {N : Cover → Cover} (hN : Continuous N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hn : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) :
    ∃ (v : Lp ℝ 2 (spatialNormalMeasure μ : Measure Torus))
      (G : Lp Cover 2 (spatialNormalMeasure μ : Measure Torus)),
      spatialPullback μ ℝ v=u.1 ∧ spatialPullback μ Cover G=u.2 ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),u.1 z=v (quotientMap z.1) ∧
        u.2 z=G (quotientMap z.1)) := by
  obtain ⟨v,G,hv,hG⟩ := surfaceH1_spatial_descent hN hp hn hu
  refine ⟨v,G,hv,hG,?_⟩
  have h₁ := (Lp.coeFn_compMeasurePreserving v (normalProjection_measurePreserving μ))
  have h₂ := (Lp.coeFn_compMeasurePreserving G (normalProjection_measurePreserving μ))
  change spatialPullback μ ℝ v=ᵐ[_] _ at h₁
  change spatialPullback μ Cover G=ᵐ[_] _ at h₂
  rw [hv] at h₁
  rw [hG] at h₂
  exact h₁.and h₂

def normalProjectedGradient (N : Cover → Cover) (F : Cover → ℝ) (x : Cover) : Cover :=
  gradient F x-⟪N x,gradient F x⟫ • N x

lemma continuous_normalProjectedGradient {N : Cover → Cover} (hN : Continuous N)
    {F : Cover → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (normalProjectedGradient N F) := by
  have hG := (gradient_contDiff hF).continuous
  exact hG.sub ((hN.inner (𝕜 := ℝ) hG).smul hN)

theorem localized_wronskian_graph_integral {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y∈Metric.closedBall (0 : Plane) R,ContinuousAt (fderiv ℝ g) y)
    {U : Set Cover}
    (hphase : (∀ᵐ x : Cover ∂volume,x∈U → (quotientMap x∈E ↔ graphSignedHeight a n g x<0)) ∨
      (∀ᵐ x : Cover ∂volume,x∈U → (quotientMap x∈E ↔ 0<graphSignedHeight a n g x)))
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ⊆U) (hφO : tsupport φ⊆{x | ∀ i,0<x i ∧ x i<1})
    (hφR : tsupport φ⊆Metric.closedBall a R) (hφb : ∀ x,φ x∈Icc 0 1)
    {N : Cover → Cover} (hN : Continuous N)
    (haeN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {F : Cover → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hφF : ∀ x∈tsupport F,φ x=1)
    (f w : smoothPeriodicScalars) (hf : ∀ x : CompactCell,f.val=ᶠ[𝓝 (x : Cover)]F)
    (u : SurfaceJet μ)
    (v : Lp ℝ 2 (spatialNormalMeasure μ : Measure Torus))
    (G : Lp Cover 2 (spatialNormalMeasure μ : Measure Torus))
    (haeu : ∀ᵐ z ∂(μ : Measure NormalBundle),u.1 z=v (quotientMap z.1) ∧
      u.2 z=G (quotientMap z.1)) :
    (∫ z,⟪(surfaceSmoothJet μ w).1 z • u.2 z-
      u.1 z • (surfaceSmoothJet μ w).2 z,smoothScalarGradient f z⟫
        ∂(μ : Measure NormalBundle))=
    ∫ y,‖graphAreaVector n g y‖*
      ⟪w.val (a+normalGraph n g y) • G (quotientMap (a+normalGraph n g y))-
        v (quotientMap (a+normalGraph n g y)) •
          normalProjectedGradient N w.val (a+normalGraph n g y),
          normalProjectedGradient N F (a+normalGraph n g y)⟫ := by
  let k : Cover → ℝ := fun x ↦ ⟪w.val x • G (quotientMap x)-
    v (quotientMap x) • normalProjectedGradient N w.val x,normalProjectedGradient N F x⟫
  have hk : Measurable k :=
    ((w.property.1.continuous.measurable.smul ((Lp.stronglyMeasurable G).measurable.comp measurable_quotientMap)).sub
      (((Lp.stronglyMeasurable v).measurable.comp measurable_quotientMap).smul
        (continuous_normalProjectedGradient hN w.property.1).measurable)).inner
          (continuous_normalProjectedGradient hN hF).measurable
  have hφk (x : Cover) : φ x*k x=k x := by
    by_cases hx : x∈tsupport F
    · rw [hφF x hx,one_mul]
    · have hz : gradient F x=0 := by simp [gradient,fderiv_of_notMem_tsupport ℝ hx]
      simp only [k,normalProjectedGradient,hz,inner_zero_right,zero_smul,sub_zero,mul_zero]
  calc
    _=(∫ z,k z.1 ∂(μ : Measure NormalBundle)) := by
      apply integral_congr_ae
      filter_upwards [haeu,haeN,
        (smoothScalarValue w).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle),
        (smoothScalarGradient w).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)]
        with z hu hNz hwv hwg
      change (surfaceSmoothJet μ w).1 z=w.val z.1 at hwv
      change (surfaceSmoothJet μ w).2 z=smoothScalarGradient w z at hwg
      rw [hwv,hwg,hu.1,hu.2]
      have hfgrad : gradient f.val (z.1 : Cover)=gradient F z.1 := by
        simp only [gradient,(hf z.1).fderiv_eq]
      change ⟪_,gradient f.val z.1-⟪(z.2 : Cover),gradient f.val z.1⟫•(z.2 : Cover)⟫=k z.1
      dsimp only [smoothScalarGradient,ContinuousMap.coe_mk]
      simp only [k,normalProjectedGradient,← hNz,hfgrad]
    _=_ := normalMeasure_graph_integral hE hμ a hn hg hc hphase hφ hsφ hφU hφO hφR hφb hk hφk

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalProjectedGradient_sign {N : Cover → Cover} {x n : Cover} {σ : ℝ}
    (hN : N x=σ•n) (hσ : σ=1 ∨ σ= -1) (F : Cover → ℝ) :
    normalProjectedGradient N F x=gradient F x-⟪n,gradient F x⟫•n := by
  rcases hσ with rfl|rfl
  · simp only [normalProjectedGradient,hN,one_smul]
  · simp only [normalProjectedGradient,hN,inner_neg_left,neg_smul,smul_neg,neg_neg,one_smul]

lemma normalProjectedGradient_graph_trace (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {N : Cover → Cover} {σ : ℝ} (hσ : σ=1 ∨ σ= -1) {y : Plane}
    (hNy : N (a+normalGraph n g y)=σ•graphSlopeNormal n (gradient g y))
    {F : Cover → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    normalProjectedGradient N F (a+normalGraph n g y)=
      graphTangentialGradient n g (fun z ↦ F (a+normalGraph n g z)) y := by
  rw [normalProjectedGradient_sign hNy hσ,graphTangentialGradient_trace a hn hg hF]

lemma plane_gradient_const_div {q : Plane → ℝ} {y : Plane}
    (hq : DifferentiableAt ℝ q y) (hy : q y≠0) (σ : ℝ) :
    gradient (fun z ↦ σ/q z) y= -(σ/(q y)^2)•gradient q y := by
  rw [plane_gradient_div (differentiableAt_const σ) hq hy]
  have hz : gradient (fun _ : Plane ↦ σ) y=0 := by simp [gradient]
  rw [hz,smul_zero,zero_sub,neg_smul]

theorem graph_wronskian_ground_state {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (a : Cover) (ψ : Plane → ℝ) (y : Plane) (σ u : ℝ) (G : Cover) :
    ‖graphAreaVector n g y‖*
      ⟪(σ/cmcWeight (gradient g y))•G-
          u•graphTangentialGradient n g (fun z ↦ σ/cmcWeight (gradient g z)) y,
        graphTangentialGradient n g ψ y⟫=
      σ*⟪cmcWeight (gradient g y)•(fderiv ℝ (fun z ↦ a+normalGraph n g z) y).adjoint G+
          u•gradient (fun z ↦ cmcWeight (gradient g z)) y,
        cmcJacobian (gradient g y) (gradient ψ y)⟫ := by
  let q : Plane → ℝ := fun z ↦ cmcWeight (gradient g z)
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := cmcWeight_contDiff.comp (plane_gradient_contDiff hg)
  have hqy : q y≠0 := (cmcWeight_pos _).ne'
  have harea : ‖graphAreaVector n g y‖=q y := graphAreaVector_norm_sqrt hn g y
  have htr : fderiv ℝ (fun z ↦ a+normalGraph n g z) y=fderiv ℝ (normalGraph n g) y := by
    exact fderiv_const_add a
  rw [harea,inner_sub_left,real_inner_smul_left,real_inner_smul_left,
    graphTangentialGradient_inner hn hg,plane_gradient_const_div
      (hq.differentiable (by simp) y) hqy]
  have hide (V : Cover) : ⟪V,graphTangentialGradient n g ψ y⟫=
      q y*⟪(fderiv ℝ (normalGraph n g) y).adjoint V,
        cmcJacobian (gradient g y) (gradient ψ y)⟫ := by
    rw [graphTangentialGradient,← ContinuousLinearMap.adjoint_inner_left,
      graphInverseMetric,smul_apply,inner_smul_right]
  rw [hide,htr]
  simp only [real_inner_smul_left,inner_add_left]
  change q y*((σ/q y)*(q y*_) -u*(q y*((-(σ/(q y)^2))*_)))=σ*(q y*_+u*_)
  field_simp
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphHeightExtension_eventually_zero (a : Cover) {n : Cover} (hn : ‖n‖=1)
    (g ψ : Plane → ℝ) {y : Plane} (hy : y∉tsupport ψ) :
    graphHeightExtension a n ψ=ᶠ[𝓝 (a+normalGraph n g y)] fun _ ↦ (0 : ℝ) := by
  have ht : Tendsto (fun z : Cover ↦ normalPlaneCoordinates n (z-a))
      (𝓝 (a+normalGraph n g y)) (𝓝 y) := by
    have ht := ((normalPlaneCoordinates n).continuous.comp
      (continuous_id.sub (continuous_const (y := a)))).tendsto (a+normalGraph n g y)
    change Tendsto (fun z : Cover ↦ normalPlaneCoordinates n (z-a))
      (𝓝 (a+normalGraph n g y)) (𝓝 (normalPlaneCoordinates n ((a+normalGraph n g y)-a))) at ht
    simpa only [add_sub_cancel_left,normalPlaneCoordinates_graph hn] using ht
  exact ht.eventually (notMem_tsupport_iff_eventuallyEq.mp hy)

lemma gradient_eq_zero_of_graph_extension_germ (a : Cover) {n : Cover} (hn : ‖n‖=1)
    (g ψ : Plane → ℝ) {F : Cover → ℝ} {y : Plane}
    (hF : F=ᶠ[𝓝 (a+normalGraph n g y)] graphHeightExtension a n ψ)
    (hy : y∉tsupport ψ) : gradient F (a+normalGraph n g y)=0 := by
  have hg := hF.trans (graphHeightExtension_eventually_zero a hn g ψ hy)
  simp [gradient,hg.fderiv_eq]

lemma graphSlopeNormal_inner_axis {n : Cover} (hn : ‖n‖=1) (p : Plane) :
    ⟪n,graphSlopeNormal n p⟫=(cmcWeight p)⁻¹ := by
  rw [graphSlopeNormal_weight hn,inner_smul_right,inner_sub_right,
    real_inner_self_eq_norm_sq,hn,one_pow,normalPlaneEmbedding_inner hn,sub_zero,mul_one]

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
