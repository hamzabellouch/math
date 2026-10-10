import Mathlib
import OAI.Geometry.CubicTorus.Profiles.CenteredJacobiChart

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem CenteredJacobiChart.weak_ground_state_equation
    {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (haeN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (c : CenteredJacobiChart E μ N)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) {u : SurfaceJet μ}
    (hu : u∈surfaceH1 μ)
    (hju : ∀ v∈surfaceH1 μ,surfaceJacobiB μ q u v=0)
    (hjw : ∀ v∈surfaceH1 μ,surfaceJacobiB μ q
      (surfaceSmoothJet μ (directionalNormalScalar N hN hp c.n)) v=0)
    (v : Lp ℝ 2 (spatialNormalMeasure μ : Measure Torus))
    (G : Lp Cover 2 (spatialNormalMeasure μ : Measure Torus))
    (haeu : ∀ᵐ z ∂(μ : Measure NormalBundle),u.1 z=v (quotientMap z.1) ∧
      u.2 z=G (quotientMap z.1))
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (_hsψ : HasCompactSupport ψ)
    (htψ : tsupport ψ⊆Metric.ball 0 (c.r/2)) :
    (∫ y,⟪cmcWeight (gradient c.g y)•
      (fderiv ℝ (fun z ↦ cubeCenter+normalGraph c.n c.g z) y).adjoint
        (G (quotientMap (cubeCenter+normalGraph c.n c.g y)))+
      v (quotientMap (cubeCenter+normalGraph c.n c.g y))•
        gradient (fun z ↦ cmcWeight (gradient c.g z)) y,
      cmcJacobian (gradient c.g y) (gradient ψ y)⟫)=0 := by
  let X : Plane → Cover := fun y ↦ cubeCenter+normalGraph c.n c.g y
  let w := directionalNormalScalar N hN hp c.n
  have hsub : Metric.ball (0 : Plane) (c.r/2)⊆Metric.ball 0 c.r :=
    Metric.ball_subset_ball (by linarith [c.r_pos])
  obtain ⟨F,hF,hFc,hFs,hFt,hFg⟩ := graph_compact_test_extension cubeCenter cubeCenter
    c.n_unit c.g c.rho_pos hψ (fun y hy ↦ c.image_disk y (Metric.ball_subset_closedBall (hsub (htψ hy))))
  have hFO : tsupport F⊆{x | ∀ i,0<x i ∧ x i<1} :=
    hFs.trans ((Metric.closedBall_subset_closedBall (by linarith [c.rho_pos])).trans
      (c.patch_in_U.trans c.U_in_cell))
  obtain ⟨f,hf⟩ := compact_test_periodization hF hFc hFO
  have hρ := c.rho_pos
  let φ := radialHeightCutoff cubeCenter c.ρ
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := radialDensityWeight_contDiff _ _ _
  have hφc : HasCompactSupport φ := radialDensityWeight_hasCompactSupport (by positivity) (by positivity)
  have hφs : tsupport φ⊆Metric.closedBall cubeCenter (2*c.ρ) :=
    radialDensityWeight_tsupport (by positivity) (by positivity)
  have hφR : tsupport φ⊆Metric.closedBall cubeCenter c.R :=
    hφs.trans (c.patch_in_U.trans (c.U_in_ball.trans Metric.ball_subset_closedBall))
  have hφb (x : Cover) : φ x∈Icc 0 1 :=
    ⟨radialDensityWeight_nonneg _ _ _ _,radialDensityWeight_le_one _ _ _ _⟩
  have hφF (x : Cover) (hx : x∈tsupport F) : φ x=1 :=
    radialHeightCutoff_one c.rho_pos (hFs hx)
  have hvw : surfaceSmoothJet μ w∈surfaceH1 μ :=
    (surfaceSmoothJet μ).range.le_topologicalClosure ⟨w,rfl⟩
  have hwr := surfaceH1_weak_wronskian μ q hu hvw hju hjw f
  have harea := localized_wronskian_graph_integral hE hμ cubeCenter c.n_unit c.lip
    (fun y _ ↦ (c.smooth.continuous_fderiv (by simp)).continuousAt) c.phase
    hφ hφc (hφs.trans c.patch_in_U) (hφs.trans (c.patch_in_U.trans c.U_in_cell))
    hφR hφb hN.continuous haeN hF hφF f w hf u v G haeu
  rw [harea] at hwr
  have he : (fun y ↦ ‖graphAreaVector c.n c.g y‖*
      ⟪w.val (X y) • G (quotientMap (X y))-
        v (quotientMap (X y)) • normalProjectedGradient N w.val (X y),
        normalProjectedGradient N F (X y)⟫)=
      fun y ↦ c.sign*⟪cmcWeight (gradient c.g y)•(fderiv ℝ X y).adjoint (G (quotientMap (X y)))+
        v (quotientMap (X y))•gradient (fun z ↦ cmcWeight (gradient c.g z)) y,
        cmcJacobian (gradient c.g y) (gradient ψ y)⟫ := by
    funext y
    by_cases hy : y∈Metric.ball (0 : Plane) c.r
    · have hnY := c.normal_disk y (Metric.ball_subset_closedBall hy)
      have ht : (fun z ↦ w.val (X z))=ᶠ[𝓝 y]
          fun z ↦ c.sign/cmcWeight (gradient c.g z) := by
        filter_upwards [Metric.isOpen_ball.eventually_mem hy] with z hz
        dsimp only [w,X]
        rw [directionalNormalScalar_apply]
        rw [c.normal_disk z (Metric.ball_subset_closedBall hz),inner_smul_right,
          graphSlopeNormal_inner_axis c.n_unit]
        exact (div_eq_mul_inv _ _).symm
      have hwv : w.val (X y)=c.sign/cmcWeight (gradient c.g y) := ht.eq_of_nhds
      have hwgrad : graphTangentialGradient c.n c.g (fun z ↦ w.val (X z)) y=
          graphTangentialGradient c.n c.g (fun z ↦ c.sign/cmcWeight (gradient c.g z)) y := by
        simp only [graphTangentialGradient,gradient,ht.fderiv_eq]
      have hψgrad : graphTangentialGradient c.n c.g (fun z ↦ F (X z)) y=
          graphTangentialGradient c.n c.g ψ y := by
        rw [show (fun z ↦ F (X z))=ψ from funext hFt]
      rw [normalProjectedGradient_graph_trace cubeCenter c.n_unit c.smooth c.sign_eq hnY w.property.1,
        normalProjectedGradient_graph_trace cubeCenter c.n_unit c.smooth c.sign_eq hnY hF,
        hwv,hwgrad,hψgrad]
      exact graph_wronskian_ground_state c.n_unit c.smooth cubeCenter ψ y c.sign
        (v (quotientMap (X y))) (G (quotientMap (X y)))
    · have hnψ : y∉tsupport ψ := fun h ↦ hy (hsub (htψ h))
      have hgF := gradient_eq_zero_of_graph_extension_germ cubeCenter c.n_unit c.g ψ (hFg y) hnψ
      have hgψ : gradient ψ y=0 := by simp [gradient,fderiv_of_notMem_tsupport ℝ hnψ]
      simp only [normalProjectedGradient,X] at hgF ⊢
      rw [hgF,hgψ]
      simp only [inner_zero_right,zero_smul,sub_zero,map_zero,mul_zero]
  change (∫ y,(fun y ↦ ‖graphAreaVector c.n c.g y‖*_) y)=0 at hwr
  rw [he,integral_const_mul] at hwr
  have hsign : c.sign≠0 := by rcases c.sign_eq with h|h <;> rw [h] <;> norm_num
  exact (mul_eq_zero.mp hwr).resolve_left hsign

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceChartPullback_periodic (μ : FiniteMeasure NormalBundle) {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (D : Set Plane) (X : Plane → Cover) (hX : Measurable (fun y ↦ quotientMap (X y)))
    {C : ℝ≥0∞} (hC : C≠⊤)
    (hdom : Measure.map (fun y ↦ quotientMap (X y)) (volume.restrict D)≤
      C•(spatialNormalMeasure μ : Measure Torus))
    (f : Cover → W) (hf : Continuous f) (hp : ∀ m x,f (x+latticeVector m)=f x) :
    surfaceChartPullback μ W D (fun y ↦ quotientMap (X y)) hX hC hdom
      (ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ
        ⟨fun z ↦ f z.1,hf.comp (continuous_subtype_val.comp continuous_fst)⟩)
      =ᵐ[volume.restrict D] fun y ↦ f (X y) := by
  let F : C(Torus,W) := ⟨fun a ↦ f (representative a),continuous_periodic_descent hf hp⟩
  have h := surfaceChartPullback_continuousMap μ D (fun y ↦ quotientMap (X y)) hX hC hdom F
  have he : F.comp ⟨normalProjection,normalProjection_continuous⟩=
      (⟨fun z : NormalBundle ↦ f z.1,hf.comp (continuous_subtype_val.comp continuous_fst)⟩ :
        C(NormalBundle,W)) := by
    apply ContinuousMap.ext
    intro z
    exact periodic_representative hp z.1
  rw [he] at h
  exact h.trans (Filter.Eventually.of_forall (fun y ↦ periodic_representative hp (X y)))

lemma surfaceChartPullback_smoothJet_value (μ : FiniteMeasure NormalBundle)
    (D : Set Plane) (X : Plane → Cover) (hX : Measurable (fun y ↦ quotientMap (X y)))
    {C : ℝ≥0∞} (hC : C≠⊤)
    (hdom : Measure.map (fun y ↦ quotientMap (X y)) (volume.restrict D)≤
      C•(spatialNormalMeasure μ : Measure Torus)) (f : smoothPeriodicScalars) :
    surfaceChartPullback μ ℝ D (fun y ↦ quotientMap (X y)) hX hC hdom (surfaceSmoothJet μ f).1
      =ᵐ[volume.restrict D]fun y ↦ f.val (X y) :=
  surfaceChartPullback_periodic μ D X hX hC hdom f.val f.property.1.continuous f.property.2

lemma surfaceChartPullback_smoothJet_gradient {μ : FiniteMeasure NormalBundle}
    {N : Cover → Cover} (hN : Continuous N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hn : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (D : Set Plane) (X : Plane → Cover) (hX : Measurable (fun y ↦ quotientMap (X y)))
    {C : ℝ≥0∞} (hC : C≠⊤)
    (hdom : Measure.map (fun y ↦ quotientMap (X y)) (volume.restrict D)≤
      C•(spatialNormalMeasure μ : Measure Torus)) (f : smoothPeriodicScalars) :
    surfaceChartPullback μ Cover D (fun y ↦ quotientMap (X y)) hX hC hdom (surfaceSmoothJet μ f).2
      =ᵐ[volume.restrict D]fun y ↦ gradient f.val (X y)-
        ⟪N (X y),gradient f.val (X y)⟫•N (X y) := by
  let G : Cover → Cover := fun x ↦ gradient f.val x-⟪N x,gradient f.val x⟫•N x
  have hG : Continuous G := (gradient_contDiff f.property.1).continuous.sub
    ((hN.inner (𝕜 := ℝ) (gradient_contDiff f.property.1).continuous).smul hN)
  have hGp : ∀ m x,G (x+latticeVector m)=G x := by
    intro m x
    simp only [G,hp,gradient_periodic f.property.2]
  have he : (surfaceSmoothJet μ f).2=ContinuousMap.toLp 2 (μ : Measure NormalBundle) ℝ
      (⟨fun z : NormalBundle ↦ G z.1,hG.comp (continuous_subtype_val.comp continuous_fst)⟩ :
        C(NormalBundle,Cover)) := by
    apply Lp.ext
    filter_upwards [(smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle),
      (⟨fun z : NormalBundle ↦ G z.1,hG.comp (continuous_subtype_val.comp continuous_fst)⟩ :
        C(NormalBundle,Cover)).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle),hn]
      with z hz hgz hnz
    change (surfaceSmoothJet μ f).2 z=smoothScalarGradient f z at hz
    rw [hz,hgz]
    change gradient f.val z.1-⟪(z.2 : Cover),gradient f.val z.1⟫•(z.2 : Cover)=G z.1
    simp only [G,hnz]
  rw [he]
  exact surfaceChartPullback_periodic μ D X hX hC hdom G hG hGp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem surfaceH1_chart_weak_chain_rule {μ : FiniteMeasure NormalBundle}
    {N : Cover → Cover} (hN : Continuous N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hn : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (D : Set Plane) (hD : MeasurableSet D) (X : Plane → Cover)
    (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    {C : ℝ≥0∞} (hC : C≠⊤)
    (hdom : Measure.map (fun y ↦ quotientMap (X y)) (volume.restrict D)≤
      C•(spatialNormalMeasure μ : Measure Torus))
    (htan : ∀ y∈D,∀ w : Plane,⟪N (X y),fderiv ℝ X y w⟫=0)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (φ : Plane → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφD : tsupport φ⊆D) (w : Plane) :
    let F : Plane → Torus := fun y ↦ quotientMap (X y)
    let mF := (continuous_quotientMap.comp hX.continuous).measurable
    let v := surfaceChartPullback μ ℝ D F mF hC hdom u.1
    let G := surfaceChartPullback μ Cover D F mF hC hdom u.2
    (∫ y in D,φ y*⟪G y,fderiv ℝ X y w⟫)=
      -(∫ y in D,fderiv ℝ φ y w*v y) := by
  let F : Plane → Torus := fun y ↦ quotientMap (X y)
  have mF : Measurable F := (continuous_quotientMap.comp hX.continuous).measurable
  let P := surfaceChartPullback μ ℝ D F mF hC hdom
  let Q := surfaceChartPullback μ Cover D F mF hC hdom
  let T₀ : Plane → Cover := fun y ↦ φ y•fderiv ℝ X y w
  let S₀ : Plane → ℝ := fun y ↦ fderiv ℝ φ y w
  have hT : MemLp T₀ 2 (volume.restrict D) :=
    (hφ.continuous.smul ((hX.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
      hsφ.smul_right
  have hS : MemLp S₀ 2 (volume.restrict D) :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hsφ.fderiv_apply ℝ w)
  let T := hT.toLp T₀
  let S := hS.toLp S₀
  let J : SurfaceJet μ → ℝ := fun v ↦ ⟪Q v.2,T⟫+⟪P v.1,S⟫
  have hJ : Continuous J :=
    ((Q.continuous.comp continuous_snd).inner (𝕜 := ℝ) continuous_const).add
      ((P.continuous.comp continuous_fst).inner (𝕜 := ℝ) continuous_const)
  have hform (v : SurfaceJet μ) : J v=∫ y in D,
      (φ y*⟪Q v.2 y,fderiv ℝ X y w⟫+fderiv ℝ φ y w*P v.1 y) := by
    dsimp only [J]
    rw [L2.inner_def,L2.inner_def,← integral_add (L2.integrable_inner (Q v.2) T)
      (L2.integrable_inner (P v.1) S)]
    apply integral_congr_ae
    filter_upwards [hT.coeFn_toLp,hS.coeFn_toLp] with y hTy hSy
    change T y=T₀ y at hTy
    change S y=S₀ y at hSy
    simp only [hTy,hSy,T₀,S₀,real_inner_smul_right,RCLike.inner_apply,RCLike.conj_to_real]
  have hzero : ∀ f : smoothPeriodicScalars,J (surfaceSmoothJet μ f)=0 := by
    intro f
    have hx : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ f.val (X y)) := f.property.1.comp hX
    let ψ : Plane → ℝ := fun y ↦ φ y*f.val (X y)
    have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.mul hx
    have hsψ : HasCompactSupport ψ := hsφ.mul_right
    rw [hform]
    calc
      _=(∫ y in D,fderiv ℝ ψ y w) := by
        apply integral_congr_ae
        filter_upwards [surfaceChartPullback_smoothJet_value μ D X mF hC hdom f,
          surfaceChartPullback_smoothJet_gradient hN hp hn D X mF hC hdom f,
          ae_restrict_mem hD] with y hv hg hy
        change P (surfaceSmoothJet μ f).1 y=_ at hv
        change Q (surfaceSmoothJet μ f).2 y=_ at hg
        rw [hv,hg,inner_sub_left,real_inner_smul_left,htan y hy w,mul_zero,sub_zero,
          inner_gradient_left]
        have hdφ := hφ.differentiable (by simp) y
        have hdx := hx.differentiable (by simp) y
        have hdf := f.property.1.differentiable (by simp) (X y)
        have hdX := hX.differentiable (by simp) y
        change _=fderiv ℝ (φ*(fun z ↦ f.val (X z))) y w
        have hchain : fderiv ℝ (fun z ↦ f.val (X z)) y=
            (fderiv ℝ f.val (X y)).comp (fderiv ℝ X y) := fderiv_comp y hdf hdX
        rw [fderiv_mul hdφ hdx,hchain]
        simp only [add_apply,smul_apply,
          ContinuousLinearMap.comp_apply,smul_eq_mul]
        ring
      _=(∫ y,fderiv ℝ ψ y w) :=
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ by
          have hnψ : y∉tsupport ψ := fun he ↦ hy (hφD (tsupport_mul_subset_left he))
          rw [fderiv_of_notMem_tsupport ℝ hnψ,zero_apply])
      _=0 := integral_compact_fderiv_zero hψ hsψ w
  have hc : IsClosed {v : SurfaceJet μ | J v=0} := isClosed_eq hJ continuous_const
  have hr : Set.range (surfaceSmoothJet μ)⊆{v | J v=0} := by
    rintro _ ⟨f,rfl⟩
    exact hzero f
  have huJ : J u=0 := closure_minimal hr hc hu
  have hvform : ⟪P u.1,S⟫=(∫ y in D,fderiv ℝ φ y w*P u.1 y) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hS.coeFn_toLp] with y hy
    change S y=S₀ y at hy
    simp only [hy,S₀,RCLike.inner_apply,RCLike.conj_to_real]
  have hgform : ⟪Q u.2,T⟫=(∫ y in D,φ y*⟪Q u.2 y,fderiv ℝ X y w⟫) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hT.coeFn_toLp] with y hy
    change T y=T₀ y at hy
    simp only [hy,T₀,real_inner_smul_right]
  change ⟪Q u.2,T⟫+⟪P u.1,S⟫=0 at huJ
  rw [hgform,hvform] at huJ
  exact eq_neg_of_add_eq_zero_left huJ

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def HasPlanarWeakGradient (D : Set Plane) (v : Plane → ℝ) (G : Plane → Plane) : Prop :=
  MemLp v 2 (volume.restrict D) ∧ MemLp G 2 (volume.restrict D) ∧
  ∀ φ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ⊆D →
    ∀ w : Plane,(∫ y in D,φ y*⟪G y,w⟫)= -(∫ y in D,fderiv ℝ φ y w*v y)

lemma memLp_variable_clm_on_compact {D : Set Plane} (hD : IsCompact D)
    {A : Plane → Cover →L[ℝ] Plane} (hA : Continuous A)
    (G : Lp Cover 2 (volume.restrict D)) :
    MemLp (fun y ↦ A y (G y)) 2 (volume.restrict D) := by
  obtain ⟨B,hB⟩ := hD.exists_bound_of_continuousOn hA.continuousOn
  have hm : AEStronglyMeasurable (fun y ↦ A y (G y)) (volume.restrict D) :=
    (show Continuous (fun p : (Cover →L[ℝ] Plane)×Cover ↦ p.1 p.2) from
      continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (hA.aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable G))
  apply (Lp.memLp G).of_le_mul hm
  filter_upwards [ae_restrict_mem hD.measurableSet] with y hy
  exact ((A y).le_opNorm (G y)).trans (mul_le_mul_of_nonneg_right (hB y hy) (norm_nonneg _))

theorem surfaceH1_hasPlanarWeakGradient {μ : FiniteMeasure NormalBundle}
    {N : Cover → Cover} (hN : Continuous N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hn : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (D : Set Plane) (hD : IsCompact D) (X : Plane → Cover)
    (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    {C : ℝ≥0∞} (hC : C≠⊤)
    (hdom : Measure.map (fun y ↦ quotientMap (X y)) (volume.restrict D)≤
      C•(spatialNormalMeasure μ : Measure Torus))
    (htan : ∀ y∈D,∀ w : Plane,⟪N (X y),fderiv ℝ X y w⟫=0)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) :
    let F : Plane → Torus := fun y ↦ quotientMap (X y)
    let mF := (continuous_quotientMap.comp hX.continuous).measurable
    let v := surfaceChartPullback μ ℝ D F mF hC hdom u.1
    let G := surfaceChartPullback μ Cover D F mF hC hdom u.2
    HasPlanarWeakGradient D v (fun y ↦ (fderiv ℝ X y).adjoint (G y)) := by
  let F : Plane → Torus := fun y ↦ quotientMap (X y)
  have mF : Measurable F := (continuous_quotientMap.comp hX.continuous).measurable
  let v := surfaceChartPullback μ ℝ D F mF hC hdom u.1
  let G := surfaceChartPullback μ Cover D F mF hC hdom u.2
  refine ⟨Lp.memLp v,memLp_variable_clm_on_compact hD
    (ContinuousLinearMap.adjoint.continuous.comp (hX.continuous_fderiv (by simp))) G,?_⟩
  intro φ hφ hsφ hφD w
  simp_rw [ContinuousLinearMap.adjoint_inner_left]
  exact surfaceH1_chart_weak_chain_rule hN hp hn D hD.measurableSet X hX hC hdom htan hu
    φ hφ hsφ hφD w

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma memLp_scalar_pair_integrable {u v : Plane → ℝ}
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    Integrable (fun y ↦ u y*v y) := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hu.toLp u) (hv.toLp v)).congr
  filter_upwards [hu.coeFn_toLp,hv.coeFn_toLp] with y hy hz
  simp only [hy,hz,RCLike.inner_apply,conj_trivial]
  ring

lemma memLp_vector_pair_integrable {u v : Plane → Plane}
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    Integrable (fun y ↦ ⟪u y,v y⟫) := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hu.toLp u) (hv.toLp v)).congr
  filter_upwards [hu.coeFn_toLp,hv.coeFn_toLp] with y hy hz
  rw [hy,hz]

theorem PlaneWeakGradient.vector_test {S : Set Plane} {u : Plane → ℝ} {G : Plane → Plane}
    (h : PlaneWeakGradient S u G) (hu : MemLp u 2 volume) (hG : MemLp G 2 volume)
    {F : Plane → Plane} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hc : HasCompactSupport F) (hs : tsupport F⊆S) :
    (∫ y,⟪G y,F y⟫)= -(∫ y,u y*planeDivergence F y) := by
  let e : Fin 2 → Plane := fun i ↦ EuclideanSpace.single i 1
  have hFi (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ F y i) :=
    (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).contDiff.comp hF
  have hci (i : Fin 2) : HasCompactSupport (fun y ↦ F y i) :=
    hc.mono' (fun y hy ↦ by contrapose! hy; simp [image_eq_zero_of_notMem_tsupport hy])
  have hsi (i : Fin 2) : tsupport (fun y ↦ F y i)⊆S :=
    (closure_mono (show Function.support (fun y ↦ F y i)⊆Function.support F from
      fun y hy hz ↦ hy (by simp [hz]))).trans hs
  have he (i : Fin 2) := h (e i) (fun y ↦ F y i) (hFi i) (hci i) (hsi i)
  have hleft (i : Fin 2) : Integrable (fun y ↦ ⟪G y,e i⟫*F y i) := by
    have ht : MemLp (fun y ↦ F y i • e i) 2 volume :=
      ((hFi i).continuous.smul continuous_const).memLp_of_hasCompactSupport (hci i).smul_right
    simpa only [inner_smul_right,mul_comm] using memLp_vector_pair_integrable hG ht
  have hright (i : Fin 2) : Integrable (fun y ↦ u y*fderiv ℝ (fun z ↦ F z i) y (e i)) :=
    memLp_scalar_pair_integrable hu
      (((hFi i).continuous_fderiv (by simp)).clm_apply continuous_const |>.memLp_of_hasCompactSupport
        ((hci i).fderiv_apply ℝ (e i)))
  have hproj (i : Fin 2) (y : Plane) :
      fderiv ℝ (fun z ↦ F z i) y (e i)=fderiv ℝ F y (e i) i := by
    exact congrArg (fun L : Plane →L[ℝ] ℝ ↦ L (e i))
      (((EuclideanSpace.proj i : Plane →L[ℝ] ℝ).hasFDerivAt.comp y
        (hF.differentiable (by simp) y).hasFDerivAt).fderiv)
  calc
    _=(∫ y,⟪G y,e 0⟫*F y 0)+(∫ y,⟪G y,e 1⟫*F y 1) := by
      rw [← integral_add (hleft 0) (hleft 1)]
      congr 1
      funext y
      rw [plane_inner_components]
      simp [e,EuclideanSpace.inner_single_right]
    _= -(∫ y,u y*fderiv ℝ (fun z ↦ F z 0) y (e 0))-
        (∫ y,u y*fderiv ℝ (fun z ↦ F z 1) y (e 1)) := by rw [he 0,he 1]; ring
    _= -(∫ y,u y*planeDivergence F y) := by
      rw [sub_eq_add_neg,← neg_add,← integral_add (hright 0) (hright 1)]
      congr 2
      funext y
      rw [hproj,hproj]
      simp only [planeDivergence,e]
      ring

theorem PlaneWeakGradient.mul_smooth {S : Set Plane} {u : Plane → ℝ} {G : Plane → Plane}
    (h : PlaneWeakGradient S u G) (hu : MemLp u 2 volume) (hG : MemLp G 2 volume)
    {q : Plane → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    PlaneWeakGradient S (fun y ↦ q y*u y)
      (fun y ↦ q y • G y+u y • gradient q y) := by
  intro v ψ hψ hc hs
  have hp := h v (fun y ↦ q y*ψ y) (hq.mul hψ) hc.mul_left
    (tsupport_mul_subset_right.trans hs)
  have h₁ : Integrable (fun y ↦ ⟪G y,v⟫*(q y*ψ y)) := by
    have ht : MemLp (fun y ↦ (q y*ψ y) • v) 2 volume :=
      ((hq.continuous.mul hψ.continuous).smul continuous_const).memLp_of_hasCompactSupport
        hc.mul_left.smul_right
    simpa only [inner_smul_right,mul_comm] using memLp_vector_pair_integrable hG ht
  have h₂ : Integrable (fun y ↦ u y*(fderiv ℝ q y v*ψ y)) :=
    memLp_scalar_pair_integrable hu
      ((((hq.continuous_fderiv (by simp)).clm_apply continuous_const).mul hψ.continuous).memLp_of_hasCompactSupport
        hc.mul_left)
  have h₃ : Integrable (fun y ↦ u y*(q y*fderiv ℝ ψ y v)) :=
    memLp_scalar_pair_integrable hu
      ((hq.continuous.mul ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
        (hc.fderiv_apply ℝ v).mul_left)
  have hprod (y : Plane) : u y*fderiv ℝ (fun z ↦ q z*ψ z) y v=
      u y*(fderiv ℝ q y v*ψ y)+u y*(q y*fderiv ℝ ψ y v) := by
    rw [fderiv_fun_mul (hq.differentiable (by simp) y) (hψ.differentiable (by simp) y)]
    simp only [add_apply,smul_apply,smul_eq_mul]
    ring
  simp_rw [hprod] at hp
  rw [integral_add h₂ h₃] at hp
  have hleft (y : Plane) : ⟪q y • G y+u y • gradient q y,v⟫*ψ y=
      ⟪G y,v⟫*(q y*ψ y)+u y*(fderiv ℝ q y v*ψ y) := by
    rw [inner_add_left,real_inner_smul_left,real_inner_smul_left,inner_gradient_left]
    ring
  simp_rw [hleft]
  rw [integral_add h₁ h₂]
  have hright : (∫ y,q y*u y*fderiv ℝ ψ y v)=(∫ y,u y*(q y*fderiv ℝ ψ y v)) := by
    congr 1; funext y; ring
  rw [hright]
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma HasPlanarWeakGradient.extend_zero {D S : Set Plane} (hD : MeasurableSet D)
    {v : Plane → ℝ} {G : Plane → Plane} (h : HasPlanarWeakGradient D v G) (hSD : S⊆D) :
    PlaneWeakGradient S (D.indicator v) (D.indicator G) := by
  intro w ψ hψ hc hs
  have he := h.2.2 ψ hψ hc (hs.trans hSD) w
  have hl : (fun y ↦ ⟪D.indicator G y,w⟫*ψ y)=D.indicator (fun y ↦ ⟪G y,w⟫*ψ y) := by
    funext y
    by_cases hy : y∈D <;> simp [hy]
  have hr : (fun y ↦ D.indicator v y*fderiv ℝ ψ y w)=D.indicator (fun y ↦ v y*fderiv ℝ ψ y w) := by
    funext y
    by_cases hy : y∈D <;> simp [hy]
  rw [hl,hr,integral_indicator hD,integral_indicator hD]
  simpa only [mul_comm] using he

lemma HasPlanarWeakGradient.zero_extension_memLp {D : Set Plane} (hD : MeasurableSet D)
    {v : Plane → ℝ} {G : Plane → Plane} (h : HasPlanarWeakGradient D v G) :
    MemLp (D.indicator v) 2 volume ∧ MemLp (D.indicator G) 2 volume :=
  ⟨(memLp_indicator_iff_restrict hD).mpr h.1,(memLp_indicator_iff_restrict hD).mpr h.2.1⟩

lemma memLp_continuous_smul_zero_extension {D : Set Plane} (hD : IsCompact D)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {v : Plane → W} (hv : MemLp v 2 (volume.restrict D))
    {q : Plane → ℝ} (hq : Continuous q) :
    MemLp (fun y ↦ q y • D.indicator v y) 2 volume := by
  have hm : MemLp (D.indicator v) 2 volume := (memLp_indicator_iff_restrict hD.measurableSet).mpr hv
  obtain ⟨B,hB⟩ := hD.exists_bound_of_continuousOn hq.continuousOn
  apply hm.of_le_mul (c := B) (hq.aestronglyMeasurable.smul hm.aestronglyMeasurable)
  filter_upwards [] with y
  change ‖q y • D.indicator v y‖≤B*‖D.indicator v y‖
  by_cases hy : y∈D
  · rw [Set.indicator_of_mem hy,norm_smul]
    exact mul_le_mul_of_nonneg_right (hB y hy) (norm_nonneg _)
  · simp only [Set.indicator_of_notMem hy,smul_zero,norm_zero,mul_zero,le_refl]

lemma memLp_zero_extension_smul_continuous {D : Set Plane} (hD : IsCompact D)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {v : Plane → ℝ} (hv : MemLp v 2 (volume.restrict D))
    {q : Plane → W} (hq : Continuous q) :
    MemLp (fun y ↦ D.indicator v y • q y) 2 volume := by
  have hm : MemLp (D.indicator v) 2 volume := (memLp_indicator_iff_restrict hD.measurableSet).mpr hv
  obtain ⟨B,hB⟩ := hD.exists_bound_of_continuousOn hq.continuousOn
  apply hm.of_le_mul (c := B) (hm.aestronglyMeasurable.smul hq.aestronglyMeasurable)
  filter_upwards [] with y
  change ‖D.indicator v y • q y‖≤B*‖D.indicator v y‖
  by_cases hy : y∈D
  · rw [Set.indicator_of_mem hy,norm_smul,mul_comm]
    exact mul_le_mul_of_nonneg_right (hB y hy) (norm_nonneg _)
  · simp only [Set.indicator_of_notMem hy,zero_smul,norm_zero,mul_zero,le_refl]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace CenteredJacobiChart
variable {E : Set Torus} {μ : FiniteMeasure NormalBundle} {N : Cover → Cover}

def parameter (c : CenteredJacobiChart E μ N) : Plane → Cover :=
  fun y ↦ cubeCenter+normalGraph c.n c.g y

lemma parameter_smooth (c : CenteredJacobiChart E μ N) :
    ContDiff ℝ (⊤ : ℕ∞) c.parameter :=
  contDiff_const.add ((normalPlaneLinearIsometry c.n).contDiff.add (c.smooth.smul contDiff_const))

lemma parameter_measurable (c : CenteredJacobiChart E μ N) :
    Measurable (fun y ↦ quotientMap (c.parameter y)) :=
  (continuous_quotientMap.comp c.parameter_smooth.continuous).measurable

def value (c : CenteredJacobiChart E μ N) (u : SurfaceJet μ) :=
  surfaceChartPullback μ ℝ (Metric.closedBall 0 c.r) (fun y ↦ quotientMap (c.parameter y))
    c.parameter_measurable c.C_finite c.domination u.1

def ambientGradient (c : CenteredJacobiChart E μ N) (u : SurfaceJet μ) :=
  surfaceChartPullback μ Cover (Metric.closedBall 0 c.r) (fun y ↦ quotientMap (c.parameter y))
    c.parameter_measurable c.C_finite c.domination u.2

def planarGradient (c : CenteredJacobiChart E μ N) (u : SurfaceJet μ) (y : Plane) : Plane :=
  (fderiv ℝ c.parameter y).adjoint (c.ambientGradient u y)

def weight (c : CenteredJacobiChart E μ N) (y : Plane) : ℝ := cmcWeight (gradient c.g y)

lemma weight_smooth (c : CenteredJacobiChart E μ N) : ContDiff ℝ (⊤ : ℕ∞) c.weight :=
  cmcWeight_contDiff.comp (plane_gradient_contDiff c.smooth)

def weightedValue (c : CenteredJacobiChart E μ N) (u : SurfaceJet μ) (y : Plane) : ℝ :=
  c.weight y*(Metric.closedBall (0 : Plane) c.r).indicator (c.value u) y

def weightedGradient (c : CenteredJacobiChart E μ N) (u : SurfaceJet μ) (y : Plane) : Plane :=
  c.weight y • (Metric.closedBall (0 : Plane) c.r).indicator (c.planarGradient u) y+
    (Metric.closedBall (0 : Plane) c.r).indicator (c.value u) y • gradient c.weight y

lemma hasPlanarWeakGradient (c : CenteredJacobiChart E μ N)
    (hN : Continuous N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) :
    HasPlanarWeakGradient (Metric.closedBall 0 c.r) (c.value u) (c.planarGradient u) := by
  apply surfaceH1_hasPlanarWeakGradient hN hp hae _ (isCompact_closedBall _ _)
    c.parameter c.parameter_smooth c.C_finite c.domination _ hu
  intro y hy w
  change ⟪N (cubeCenter+normalGraph c.n c.g y),fderiv ℝ c.parameter y w⟫=0
  rw [c.normal_disk y hy]
  exact normalGraph_translated_tangency c.n_unit c.smooth cubeCenter c.sign y w

lemma weighted_weak_gradient (c : CenteredJacobiChart E μ N)
    (hN : Continuous N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) :
    MemLp (c.weightedValue u) 2 volume ∧ MemLp (c.weightedGradient u) 2 volume ∧
    PlaneWeakGradient (Metric.ball 0 (c.r/2)) (c.weightedValue u) (c.weightedGradient u) := by
  have hg := c.hasPlanarWeakGradient hN hp hae hu
  have hu0 := hg.zero_extension_memLp measurableSet_closedBall
  have hsub : Metric.ball (0 : Plane) (c.r/2)⊆Metric.closedBall 0 c.r :=
    (Metric.ball_subset_ball (by linarith [c.r_pos])).trans Metric.ball_subset_closedBall
  refine ⟨?_,?_,(hg.extend_zero measurableSet_closedBall hsub).mul_smooth hu0.1 hu0.2 c.weight_smooth⟩
  · exact memLp_continuous_smul_zero_extension (isCompact_closedBall _ _) hg.1 c.weight_smooth.continuous
  · exact (memLp_continuous_smul_zero_extension (isCompact_closedBall _ _) hg.2.1 c.weight_smooth.continuous).add
      (memLp_zero_extension_smul_continuous (isCompact_closedBall _ _) hg.1
        (plane_gradient_contDiff c.weight_smooth).continuous)

lemma representatives_ae (c : CenteredJacobiChart E μ N) {u : SurfaceJet μ}
    (v : Lp ℝ 2 (spatialNormalMeasure μ : Measure Torus))
    (G : Lp Cover 2 (spatialNormalMeasure μ : Measure Torus))
    (hv : spatialPullback μ ℝ v=u.1) (hG : spatialPullback μ Cover G=u.2) :
    ∀ᵐ y ∂volume.restrict (Metric.closedBall (0 : Plane) c.r),
      c.value u y=v (quotientMap (c.parameter y)) ∧
      c.ambientGradient u y=G (quotientMap (c.parameter y)) := by
  have h₁ : c.value u=ᵐ[volume.restrict (Metric.closedBall (0 : Plane) c.r)]
      fun y ↦ v (quotientMap (c.parameter y)) := by
    unfold value surfaceChartPullback
    simp only [ContinuousLinearMap.comp_apply,← hv,spatialPushdown_pullback]
    exact dominatedL2Pullback_ae _ _ _ _ _ _ _
  have h₂ : c.ambientGradient u=ᵐ[volume.restrict (Metric.closedBall (0 : Plane) c.r)]
      fun y ↦ G (quotientMap (c.parameter y)) := by
    unfold ambientGradient surfaceChartPullback
    simp only [ContinuousLinearMap.comp_apply,← hG,spatialPushdown_pullback]
    exact dominatedL2Pullback_ae _ _ _ _ _ _ _
  exact h₁.and h₂

theorem weighted_divergence (c : CenteredJacobiChart E μ N)
    (hE : MeasurableSet E) (hμ : IsNormalMeasure E μ)
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (haeN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) {u : SurfaceJet μ}
    (hu : u∈surfaceH1 μ) (hju : ∀ v∈surfaceH1 μ,surfaceJacobiB μ q u v=0)
    (hjw : ∀ v∈surfaceH1 μ,surfaceJacobiB μ q
      (surfaceSmoothJet μ (directionalNormalScalar N hN hp c.n)) v=0)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ⊆Metric.ball 0 (c.r/2)) :
    (∫ y,fderiv ℝ ψ y (cmcJacobian (gradient c.g y) (c.weightedGradient u y)))=0 := by
  obtain ⟨v,G,hv,hG,haeu⟩ := surfaceH1_spatial_representatives hN.continuous hp haeN hu
  have hw := c.weak_ground_state_equation hE hμ hN hp haeN q hu hju hjw v G haeu hψ hcψ hsψ
  rw [← hw]
  have ha := (ae_restrict_iff' measurableSet_closedBall).mp (c.representatives_ae v G hv hG)
  apply integral_congr_ae
  filter_upwards [ha] with y hy
  by_cases hys : y∈Metric.closedBall (0 : Plane) c.r
  · dsimp only [weightedGradient,planarGradient,weight]
    rw [Set.indicator_of_mem hys,Set.indicator_of_mem hys,(hy hys).1]
    dsimp only [planarGradient]
    rw [(hy hys).2,← inner_gradient_left,real_inner_comm,← cmcJacobian_symmetric]
    rfl
  · have hnt : y∉tsupport ψ := by
      intro ht
      apply hys
      exact Metric.ball_subset_closedBall
        (Metric.ball_subset_ball (by linarith [c.r_pos]) (hsψ ht))
    have hd : fderiv ℝ ψ y=0 := fderiv_of_notMem_tsupport ℝ hnt
    have hg : gradient ψ y=0 := by simp [gradient,hd]
    rw [hd,hg]
    simp only [zero_apply,map_zero,inner_zero_right]

end CenteredJacobiChart
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cmc_weak_continuous_C1 {p : Plane → Plane} (hp : Continuous p)
    (hpb : ∀ y,‖p y‖≤1) {R α D : ℝ} (hR : 0<R) (hα : 0<α) (hα1 : α≤1) (hD : 0≤D)
    (hHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*(dist x y)^α)
    {u : Plane → ℝ} {G : Plane → Plane}
    (hu : MemLp u 2 volume) (hG : MemLp G 2 volume)
    (hc : ContinuousOn u (Metric.ball 0 R))
    (hg : PlaneWeakGradient (Metric.ball 0 R) u G)
    (hd : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 R → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)))=0) :
    ∃ s K β : ℝ,0<s ∧ s≤R/16 ∧ 0≤K ∧ 0<β ∧ β≤1 ∧
      ContDiffOn ℝ 1 u (Metric.ball 0 s) ∧
      ∀ x∈Metric.ball (0 : Plane) s,∀ y∈Metric.ball (0 : Plane) s,
        dist (fderiv ℝ u x) (fderiv ℝ u y)≤K*(dist x y)^β := by
  have hg' := hg.congr hu.coeFn_toLp hG.coeFn_toLp
  have hd' : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 R →
      (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (hG.toLp G y)))=0 := by
    intro ψ hψ hs hts
    rw [← hd ψ hψ hs hts]
    apply integral_congr_ae
    filter_upwards [hG.coeFn_toLp] with y hy
    rw [hy]
  obtain ⟨H,s,K,β,hs,hsR,hK,hβ,hβ1,hH,hHe,hHp⟩ :=
    cmc_linearized_holder_gradient hp hpb hR hα hα1 hD hHolder
      (hu.toLp u) (hG.toLp G) hg' hd'
  have hsub : Metric.ball (0 : Plane) s⊆Metric.ball 0 R := Metric.ball_subset_ball (by linarith)
  have he : H=ᵐ[volume.restrict (Metric.ball (0 : Plane) s)] G :=
    hHe.trans (ae_mono Measure.restrict_le_self hG.coeFn_toLp)
  have hw := (hg.mono hsub).local_congr measurableSet_ball EventuallyEq.rfl he
  obtain ⟨hC,hCd⟩ := hw.holder_C1 hs (hc.mono hsub) hH hHp
  exact ⟨s/4,K,β,by positivity,by linarith,hK,hβ,hβ1,hC,hCd⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeSlopeClamp (p : Plane) : Plane := (max (1 : ℝ) ‖p‖)⁻¹ • p

lemma planeSlopeClamp_continuous : Continuous planeSlopeClamp := by
  exact (continuous_const.max continuous_norm).inv₀ (fun p ↦
    (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖p‖)).ne') |>.smul continuous_id

lemma planeSlopeClamp_norm (p : Plane) : ‖planeSlopeClamp p‖≤1 := by
  have hm : 0 < max (1 : ℝ) ‖p‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [planeSlopeClamp,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hm.le),← div_eq_inv_mul]
  exact (div_le_one₀ hm).mpr (le_max_right _ _)

lemma planeSlopeClamp_eq {p : Plane} (hp : ‖p‖≤1) : planeSlopeClamp p=p := by
  simp only [planeSlopeClamp,max_eq_left hp,inv_one,one_smul]

lemma smooth_cmc_coefficient_lipschitz {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (r : ℝ) : ∃ L : ℝ,0≤L ∧ ∀ x∈Metric.closedBall (0 : Plane) r,
      ∀ y∈Metric.closedBall (0 : Plane) r,
      ‖cmcJacobian (gradient g x)-cmcJacobian (gradient g y)‖≤L*dist x y := by
  obtain ⟨L,hL⟩ := (cmcJacobian_contDiff.comp (plane_gradient_contDiff hg)).contDiffOn.exists_lipschitzOnWith
    (by simp) (convex_closedBall (0 : Plane) r) (isCompact_closedBall (0 : Plane) r)
  refine ⟨L,L.coe_nonneg,fun x hx y hy ↦ ?_⟩
  simpa only [dist_eq_norm,Function.comp_def] using hL.dist_le_mul x hx y hy

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem CenteredJacobiChart.continuous_representative_C1
    {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (haeN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (c : CenteredJacobiChart E μ N)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) {u : SurfaceJet μ}
    (hu : u∈surfaceH1 μ) (hju : ∀ v∈surfaceH1 μ,surfaceJacobiB μ q u v=0)
    (hjw : ∀ v∈surfaceH1 μ,surfaceJacobiB μ q
      (surfaceSmoothJet μ (directionalNormalScalar N hN hp c.n)) v=0)
    {F : Plane → ℝ} (hF : ContinuousOn F (Metric.ball 0 c.r))
    (heF : F=ᵐ[volume.restrict (Metric.closedBall (0 : Plane) c.r)] c.value u) :
    ∃ s : ℝ,0<s ∧ s≤c.r/32 ∧ ContDiffOn ℝ 1 F (Metric.ball 0 s) := by
  let D := Metric.closedBall (0 : Plane) c.r
  let R := c.r/2
  let U : Plane → ℝ := fun y ↦ c.weight y*D.indicator F y
  let p : Plane → Plane := fun y ↦ planeSlopeClamp (gradient c.g y)
  have hR : 0<R := half_pos c.r_pos
  have hsub : Metric.ball (0 : Plane) R⊆Metric.closedBall 0 c.r :=
    (Metric.ball_subset_ball (by dsimp [R]; linarith [c.r_pos])).trans Metric.ball_subset_closedBall
  have hsub' : Metric.ball (0 : Plane) R⊆Metric.ball 0 c.r :=
    Metric.ball_subset_ball (by dsimp [R]; linarith [c.r_pos])
  have hpC : Continuous p := planeSlopeClamp_continuous.comp (plane_gradient_contDiff c.smooth).continuous
  have hpb (y : Plane) : ‖p y‖≤1 := planeSlopeClamp_norm _
  have hpeq (y : Plane) (hy : y∈Metric.ball (0 : Plane) R) : p y=gradient c.g y :=
    planeSlopeClamp_eq ((c.slope_disk y (hsub hy)).trans (by norm_num))
  obtain ⟨L,hL,hLip⟩ := smooth_cmc_coefficient_lipschitz c.smooth c.r
  have hHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤L*(dist x y)^(1 : ℝ) := by
    intro x hx y hy
    rw [hpeq x hx,hpeq y hy,Real.rpow_one]
    exact hLip x (hsub hx) y (hsub hy)
  have hUW : U=ᵐ[volume] c.weightedValue u := by
    have he := (ae_restrict_iff' measurableSet_closedBall).mp heF
    filter_upwards [he] with y hy
    by_cases hys : y∈D
    · simp only [U,CenteredJacobiChart.weightedValue,D,Set.indicator_of_mem hys,hy hys]
    · simp only [U,CenteredJacobiChart.weightedValue,D,Set.indicator_of_notMem hys,mul_zero]
  obtain ⟨huL,hGL,hgrad⟩ := c.weighted_weak_gradient hN.continuous hp haeN hu
  have hUL : MemLp U 2 volume := (memLp_congr_ae hUW).mpr huL
  have huC : ContinuousOn U (Metric.ball 0 R) := by
    apply (c.weight_smooth.continuous.continuousOn.mul (hF.mono hsub')).congr
    intro y hy
    simp only [U,D,Pi.mul_apply,Set.indicator_of_mem (hsub hy)]
  have huG : PlaneWeakGradient (Metric.ball 0 R) U (c.weightedGradient u) :=
    hgrad.congr hUW EventuallyEq.rfl
  have hdiv : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 R →
      (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (c.weightedGradient u y)))=0 := by
    intro ψ hψ hc hs
    have he := c.weighted_divergence hE hμ hN hp haeN q hu hju hjw hψ hc hs
    rw [← he]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y∈Metric.ball (0 : Plane) R
    · rw [hpeq y hy]
    · rw [fderiv_of_notMem_tsupport ℝ (fun ht ↦ hy (hs ht))]
      rfl
  obtain ⟨s,K,β,hs,hsR,_,_,_,hCs,_⟩ := cmc_weak_continuous_C1 hpC hpb hR
    (show (0 : ℝ)<1 by norm_num) (le_refl (1 : ℝ)) hL hHolder hUL hGL huC huG hdiv
  refine ⟨s,hs,by dsimp [R] at hsR; linarith,?_⟩
  have hsD : Metric.ball (0 : Plane) s⊆Metric.closedBall 0 c.r :=
    (Metric.ball_subset_ball (by dsimp [R] at hsR; linarith [c.r_pos])).trans Metric.ball_subset_closedBall
  have hq0 : ∀ y∈Metric.ball (0 : Plane) s,c.weight y≠0 := fun y _ ↦ (cmcWeight_pos _).ne'
  apply (hCs.div (c.weight_smooth.of_le (by simp)).contDiffOn hq0).congr
  intro y hy
  change F y=(c.weight y*D.indicator F y)/c.weight y
  rw [Set.indicator_of_mem (hsD hy),mul_div_cancel_left₀ _ (hq0 y hy)]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma sibling_continuous_indicator_positive_piece {α : Type*} [TopologicalSpace α]
    {f : α → ℝ} (hf : Continuous f) {D : Set α}
    (hDo : ∃ U : Set α,IsOpen U ∧ D={x | 0<f x}∩U)
    (hDc : ∃ C : Set α,IsClosed C ∧ D={x | 0<f x}∩C) :
    Continuous (D.indicator f) := by
  obtain ⟨U,hU,hDU⟩ := hDo
  obtain ⟨C,hC,hDC⟩ := hDc
  have hD : IsOpen D := by rw [hDU]; exact (isOpen_lt continuous_const hf).inter hU
  have hpos : closure D⊆{x | 0≤f x} :=
    (isClosed_le continuous_const hf).closure_subset_iff.mpr (by
      intro x hx
      rw [hDU] at hx
      exact (show 0<f x from hx.1).le)
  have hcls : closure D⊆C := hC.closure_subset_iff.mpr (by
    intro x hx
    rw [hDC] at hx
    exact hx.2)
  apply continuous_indicator _ hf.continuousOn
  intro x hx
  have hf0 := hpos hx.1
  apply le_antisymm _ hf0
  by_contra hh
  have hxD : x∈D := by rw [hDC]; exact ⟨lt_of_not_ge hh,hcls hx.1⟩
  exact hx.2 (by simpa only [hD.interior_eq] using hxD)

end CubicTorus
end
end
end

end OAI
