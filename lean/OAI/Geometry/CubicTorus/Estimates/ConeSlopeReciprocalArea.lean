import Mathlib
import OAI.Geometry.CubicTorus.Regularity.NormalCoverMap

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem coverC1BoundaryAt_physical_patch {A : Set Cover} (hA : MeasurableSet A)
    {p : Cover} (hp : p ∈ coverEssentialBoundary A) (hC : CoverC1BoundaryAt A p) :
    ∃ (a n : Cover) (g : Plane → ℝ) (R : ℝ) (U : Set Cover),
      ‖n‖ = 1 ∧ LipschitzWith (1/4) g ∧ 0 < R ∧
      (∀ y ∈ Metric.closedBall (0 : Plane) R, ContDiffAt ℝ 1 g y) ∧
      IsOpen U ∧ p ∈ U ∧ U ⊆ Metric.ball a R ∧
      (∀ x ∈ U, x ∈ coverEssentialBoundary A ↔
        normalGraph n g (normalPlaneCoordinates n (x-a))=x-a) ∧
      ((∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ graphSignedHeight a n g x < 0)) ∨
       (∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ 0 < graphSignedHeight a n g x))) := by
  obtain ⟨n,b,s,G,hn,hs,hb,hG,hGc,_,hcover⟩ := hC
  let a := p+s • b
  let g := dilatedGraph s G
  let R := 3*s/(544*8192)
  let r := s/(544*16384)
  have hR : 0 < R := by dsimp only [R]; positivity
  have hr : 0 < r := by dsimp only [r]; positivity
  have hg := dilatedGraph_lipschitz hG hs
  have hc (y : Plane) (hy : y ∈ Metric.closedBall (0 : Plane) R) : ContDiffAt ℝ 1 g y := by
    apply dilatedGraph_contDiffAt
    apply hGc.contDiffAt
    apply Metric.isOpen_ball.mem_nhds
    simp only [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hs).le]
    apply (inv_mul_lt_iff₀ hs).mpr
    have hh : ‖y‖ ≤ R := by simpa using hy
    dsimp only [R] at hh
    nlinarith
  have hba : Metric.ball p r ⊆ Metric.ball a R := by
    intro x hx
    have hd := dist_triangle x p a
    have hpa : dist p a = s*‖b‖ := by simp only [a,dist_eq_norm,sub_add_eq_sub_sub,sub_self,zero_sub,norm_neg,norm_smul,Real.norm_of_nonneg hs.le]
    rw [hpa] at hd
    have hx' : dist x p < r := hx
    change dist x a < R
    dsimp only [R,r] at hx' ⊢
    nlinarith [mul_le_mul_of_nonneg_left hb hs.le]
  have hbd (x : Cover) (hx : x ∈ Metric.ball p r) :
      x ∈ coverEssentialBoundary A ↔ normalGraph n g (normalPlaneCoordinates n (x-a))=x-a := by
    let z := s⁻¹ • (x-p)
    have hz : z ∈ Metric.ball (0 : Cover) (1/(544*8192)) := by
      simp only [Metric.mem_ball,dist_zero_right,z,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hs).le]
      apply (inv_mul_lt_iff₀ hs).mpr
      have hh : ‖x-p‖ < r := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
      dsimp only [r] at hh
      nlinarith
    have hxz : p+s • z=x := by simp only [z,smul_smul,mul_inv_cancel₀ hs.ne',one_smul,add_sub_cancel]
    have hxa : x-a=s • (z-b) := by
      simp only [a,z,smul_sub,smul_smul,mul_inv_cancel₀ hs.ne',one_smul]
      abel
    have he : normalGraph n g (normalPlaneCoordinates n (x-a)) =
        s • normalGraph n G (normalPlaneCoordinates n (z-b)) := by
      rw [normalGraph_dilated n G hs.ne',hxa,map_smul,smul_smul,inv_mul_cancel₀ hs.ne',one_smul]
    rw [he,hxa,smul_right_inj hs.ne']
    simpa only [hxz] using hcover z hz

  obtain ⟨W,hW,hpW,hWU,hphase⟩ := cover_graph_boundary_phases hA a hn hg.continuous
    (Metric.isOpen_ball.mem_nhds (by simpa using hr)) hp (fun x hx hb ↦ (hbd x hx).mp hb)
  refine ⟨a,n,g,R,W,hn,hg,hR,hc,hW,hpW,hWU.trans hba,fun x hx ↦ hbd x (hWU hx),?_⟩
  exact hphase.symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma tangentialDivergence_neg_normal (F : Cover → Cover) (x v : Cover) :
    tangentialDivergence F x (-v)=tangentialDivergence F x v := by
  simp only [tangentialDivergence,map_neg,inner_neg_neg]

lemma reverseBlowupNormal_stationary (ν : FiniteMeasure BlowupNormalBundle)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (_hs : HasCompactSupport F) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(ν.map reverseBlowupNormal : Measure BlowupNormalBundle)) =
      ∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle) := by
  rw [FiniteMeasure.toMeasure_map,integral_map continuous_reverseBlowupNormal.measurable.aemeasurable
    (continuous_blowupTangentTest hF).aestronglyMeasurable]
  exact integral_congr_ae (ae_of_all _ fun z ↦ tangentialDivergence_neg_normal F z.1 z.2)

lemma graph_superlevel_compl_ae {A U : Set Cover} (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : Continuous g)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ graphHeightExtension a n g x < ⟪n,x-a⟫)) :
    ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ Aᶜ ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x) := by
  have hnz : ∀ᵐ x : Cover ∂volume, ⟪n,x-a⟫ ≠ graphHeightExtension a n g x := by
    rw [ae_iff]
    simpa only [not_not] using graph_trace_volume_zero a hn hg
  filter_upwards [hgraph,hnz] with x hx hne hU
  rw [mem_compl_iff,hx hU,not_lt]
  exact ⟨fun h ↦ lt_of_le_of_ne h hne,le_of_lt⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem strict_C1_patch_stationary {A : Set Cover} (hA : MeasurableSet A)
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A (Metric.closedBall (0 : Cover) 1) =
      (ν : Measure BlowupNormalBundle) {z | z.1 ∈ Metric.closedBall (0 : Cover) 1})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle))=0 ∧
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    {p : Cover} (hp : p ∈ coverEssentialBoundary A) (hpn : ‖p‖ < 1)
    (hC : CoverC1BoundaryAt A p) :
    ∃ (a n : Cover) (g : Plane → ℝ) (R ρ : ℝ),
      ‖n‖=1 ∧ LipschitzWith (1/4) g ∧ 0<R ∧ 0<ρ ∧
      (∀ y ∈ Metric.closedBall (0 : Plane) R, ContDiffAt ℝ 1 g y) ∧
      Metric.closedBall p (2*ρ) ⊆ Metric.ball a R ∧
      (∀ x ∈ Metric.closedBall p (2*ρ), x ∈ coverEssentialBoundary A ↔
        normalGraph n g (normalPlaneCoordinates n (x-a))=x-a) ∧
      ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
        tsupport F ⊆ Metric.closedBall p ρ →
        (∫ y : Plane, tangentialDivergence F (a+normalGraph n g y)
          (graphSlopeNormal n (gradient g y))*‖graphAreaVector n g y‖)=0 := by
  obtain ⟨a,n,g,R,U,hn,hg,hR,hc,hU,hpU,hUR,hbd,hphase⟩ :=
    coverC1BoundaryAt_physical_patch hA hp hC
  have hpB : p ∈ Metric.ball (0 : Cover) 1 := by simpa using hpn
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp
    ((hU.inter Metric.isOpen_ball).mem_nhds ⟨hpU,hpB⟩)
  let ρ := r/3
  have hρ : 0<ρ := by dsimp only [ρ]; positivity
  have hsub : Metric.closedBall p (2*ρ) ⊆ U ∩ Metric.ball (0 : Cover) 1 := by
    apply Subset.trans _ hrsub
    exact Metric.closedBall_subset_ball (by dsimp only [ρ]; linarith)
  have hsubU := hsub.trans inter_subset_left
  have hsubO := hsub.trans (inter_subset_right.trans Metric.ball_subset_closedBall)
  refine ⟨a,n,g,R,ρ,hn,hg,hR,hρ,hc,hsubU.trans hUR,
    fun x hx ↦ hbd x (hsubU hx),?_⟩
  intro F hF hsF
  let φ := radialHeightCutoff p ρ
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := radialDensityWeight_contDiff _ _ _
  have hsφ : HasCompactSupport φ := radialDensityWeight_hasCompactSupport (by positivity) (by positivity)
  have hφs : tsupport φ ⊆ Metric.closedBall p (2*ρ) :=
    radialDensityWeight_tsupport (by positivity) (by positivity)
  have hφU := hφs.trans hsubU
  have hφO := hφs.trans hsubO
  have hφR := hφU.trans (hUR.trans Metric.ball_subset_closedBall)
  have hφb (x : Cover) : φ x ∈ Icc 0 1 :=
    ⟨radialDensityWeight_nonneg _ _ _ _,radialDensityWeight_le_one _ _ _ _⟩
  have hφF (x : Cover) (hx : x ∈ tsupport F) : φ x=1 := radialHeightCutoff_one hρ (hsF hx)
  have hFs : HasCompactSupport F := (isCompact_closedBall p ρ).of_isClosed_subset isClosed_closure hsF
  have hFO : tsupport F ⊆ Metric.closedBall (0 : Cover) 1 :=
    hsF.trans ((Metric.closedBall_subset_closedBall (by linarith)).trans hsubO)
  have hdc (y : Plane) (hy : y ∈ Metric.closedBall (0 : Plane) R) : ContinuousAt (fderiv ℝ g) y :=
    (hc y hy).continuousAt_fderiv (by norm_num)
  rcases hphase with hphase|hphase
  · have hp' : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x) := by
      filter_upwards [hphase] with x hx hU
      simpa only [graphSignedHeight,sub_neg] using hx hU
    exact blowup_C1graph_stationary hA a hn hg hdc hp' heq
      (fun F hF _ hs _ ↦ (hflux F hF hs).2) hφ hsφ hφU hφO hφR hφb
      hF hFs hφF (hflux F hF hFO).1
  · have hp' : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ graphHeightExtension a n g x < ⟪n,x-a⟫) := by
      filter_upwards [hphase] with x hx hU
      simpa only [graphSignedHeight,sub_pos] using hx hU
    have hphase' := graph_superlevel_compl_ae a hn hg.continuous hp'
    have heq' := coverLocalPerimeter_normal_compl hA Metric.isClosed_closedBall.measurableSet heq
    have hflux' := fun (F : Cover → Cover) hF hFs hs hb ↦ reverseBlowupNormal_flux (F := F) hA
      (fun F hF _ hs _ ↦ (hflux F hF hs).2) hF hFs hs hb
    have hstat' : (∫ z, tangentialDivergence F z.1 z.2
        ∂(ν.map reverseBlowupNormal : Measure BlowupNormalBundle))=0 := by
      rw [reverseBlowupNormal_stationary ν hF hFs]
      exact (hflux F hF hFO).1
    exact blowup_C1graph_stationary hA.compl a hn hg hdc hphase' heq' hflux'
      hφ hsφ hφU hφO hφR hφb hF hFs hφF hstat'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalPlaneCoordinates_tangent_graph {n : Cover} (hn : ‖n‖ = 1) (q : Plane) :
    normalPlaneCoordinates n (tangentPart (graphSlopeNormal n q) n) =
      (‖n-normalPlaneEmbedding n q‖⁻¹)^2 • q := by
  have hi : ⟪graphSlopeNormal n q,n⟫ = ‖n-normalPlaneEmbedding n q‖⁻¹ := by
    have hz : ⟪normalPlaneEmbedding n q,n⟫=0 :=
      (real_inner_comm _ _).trans (normalPlaneEmbedding_inner hn q)
    rw [graphSlopeNormal,real_inner_smul_left,inner_sub_left,real_inner_self_eq_norm_sq,hn,hz]
    ring
  rw [tangentPart,hi]
  simp only [map_sub,map_smul,normalPlaneCoordinates_normal hn,graphSlopeNormal,
    normalPlaneCoordinates_embedding,zero_sub,smul_neg,neg_neg,smul_smul,pow_two]

lemma graph_vertical_variation (a : Cover) {n : Cover} (hn : ‖n‖=1)
    (g : Plane → ℝ) {ψ : Plane → ℝ} (hψ : Differentiable ℝ ψ) (y : Plane) :
    tangentialDivergence (fun x ↦ graphHeightExtension a n ψ x • n)
      (a+normalGraph n g y) (graphSlopeNormal n (gradient g y)) * ‖graphAreaVector n g y‖ =
      fderiv ℝ ψ y (gradient g y) / ‖graphAreaVector n g y‖ := by
  have hd : DifferentiableAt ℝ (graphHeightExtension a n ψ) (a+normalGraph n g y) :=
    ((hψ _).comp _ ((normalPlaneCoordinates n).differentiableAt.comp _
      (differentiableAt_id.sub_const a)))
  have hnz : ‖graphAreaVector n g y‖ ≠ 0 := by
    have hh := graphSlopeVector_norm_ge hn (gradient g y)
    exact ne_of_gt (by change 0 < ‖n-normalPlaneEmbedding n (gradient g y)‖; linarith)
  rw [tangentialDivergence_smul_const hd,graphHeightExtension_fderiv a n hψ,
    ContinuousLinearMap.comp_apply,normalPlaneCoordinates_tangent_graph hn,
    add_sub_cancel_left,normalPlaneCoordinates_graph hn,map_smul]
  change (‖graphAreaVector n g y‖⁻¹)^2 * fderiv ℝ ψ y (gradient g y) *
      ‖graphAreaVector n g y‖ = _
  field_simp

lemma radialHeightCutoff_eventually_one {p : Cover} {r : ℝ} (hr : 0<r)
    {x : Cover} (hx : x ∈ Metric.ball p r) :
    radialHeightCutoff p r =ᶠ[𝓝 x] (fun _ ↦ (1 : ℝ)) := by
  filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
  exact radialHeightCutoff_one hr (Metric.ball_subset_closedBall hz)

theorem stationary_graph_weak_equation (a : Cover) {n : Cover} (hn : ‖n‖=1)
    (g : Plane → ℝ) {p : Cover} {ρ : ℝ} (hρ : 0<ρ)
    (hstat : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall p ρ →
      (∫ y : Plane, tangentialDivergence F (a+normalGraph n g y)
        (graphSlopeNormal n (gradient g y))*‖graphAreaVector n g y‖)=0)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hsψ : ∀ y ∈ tsupport ψ, a+normalGraph n g y ∈ Metric.ball p (ρ/2)) :
    (∫ y : Plane, fderiv ℝ ψ y (gradient g y)/‖graphAreaVector n g y‖)=0 := by
  let ζ := radialHeightCutoff p (ρ/2)
  let f := graphHeightExtension a n ψ
  let F : Cover → Cover := fun x ↦ (ζ x*f x) • n
  have hζ : ContDiff ℝ (⊤ : ℕ∞) ζ := radialDensityWeight_contDiff _ _ _
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := graphHeightExtension_contDiff a n hψ
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := (hζ.mul hf).smul contDiff_const
  have hsF : tsupport F ⊆ Metric.closedBall p ρ := by
    have hsζ : tsupport ζ ⊆ Metric.closedBall p ρ := by
      have hh := radialDensityWeight_tsupport (a := p) (r := 2*(ρ/2))
        (ε := 3*(ρ/2)^2) (by positivity) (by positivity)
      convert hh using 1 <;> congr 1; ring
    apply Subset.trans _ hsζ
    apply closure_mono
    intro x hx
    by_contra hh
    exact hx (by simp [F,Function.notMem_support.mp hh])
  have he (y : Plane) : tangentialDivergence F (a+normalGraph n g y)
      (graphSlopeNormal n (gradient g y))*‖graphAreaVector n g y‖ =
      fderiv ℝ ψ y (gradient g y)/‖graphAreaVector n g y‖ := by
    let x := a+normalGraph n g y
    have hxy : normalPlaneCoordinates n (x-a)=y := by
      simp only [x,add_sub_cancel_left,normalPlaneCoordinates_graph hn]
    by_cases hy : y ∈ tsupport ψ
    · have hz : ζ =ᶠ[𝓝 x] (fun _ ↦ (1 : ℝ)) :=
        radialHeightCutoff_eventually_one (by positivity) (hsψ y hy)
      have hFe : F =ᶠ[𝓝 x] (fun z ↦ f z • n) := by
        filter_upwards [hz] with z hz
        simp only [F,hz,one_mul]
      have hde := hFe.fderiv_eq (𝕜 := ℝ)
      have hte : tangentialDivergence F x (graphSlopeNormal n (gradient g y)) =
          tangentialDivergence (fun z ↦ f z • n) x (graphSlopeNormal n (gradient g y)) := by
        simp only [tangentialDivergence,divergence,hde]
      change tangentialDivergence F x _ * _ = _
      rw [hte]
      exact graph_vertical_variation a hn g (hψ.differentiable (by simp)) y
    · have hψ0 : ψ =ᶠ[𝓝 y] (fun _ ↦ (0 : ℝ)) := notMem_tsupport_iff_eventuallyEq.mp hy
      have hf0 : f =ᶠ[𝓝 x] (fun _ ↦ (0 : ℝ)) := by
        have hp := ((normalPlaneCoordinates n).continuous.comp (continuous_id.sub (continuous_const (y := a)))).tendsto x
        change Tendsto (fun z : Cover ↦ normalPlaneCoordinates n (z-a)) (𝓝 x)
          (𝓝 (normalPlaneCoordinates n (x-a))) at hp
        rw [hxy] at hp
        exact hp.eventually hψ0
      have hF0 : F =ᶠ[𝓝 x] (fun _ ↦ (0 : Cover)) := by
        filter_upwards [hf0] with z hz
        simp only [F,hz,mul_zero,zero_smul]
      have hd0 := hF0.fderiv_eq (𝕜 := ℝ)
      have hψd0 := hψ0.fderiv_eq (𝕜 := ℝ)
      change tangentialDivergence F x _ * _ = _
      simp [tangentialDivergence,divergence,hd0,hψd0]
  simpa only [he] using hstat F hF hsF

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cover_cone_boundary_smul {A : Set Cover}
    (hcone : ∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A))
    {x : Cover} (hx : x ∈ coverEssentialBoundary A) (hxb : ‖x‖<1)
    {s : ℝ} (hs : 0<s) (hs1 : s≤1) : s • x ∈ coverEssentialBoundary A := by
  have hinv : 1 ≤ s⁻¹ := (one_le_inv₀ hs).mpr hs1
  have he : ∀ᵐ y : Cover ∂volume, y ∈ Metric.ball (0 : Cover) 1 →
      (y ∈ A ↔ y ∈ (fun z : Cover ↦ s • z) ⁻¹' A) := by
    filter_upwards [hcone s⁻¹ hinv] with y hy hb
    simpa only [inv_inv,mem_preimage] using (hy hb).symm
  have hpre := cover_boundary_local_ae
    (Metric.isOpen_ball.mem_nhds (show x ∈ Metric.ball (0 : Cover) 1 by simpa using hxb)) he hx
  exact cover_boundary_preimage_image (Measure.quasiMeasurePreserving_smul volume hs.ne')
    (show ContinuousAt (fun z : Cover ↦ s • z) x from (Continuous.const_smul continuous_id s).continuousAt) hpre

theorem cone_graph_radial_derivative {A : Set Cover}
    (hcone : ∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A))
    {x a n : Cover} (hn : ‖n‖=1) (hx : x ∈ coverEssentialBoundary A) (hxb : ‖x‖<1)
    {g : Plane → ℝ}
    (hg : DifferentiableAt ℝ g (normalPlaneCoordinates n (x-a)))
    (hgraph : ∀ᶠ z in 𝓝 x, z ∈ coverEssentialBoundary A →
      normalGraph n g (normalPlaneCoordinates n (z-a))=z-a) :
    fderiv ℝ g (normalPlaneCoordinates n (x-a)) (normalPlaneCoordinates n x)=⟪n,x⟫ := by
  have htx : Tendsto (fun t : ℝ ↦ t • x) (𝓝 (1 : ℝ)) (𝓝 x) := by
    have hh : Continuous (fun t : ℝ ↦ t • x) := continuous_id.smul continuous_const
    simpa only [one_smul] using hh.tendsto (1 : ℝ)
  have he : (fun t : ℝ ↦ g (normalPlaneCoordinates n (t • x-a))) =ᶠ[𝓝[≤] (1 : ℝ)]
      (fun t ↦ ⟪n,t • x-a⟫) := by
    filter_upwards [htx.eventually hgraph |> mem_nhdsWithin_of_mem_nhds,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ)<1)), self_mem_nhdsWithin] with t ht ht0 ht1
    have hb := ht (cover_cone_boundary_smul hcone hx hxb ht0 ht1)
    have hh := congrArg (fun v : Cover ↦ ⟪n,v⟫) hb
    simpa only [normalGraph_inner hn] using hh
  have hlin : HasDerivAt (fun t : ℝ ↦ t • x-a) x 1 := by
    simpa using (((hasDerivAt_id (1 : ℝ)).smul_const x).sub_const a)
  have hdlin : HasDerivAt (fun t : ℝ ↦ normalPlaneCoordinates n (t • x-a))
      (normalPlaneCoordinates n x) 1 :=
    (normalPlaneCoordinates n).hasFDerivAt.comp_hasDerivAt 1 hlin
  have hg' : DifferentiableAt ℝ g (normalPlaneCoordinates n ((1 : ℝ) • x-a)) := by
    simpa only [one_smul] using hg
  have hdg' : HasDerivAt (fun t : ℝ ↦ g (normalPlaneCoordinates n (t • x-a)))
      (fderiv ℝ g (normalPlaneCoordinates n (x-a)) (normalPlaneCoordinates n x)) 1 := by
    simpa only [Function.comp_def,one_smul] using hg'.hasFDerivAt.comp_hasDerivAt 1 hdlin
  have hdi : HasDerivAt (fun t : ℝ ↦ ⟪n,t • x-a⟫) ⟪n,x⟫ 1 :=
    (innerSL ℝ n).hasFDerivAt.comp_hasDerivAt 1 hlin
  have hval : g (normalPlaneCoordinates n ((1 : ℝ) • x-a)) = ⟪n,(1 : ℝ) • x-a⟫ :=
    he.self_of_nhdsWithin (by simp : (1 : ℝ) ∈ Iic (1 : ℝ))
  exact (hdg'.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic 1)).symm.trans
    ((hdi.hasDerivWithinAt.congr_of_eventuallyEq he hval).derivWithin
      (uniqueDiffWithinAt_Iic 1))

lemma cone_graph_radial_projection_ne_zero {x n : Cover} (hn : ‖n‖=1)
    (hx : x≠0) {L : Plane →L[ℝ] ℝ} (he : L (normalPlaneCoordinates n x)=⟪n,x⟫) :
    normalPlaneCoordinates n x ≠ 0 := by
  intro hz
  have hi : ⟪n,x⟫=0 := by rw [hz,map_zero] at he; exact he.symm
  have hh := normalPlaneCoordinates_reconstruct hn x
  rw [hz,hi] at hh
  have h0 : normalPlaneEmbedding n 0=0 := by
    apply norm_eq_zero.mp
    simpa using normalPlaneEmbedding_norm n (0 : Plane)
  exact hx (by simpa only [h0,zero_smul,add_zero] using hh.symm)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma slopeScalarTest_derivative {χ ψ : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hχ0 : 0 ∉ tsupport χ) {r s : ℝ} (hr : r≠0) (v : Plane) :
    fderiv ℝ (slopeScalarTest χ ψ) (planarWedgeChart (r,s)) v =
      deriv χ r*ψ s*(planeProductCoordinates v).1 +
        χ r*deriv ψ s*((planeProductCoordinates v).2-s*(planeProductCoordinates v).1)/r := by
  let x := planarWedgeChart (r,s)
  have hf := slopeScalarTest_contDiff hχ hψ hχ0
  have hl : HasDerivAt (fun t : ℝ ↦ x+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hd : HasDerivAt (fun t : ℝ ↦ slopeScalarTest χ ψ (x+t • v))
      (fderiv ℝ (slopeScalarTest χ ψ) x v) 0 := by
    simpa only [zero_smul,add_zero,Function.comp_def] using
      ((hf.differentiable (by simp)) (x+(0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt 0 hl
  have he (t : ℝ) : slopeScalarTest χ ψ (x+t • v)=
      χ (r+t*(planeProductCoordinates v).1)*
        ψ ((r*s+t*(planeProductCoordinates v).2)/(r+t*(planeProductCoordinates v).1)) := by
    simp [slopeScalarTest,x,planarWedgeChart]
  simp_rw [he] at hd
  have hd₁ : HasDerivAt (fun t : ℝ ↦ r+t*(planeProductCoordinates v).1)
      (planeProductCoordinates v).1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (planeProductCoordinates v).1).const_add r
  have hd₂ : HasDerivAt (fun t : ℝ ↦ r*s+t*(planeProductCoordinates v).2)
      (planeProductCoordinates v).2 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (planeProductCoordinates v).2).const_add (r*s)
  have hden : r+(0 : ℝ)*(planeProductCoordinates v).1≠0 := by simpa using hr
  have hquot := hd₂.div hd₁ hden
  have hc := (((hχ.differentiable (by simp)) _).hasDerivAt.comp 0 hd₁)
  have hp := (((hψ.differentiable (by simp)) _).hasDerivAt.comp 0 hquot)
  have hh := hd.unique (hc.mul hp)
  simp only [Function.comp_apply,Pi.div_apply,zero_mul,add_zero,mul_div_cancel_left₀ _ hr] at hh
  change _ = _ at hh
  rw [hh]
  field_simp

lemma integral_mul_deriv_radial {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hsχ : HasCompactSupport χ) :
    (∫ r : ℝ, r*deriv χ r)=-(∫ r : ℝ, χ r) := by
  have hχd : Continuous (deriv χ) := hχ.continuous_deriv (by simp)
  have hi : Integrable (fun r : ℝ ↦ r*deriv χ r) :=
    (continuous_id.mul hχd).integrable_of_hasCompactSupport hsχ.deriv.mul_left
  have hj : Integrable (fun r : ℝ ↦ (1 : ℝ)*χ r) := by
    simpa only [one_mul] using hχ.continuous.integrable_of_hasCompactSupport hsχ
  have hk : Integrable (fun r : ℝ ↦ r*χ r) :=
    (continuous_id.mul hχ.continuous).integrable_of_hasCompactSupport hsχ.mul_left
  simpa only [one_mul,id_eq] using integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun r _ ↦ hasDerivAt_id r) (fun r _ ↦ ((hχ.differentiable (by simp)) r).hasDerivAt) hi hj hk

theorem integral_slope_separated {G : Plane → ℝ} (hG : Integrable G)
    {χ A B : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hsχ : HasCompactSupport χ) (hχpos : tsupport χ ⊆ Ioi (0 : ℝ))
    (hA : Integrable A) (hB : Integrable B)
    (hzero : ∀ r : ℝ, r≤0 → ∀ y : ℝ, G (planeProductCoordinates.symm (r,y))=0)
    (he : ∀ r : ℝ, 0<r → ∀ s : ℝ, G (planarWedgeChart (r,s))=
      deriv χ r*A s+(χ r/r)*B s) :
    (∫ y : Plane, G y)=(∫ r : ℝ, χ r)*((∫ s : ℝ, B s)-(∫ s : ℝ, A s)) := by
  have hL := planeProductCoordinates_measurePreserving.symm
    planeProductCoordinates.toHomeomorph.toMeasurableEquiv
  have hLi := (hL.integrable_comp hG.aestronglyMeasurable).mpr hG
  have hi : (fun r : ℝ ↦ ∫ y : ℝ, G (planeProductCoordinates.symm (r,y))) =
      (fun r : ℝ ↦ (r*deriv χ r)*(∫ s : ℝ, A s)+χ r*(∫ s : ℝ, B s)) := by
    funext r
    by_cases hr : 0<r
    · have hscale : (∫ y : ℝ, G (planeProductCoordinates.symm (r,y))) =
          r*(∫ s : ℝ, G (planarWedgeChart (r,s))) := by
        change _ = r*(∫ s : ℝ, G (planeProductCoordinates.symm (r,r*s)))
        rw [Measure.integral_comp_mul_left (fun y : ℝ ↦ G (planeProductCoordinates.symm (r,y))) r,
          abs_of_pos (inv_pos.mpr hr),smul_eq_mul,mul_inv_cancel_left₀ hr.ne']
      rw [hscale]
      simp_rw [he r hr]
      rw [integral_add (hA.const_mul _) (hB.const_mul _),integral_const_mul,integral_const_mul]
      field_simp
    · have hz : r ∉ tsupport χ := fun hh ↦ hr (hχpos hh)
      simp only [hzero r (le_of_not_gt hr),integral_zero,
        image_eq_zero_of_notMem_tsupport hz,deriv_of_notMem_tsupport hz,mul_zero,zero_mul,add_zero]
  have hχi : Integrable χ (volume : Measure ℝ) := hχ.continuous.integrable_of_hasCompactSupport hsχ
  have hχdi : Integrable (fun r : ℝ ↦ r*deriv χ r) :=
    (continuous_id.mul (hχ.continuous_deriv (by simp))).integrable_of_hasCompactSupport hsχ.deriv.mul_left
  rw [← hL.integral_comp planeProductCoordinates.symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding G]
  change (∫ z : ℝ × ℝ, G (planeProductCoordinates.symm z)) = _
  change Integrable (fun z : ℝ × ℝ ↦ G (planeProductCoordinates.symm z)) (volume.prod volume) at hLi
  rw [Measure.volume_eq_prod,integral_prod _ hLi,hi,
    integral_add (hχdi.mul_const _) (hχi.mul_const _),integral_mul_const,integral_mul_const,
    integral_mul_deriv_radial hχ hsχ]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Convolution
namespace CubicTorus

lemma continuous_mul_shift_integrable {u b : ℝ → ℝ} (hu : Continuous u)
    (hb : Continuous b) (hs : HasCompactSupport b) (x : ℝ) :
    Integrable (fun t ↦ u t*b (t-x)) := by
  have hb' : HasCompactSupport (fun t ↦ b (t-x)) := by
    have hh := hs.comp_homeomorph (Homeomorph.addRight (-x))
    change HasCompactSupport (fun t : ℝ ↦ b (t+ -x)) at hh
    simpa only [sub_eq_add_neg] using hh
  exact (hu.mul (hb.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport hb'.mul_left

lemma continuous_angular_smoothing_tendsto {u : ℝ → ℝ} (hu : Continuous u) (x : ℝ) :
    Tendsto (fun i ↦ ∫ t : ℝ, u t*(angularMollifier i).normed volume (t-x)) atTop (𝓝 (u x)) := by
  have ht := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) angularMollifier_radius_tendsto hu x
  convert ht using 1
  funext i
  rw [convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply,smul_eq_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  change u t*(angularMollifier i).normed volume (t-x) =
    (angularMollifier i).normed volume (x-t)*u t
  rw [show x-t = -(t-x) by ring,(angularMollifier i).normed_neg]
  ring

theorem continuous_constant_of_weak_derivative_zero {u : ℝ → ℝ} (hu : Continuous u)
    {a b x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b)
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → tsupport ψ ⊆ Ioo a b →
      (∫ t : ℝ, u t*deriv ψ t)=0) : u x=u y := by
  wlog hxy : x ≤ y generalizing x y
  · exact (this hy hx (le_of_not_ge hxy)).symm
  have hrad : ∀ᶠ i : ℕ in atTop, (angularMollifier i).rOut < min (x-a) (b-y) :=
    angularMollifier_radius_tendsto.eventually (gt_mem_nhds (by exact lt_min (by linarith [hx.1]) (by linarith [hy.2])))
  have he : (fun i ↦ ∫ t : ℝ, u t*(angularMollifier i).normed volume (t-x)) =ᶠ[atTop]
      (fun i ↦ ∫ t : ℝ, u t*(angularMollifier i).normed volume (t-y)) := by
    filter_upwards [hrad] with i hi
    let k := (angularMollifier i).normed volume
    have hk : ContDiff ℝ (⊤ : ℕ∞) k := (angularMollifier i).contDiff_normed
    have hks : tsupport k ⊆ Icc (-(angularMollifier i).rOut) (angularMollifier i).rOut := by
      rw [(angularMollifier i).tsupport_normed_eq,Real.closedBall_eq_Icc]
      simp only [zero_sub,zero_add,subset_refl]
    have hs : tsupport (intervalSmoothHat k x y) ⊆ Ioo a b := by
      apply (intervalSmoothHat_support hk.continuous hks hxy).trans
      intro t ht
      constructor <;> linarith [lt_of_lt_of_le hi (min_le_left _ _),lt_of_lt_of_le hi (min_le_right _ _),ht.1,ht.2]
    have hh := hweak (intervalSmoothHat k x y) (intervalSmoothHat_contDiff hk x y) hs
    simp_rw [(intervalSmoothHat_hasDerivAt hk.continuous x y _).deriv,mul_sub] at hh
    rw [integral_sub (continuous_mul_shift_integrable hu hk.continuous
      (angularMollifier i).hasCompactSupport_normed x)
      (continuous_mul_shift_integrable hu hk.continuous (angularMollifier i).hasCompactSupport_normed y)] at hh
    exact sub_eq_zero.mp hh
  exact tendsto_nhds_unique (continuous_angular_smoothing_tendsto hu x)
    ((continuous_angular_smoothing_tendsto hu y).congr' he.symm)

theorem hasDerivAt_of_continuous_weak_derivative {u v : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) {a b : ℝ}
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → tsupport ψ ⊆ Ioo a b →
      (∫ t : ℝ, u t*deriv ψ t) = -(∫ t : ℝ, v t*ψ t))
    {x : ℝ} (hx : x ∈ Ioo a b) : HasDerivAt u (v x) x := by
  let V : ℝ → ℝ := fun t ↦ ∫ s in (0 : ℝ)..t, v s
  have hd (t : ℝ) : HasDerivAt V (v t) t := intervalIntegral.integral_hasDerivAt_right
    (hv.intervalIntegrable 0 t) (hv.stronglyMeasurableAtFilter volume _) hv.continuousAt
  have hV : Continuous V := (fun t ↦ (hd t).continuousAt) |> continuous_iff_continuousAt.mpr
  have hz : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → tsupport ψ ⊆ Ioo a b →
      (∫ t : ℝ, (u t-V t)*deriv ψ t)=0 := by
    intro ψ hψ hsψ
    have hs : HasCompactSupport ψ := isCompact_Icc.of_isClosed_subset isClosed_closure
      (hsψ.trans Ioo_subset_Icc_self)
    have hψd : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
    have hui : Integrable (fun t ↦ u t*deriv ψ t) :=
      (hu.mul hψd).integrable_of_hasCompactSupport hs.deriv.mul_left
    have hVi : Integrable (fun t ↦ V t*deriv ψ t) :=
      (hV.mul hψd).integrable_of_hasCompactSupport hs.deriv.mul_left
    have hvi : Integrable (fun t ↦ v t*ψ t) :=
      (hv.mul hψ.continuous).integrable_of_hasCompactSupport hs.mul_left
    have hprod : Integrable (fun t ↦ V t*ψ t) :=
      (hV.mul hψ.continuous).integrable_of_hasCompactSupport hs.mul_left
    have hparts := integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun t _ ↦ hd t) (fun t _ ↦ ((hψ.differentiable (by simp)) t).hasDerivAt) hVi hvi hprod
    simp_rw [sub_mul]
    rw [integral_sub hui hVi,hweak ψ hψ hsψ,hparts,sub_self]
  have he : u =ᶠ[𝓝 x] (fun t ↦ V t+(u x-V x)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    have hh := continuous_constant_of_weak_derivative_zero (hu.sub hV) ht hx hz
    dsimp only [Pi.sub_apply] at hh
    linarith
  exact ((hd x).add_const (u x-V x)).congr_of_eventuallyEq he

theorem hasDerivAt_of_continuousOn_weak_derivative {u v : ℝ → ℝ}
    {a b : ℝ} (hu : ContinuousOn u (Ioo a b)) (hv : ContinuousOn v (Ioo a b))
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → tsupport ψ ⊆ Ioo a b →
      (∫ t : ℝ, u t*deriv ψ t) = -(∫ t : ℝ, v t*ψ t))
    {x : ℝ} (hx : x ∈ Ioo a b) : HasDerivAt u (v x) x := by
  let c := (a+x)/2
  let d := (x+b)/2
  have hcx : c<x := by dsimp only [c]; linarith [hx.1]
  have hxd : x<d := by dsimp only [d]; linarith [hx.2]
  have hsub : Icc c d ⊆ Ioo a b := by
    intro t ht
    constructor <;> dsimp only [c,d] at ht <;> linarith [ht.1,ht.2,hx.1,hx.2]
  let U : C(Icc c d,ℝ) := ⟨fun t ↦ u t,continuousOn_iff_continuous_domRestrict.mp (hu.mono hsub)⟩
  let W : C(Icc c d,ℝ) := ⟨fun t ↦ v t,continuousOn_iff_continuous_domRestrict.mp (hv.mono hsub)⟩
  obtain ⟨U',hU'⟩ := U.exists_extension' isClosed_Icc.isClosedEmbedding_subtypeVal
  obtain ⟨W',hW'⟩ := W.exists_extension' isClosed_Icc.isClosedEmbedding_subtypeVal
  have heU (t : ℝ) (ht : t ∈ Icc c d) : U' t=u t := congrFun hU' ⟨t,ht⟩
  have heW (t : ℝ) (ht : t ∈ Icc c d) : W' t=v t := congrFun hW' ⟨t,ht⟩
  have hw : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → tsupport ψ ⊆ Ioo c d →
      (∫ t : ℝ, U' t*deriv ψ t) = -(∫ t : ℝ, W' t*ψ t) := by
    intro ψ hψ hsψ
    have he₁ : (fun t ↦ U' t*deriv ψ t) = (fun t ↦ u t*deriv ψ t) := by
      funext t
      by_cases ht : t ∈ tsupport ψ
      · rw [heU t (Ioo_subset_Icc_self (hsψ ht))]
      · rw [deriv_of_notMem_tsupport ht,mul_zero,mul_zero]
    have he₂ : (fun t ↦ W' t*ψ t) = (fun t ↦ v t*ψ t) := by
      funext t
      by_cases ht : t ∈ tsupport ψ
      · rw [heW t (Ioo_subset_Icc_self (hsψ ht))]
      · rw [image_eq_zero_of_notMem_tsupport ht,mul_zero,mul_zero]
    rw [he₁,he₂]
    exact hweak ψ hψ (hsψ.trans (Ioo_subset_Icc_self.trans hsub))
  have hd := hasDerivAt_of_continuous_weak_derivative U'.continuous W'.continuous hw ⟨hcx,hxd⟩
  rw [heW x ⟨hcx.le,hxd.le⟩] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds (show x ∈ Ioo c d from ⟨hcx,hxd⟩)] with t ht
  exact (heU t (Ioo_subset_Icc_self ht)).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicTorus

theorem cone_slope_ODE_derivative {f q c h : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ s ∈ Ioo a b, HasDerivAt f (q s) s)
    (hc : ContinuousOn c (Ioo a b))
    (hpos : ∀ s ∈ Ioo a b, 0<c s)
    (hmetric : ∀ s ∈ Ioo a b, (c s)^2*(1+(f s-s*q s)^2+(q s)^2)=1)
    (hflux : ∀ s ∈ Ioo a b, h s=(q s-s*(f s-s*q s))*c s)
    (hh : ∀ s ∈ Ioo a b, HasDerivAt h (-(f s-s*q s)*c s) s)
    {x : ℝ} (hx : x ∈ Ioo a b) : HasDerivAt q 0 x ∧ HasDerivAt c 0 x := by
  have hcx := hpos x hx
  have hden (s : ℝ) : 0<1+s^2+(f s)^2 := by positivity
  have hid (s : ℝ) (hs : s ∈ Ioo a b) :
      1+s^2-(h s)^2=(c s)^2*(1+s^2+(f s)^2) := by
    rw [hflux s hs]
    linear_combination -(1+s^2)*(hmetric s hs)
  have hhnum : 2*x+2*(h x)*(f x-x*q x)*c x = (c x)^2*(2*x+2*f x*q x) := by
    rw [hflux x hx]
    linear_combination -(2*x)*(hmetric x hx)
  have hdnum : HasDerivAt (fun s ↦ 1+s^2-(h s)^2)
      (2*x+2*(h x)*(f x-x*q x)*c x) x := by
    convert (((hasDerivAt_id x).pow 2).const_add 1).sub ((hh x hx).pow 2) using 1 <;> first | rfl | (simp only [id_eq]; ring)
  have hdden : HasDerivAt (fun s ↦ 1+s^2+(f s)^2) (2*x+2*f x*q x) x := by
    convert (((hasDerivAt_id x).pow 2).const_add 1).add ((hf x hx).pow 2) using 1 <;> first | rfl | (simp only [id_eq]; ring)
  have hdsq : HasDerivAt (fun s ↦ (c s)^2) 0 x := by
    have hd := hdnum.div hdden (hden x).ne'
    rw [hhnum,hid x hx] at hd
    have he : (fun s ↦ (c s)^2) =ᶠ[𝓝 x]
        (fun s ↦ (1+s^2-(h s)^2)/(1+s^2+(f s)^2)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with s hs
      rw [hid s hs,mul_div_cancel_right₀ _ (hden s).ne']
    convert hd.congr_of_eventuallyEq he using 1
    all_goals first | rfl | (field_simp; ring)
  have hdc : HasDerivAt c 0 x := by
    have hd := hdsq.sqrt (by positivity : (c x)^2 ≠ 0)
    have he : c =ᶠ[𝓝 x] (fun s ↦ Real.sqrt ((c s)^2)) := by
      filter_upwards [(hc.continuousAt (isOpen_Ioo.mem_nhds hx)).eventually
        (Ioi_mem_nhds hcx)] with s hs
      rw [Real.sqrt_sq hs.le]
    simpa only [zero_div] using hd.congr_of_eventuallyEq he
  have hqeq (s : ℝ) (hs : s ∈ Ioo a b) :
      q s=(h s+s*f s*c s)/((1+s^2)*c s) := by
    rw [hflux s hs]
    field_simp [(hpos s hs).ne']
    ring
  have hn : HasDerivAt (fun s ↦ h s+s*f s*c s)
      (2*x*q x*c x) x := by
    convert (hh x hx).add ((((hasDerivAt_id x).mul (hf x hx)).mul hdc)) using 1 <;> first | rfl | (simp only [id_eq]; ring)
  have hd : HasDerivAt (fun s ↦ (1+s^2)*c s) (2*x*c x) x := by
    convert ((((hasDerivAt_id x).pow 2).const_add 1).mul hdc) using 1 <;> first | rfl | (simp only [id_eq]; ring)
  have hneq : (1+x^2)*c x≠0 := by positivity
  have hder := hn.div hd hneq
  have he : q =ᶠ[𝓝 x] (fun s ↦ (h s+s*f s*c s)/((1+s^2)*c s)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with s hs
    exact hqeq s hs
  refine ⟨?_,hdc⟩
  convert hder.congr_of_eventuallyEq he using 1
  all_goals first | rfl | (rw [hflux x hx]; field_simp; ring)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicTorus

def coneSlopeReciprocalArea (f q : ℝ → ℝ) (s : ℝ) : ℝ :=
  (Real.sqrt (1+(f s-s*q s)^2+(q s)^2))⁻¹

def coneSlopeFlux (f q : ℝ → ℝ) (s : ℝ) : ℝ :=
  (q s-s*(f s-s*q s))*coneSlopeReciprocalArea f q s

lemma coneSlopeReciprocalArea_pos (f q : ℝ → ℝ) (s : ℝ) :
    0<coneSlopeReciprocalArea f q s := by
  exact inv_pos.mpr (Real.sqrt_pos.2 (by positivity))

lemma coneSlopeReciprocalArea_metric (f q : ℝ → ℝ) (s : ℝ) :
    (coneSlopeReciprocalArea f q s)^2*(1+(f s-s*q s)^2+(q s)^2)=1 := by
  have hp : 0<1+(f s-s*q s)^2+(q s)^2 := by positivity
  dsimp only [coneSlopeReciprocalArea]
  rw [inv_pow,Real.sq_sqrt hp.le,inv_mul_cancel₀ hp.ne']

lemma coneSlopeReciprocalArea_continuousOn {f q : ℝ → ℝ} {U : Set ℝ}
    (hf : ContinuousOn f U) (hq : ContinuousOn q U) :
    ContinuousOn (coneSlopeReciprocalArea f q) U := by
  apply ((((hf.sub (continuousOn_id.mul hq)).pow 2).const_add 1).add (hq.pow 2)).sqrt.inv₀
  intro s hs
  exact (Real.sqrt_pos.2 (by positivity : 0<1+(f s-s*q s)^2+(q s)^2)).ne'

theorem weak_cone_slope_derivative {f q : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ s ∈ Ioo a b, HasDerivAt f (q s) s)
    (hq : ContinuousOn q (Ioo a b))
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → tsupport ψ ⊆ Ioo a b →
      (∫ s : ℝ, coneSlopeFlux f q s*deriv ψ s) =
        (∫ s : ℝ, (f s-s*q s)*coneSlopeReciprocalArea f q s*ψ s))
    {x : ℝ} (hx : x ∈ Ioo a b) : HasDerivAt q 0 x := by
  have hfc : ContinuousOn f (Ioo a b) := fun s hs ↦ (hf s hs).continuousAt.continuousWithinAt
  have hc := coneSlopeReciprocalArea_continuousOn hfc hq
  have hu := hfc.sub (continuousOn_id.mul hq)
  have hh : ContinuousOn (coneSlopeFlux f q) (Ioo a b) :=
    (hq.sub (continuousOn_id.mul hu)).mul hc
  have hhder (s : ℝ) (hs : s ∈ Ioo a b) :
      HasDerivAt (coneSlopeFlux f q) (-(f s-s*q s)*coneSlopeReciprocalArea f q s) s := by
    apply hasDerivAt_of_continuousOn_weak_derivative hh (hu.neg.mul hc) _ hs
    intro ψ hψ hsψ
    rw [hweak ψ hψ hsψ]
    simp only [Pi.mul_apply,Pi.sub_apply,Pi.neg_apply,id_eq,neg_mul,integral_neg,neg_neg]
  exact (cone_slope_ODE_derivative hf hc
    (fun s _ ↦ coneSlopeReciprocalArea_pos f q s)
    (fun s _ ↦ coneSlopeReciprocalArea_metric f q s)
    (fun s _ ↦ rfl) hhder hx).1

theorem weak_cone_slope_affine {f q : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ s ∈ Ioo a b, HasDerivAt f (q s) s)
    (hq : ContinuousOn q (Ioo a b))
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → tsupport ψ ⊆ Ioo a b →
      (∫ s : ℝ, coneSlopeFlux f q s*deriv ψ s) =
        (∫ s : ℝ, (f s-s*q s)*coneSlopeReciprocalArea f q s*ψ s))
    {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) :
    q y=q x ∧ f y=f x+q x*(y-x) := by
  have hqd (s : ℝ) (hs : s ∈ Ioo a b) := weak_cone_slope_derivative hf hq hweak hs
  have hqc (s : ℝ) (hs : s ∈ Ioo a b) : q s=q x :=
    isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
      (fun s hs ↦ (hqd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs ↦ (hqd s hs).deriv) hs hx
  have hfd (s : ℝ) (hs : s ∈ Ioo a b) : HasDerivAt (fun t ↦ f t-q x*t) 0 s := by
    have hd := (hf s hs).sub ((hasDerivAt_id s).const_mul (q x))
    convert hd using 1 <;> first | rfl | simp only [hqc s hs,mul_one,sub_self]
  have he := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun s hs ↦ (hfd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs ↦ (hfd s hs).deriv) hy hx
  exact ⟨hqc y hy,by change f y-q x*y=f x-q x*x at he; linarith⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def slopeHorizontalVector : Plane := planeProductCoordinates.symm (1,0)

lemma plane_inner_coordinates (u v : Plane) :
    ⟪u,v⟫ = (planeProductCoordinates u).1*(planeProductCoordinates v).1+
      (planeProductCoordinates u).2*(planeProductCoordinates v).2 := by
  simp [planeProductCoordinates_apply,EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct,Fin.sum_univ_two,mul_comm]

lemma plane_gradient_coordinates (g : Plane → ℝ) (y : Plane) :
    (planeProductCoordinates (gradient g y)).1 = fderiv ℝ g y slopeHorizontalVector ∧
    (planeProductCoordinates (gradient g y)).2 = fderiv ℝ g y slopeVerticalVector := by
  constructor <;> rw [← inner_gradient_left,plane_inner_coordinates]
  · simp [slopeHorizontalVector]
  · simp [slopeVerticalVector]

lemma planarWedgeChart_hasDerivAt_radial (r s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ planarWedgeChart (t,s))
      (planeProductCoordinates.symm (1,s)) r := by
  have hd := (hasDerivAt_id r).prodMk ((hasDerivAt_id r).mul_const s)
  convert planeProductCoordinates.symm.hasFDerivAt.comp_hasDerivAt r hd using 1 <;>
    first | rfl | simp only [one_mul,ContinuousLinearEquiv.coe_coe]

lemma planarWedgeChart_hasDerivAt_angular (r s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ planarWedgeChart (r,t)) (r • slopeVerticalVector) s := by
  have hd := (hasDerivAt_const s r).prodMk ((hasDerivAt_id s).const_mul r)
  have hh := planeProductCoordinates.symm.hasFDerivAt.comp_hasDerivAt s hd
  simpa [Function.comp_def,planarWedgeChart,slopeVerticalVector,← map_smul] using hh

theorem euler_graph_homogeneous {g : Plane → ℝ} {a b c d : ℝ} (ha : 0<a)
    (hg : ∀ r ∈ Ioo a b, ∀ s ∈ Ioo c d, DifferentiableAt ℝ g (planarWedgeChart (r,s)))
    (he : ∀ r ∈ Ioo a b, ∀ s ∈ Ioo c d,
      fderiv ℝ g (planarWedgeChart (r,s)) (planarWedgeChart (r,s))=g (planarWedgeChart (r,s)))
    {r t s : ℝ} (hr : r ∈ Ioo a b) (ht : t ∈ Ioo a b) (hs : s ∈ Ioo c d) :
    g (planarWedgeChart (r,s))/r=g (planarWedgeChart (t,s))/t := by
  have hd (v : ℝ) (hv : v ∈ Ioo a b) :
      HasDerivAt (fun w : ℝ ↦ g (planarWedgeChart (w,s))/w) 0 v := by
    have hv0 : 0<v := ha.trans hv.1
    have h := (hg v hv s hs).hasFDerivAt.comp_hasDerivAt v (planarWedgeChart_hasDerivAt_radial v s)
    have hh := h.div (hasDerivAt_id v) hv0.ne'
    have hmult : fderiv ℝ g (planarWedgeChart (v,s)) (planeProductCoordinates.symm (1,s))*v=
        g (planarWedgeChart (v,s)) := by
      calc
        _ = fderiv ℝ g (planarWedgeChart (v,s)) (v • planeProductCoordinates.symm (1,s)) := by
          rw [map_smul,smul_eq_mul,mul_comm]
        _ = _ := by
          rw [← map_smul]
          simpa [planarWedgeChart] using he v hv s hs
    convert hh using 1 <;> first | rfl | simp only [id_eq,Function.comp_def,hmult,mul_one,sub_self,zero_div]
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun v hv ↦ (hd v hv).differentiableAt.differentiableWithinAt)
    (fun v hv ↦ (hd v hv).deriv) hr ht

lemma graph_angular_slice_hasDerivAt {g : Plane → ℝ} {r s : ℝ} (hr : r≠0)
    (hg : DifferentiableAt ℝ g (planarWedgeChart (r,s))) :
    HasDerivAt (fun t : ℝ ↦ g (planarWedgeChart (r,t))/r)
      (fderiv ℝ g (planarWedgeChart (r,s)) slopeVerticalVector) s := by
  have hd := (hg.hasFDerivAt.comp_hasDerivAt s
    (planarWedgeChart_hasDerivAt_angular r s)).div_const r
  simpa only [Function.comp_def,map_smul,smul_eq_mul,mul_div_cancel_left₀ _ hr] using hd

lemma planarWedgeChart_expand (r s : ℝ) :
    planarWedgeChart (r,s)=r • slopeHorizontalVector+(r*s) • slopeVerticalVector := by
  apply planeProductCoordinates.injective
  simp [planarWedgeChart,slopeHorizontalVector,slopeVerticalVector]

theorem euler_graph_gradient {g : Plane → ℝ} {a b c d : ℝ} (ha : 0<a)
    (hg : ∀ r ∈ Ioo a b, ∀ s ∈ Ioo c d, DifferentiableAt ℝ g (planarWedgeChart (r,s)))
    (he : ∀ r ∈ Ioo a b, ∀ s ∈ Ioo c d,
      fderiv ℝ g (planarWedgeChart (r,s)) (planarWedgeChart (r,s))=g (planarWedgeChart (r,s)))
    {r r₀ s : ℝ} (hr : r ∈ Ioo a b) (hr₀ : r₀ ∈ Ioo a b) (hs : s ∈ Ioo c d) :
    let f := g (planarWedgeChart (r₀,s))/r₀
    let q := fderiv ℝ g (planarWedgeChart (r₀,s)) slopeVerticalVector
    planeProductCoordinates (gradient g (planarWedgeChart (r,s)))=(f-s*q,q) := by
  dsimp only
  have hr0 : r≠0 := (ha.trans hr.1).ne'
  have hr₀0 : r₀≠0 := (ha.trans hr₀.1).ne'
  have hvs : fderiv ℝ g (planarWedgeChart (r,s)) slopeVerticalVector =
      fderiv ℝ g (planarWedgeChart (r₀,s)) slopeVerticalVector := by
    have hfun : (fun t : ℝ ↦ g (planarWedgeChart (r,t))/r) =ᶠ[𝓝 s]
        (fun t : ℝ ↦ g (planarWedgeChart (r₀,t))/r₀) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
      exact euler_graph_homogeneous ha hg he hr hr₀ ht
    exact (graph_angular_slice_hasDerivAt hr0 (hg r hr s hs)).unique
      ((graph_angular_slice_hasDerivAt hr₀0 (hg r₀ hr₀ s hs)).congr_of_eventuallyEq hfun)
  have hre := he r hr s hs
  have hlin : fderiv ℝ g (planarWedgeChart (r,s)) (planarWedgeChart (r,s)) =
      r*fderiv ℝ g (planarWedgeChart (r,s)) slopeHorizontalVector+
        (r*s)*fderiv ℝ g (planarWedgeChart (r,s)) slopeVerticalVector := by
    calc
      _ = fderiv ℝ g (planarWedgeChart (r,s))
          (r • slopeHorizontalVector+(r*s) • slopeVerticalVector) :=
        congrArg (fderiv ℝ g (planarWedgeChart (r,s))) (planarWedgeChart_expand r s)
      _ = _ := by simp only [map_add,map_smul,smul_eq_mul]
  rw [hlin,hvs] at hre
  have hhom := euler_graph_homogeneous ha hg he hr hr₀ hs
  have hhom' : g (planarWedgeChart (r,s)) =
      (g (planarWedgeChart (r₀,s))/r₀)*r := (div_eq_iff hr0).mp hhom
  have hh : fderiv ℝ g (planarWedgeChart (r,s)) slopeHorizontalVector=
      g (planarWedgeChart (r₀,s))/r₀-s*fderiv ℝ g (planarWedgeChart (r₀,s)) slopeVerticalVector := by
    apply (mul_right_inj' hr0).mp
    nlinarith [hre,hhom']
  have hcoord := plane_gradient_coordinates g (planarWedgeChart (r,s))
  exact Prod.ext (hcoord.1.trans hh) (hcoord.2.trans hvs)

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
