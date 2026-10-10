import Mathlib
import OAI.Geometry.CubicTorus.Curvature.LinearCMCEquationNear

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_centered_C1_modulus {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E)) :
    ∃ (n : Cover) (g : Plane → ℝ) (r M ρ : ℝ), ‖n‖=1 ∧ 0<r ∧
      0≤M ∧ 0<ρ ∧ ρ≤1/16 ∧
      LipschitzWith (1/4) g ∧ g 0=0 ∧ ContDiffOn ℝ 1 g (Metric.ball 0 r) ∧
      (∀ y ∈ Metric.ball (0 : Plane) r,
        quotientMap (cubeCenter+normalGraph n g y)∈frontier (openRepresentative E)) ∧
      (∀ x∈Metric.ball (0 : Cover) r,
        quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
          normalGraph n g (normalPlaneCoordinates n x)=x) ∧
      (∀ i : ℕ, ∀ x∈Metric.ball (0 : Plane) r, ∀ y∈Metric.ball (0 : Plane) r,
        dist x y≤ρ^i*r → dist (fderiv ℝ g x) (fderiv ℝ g y)≤M*(1/2:ℝ)^i) := by
  classical
  obtain ⟨μ,hμ⟩ := exists_normalMeasure hE hmin.1.2.ne
  obtain ⟨H,hH⟩ := isMinimizerAt_centered_multiplier hV hE hmin hcenter hμ
  obtain ⟨R,ρ,hR,hρ,hρs,hcharts⟩ := MovingCenter.isMinimizerAt_moving_C1_modulus hV hE hmin hcenter
  obtain ⟨N,hN,hp,hu⟩ := normalMeasure_polar_unit hμ
  obtain ⟨δ,hδ,hchart⟩ := hcharts μ hμ N hN hp hu
  let e := δ/2
  have he : 0<e := half_pos hδ
  have heδ : e≤δ := by dsimp [e]; linarith
  let s : ℕ → ℝ := fun i ↦ 1/((i : ℝ)+1)
  have hs (i : ℕ) : 0<s i := by dsimp [s]; positivity
  have hslim : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨n,φ,hn,hφ,hconv⟩ := isMinimizerAt_primary_halfspace hV hE hmin hcenter s hs hslim
  obtain ⟨η,hη,hsmall⟩ := isMinimizerAt_halfspace_L1_tilt_small hV hE hmin hμ hH hn
    (show 0<e^2/272^2 by positivity)
  have hlim := hslim.comp hφ.tendsto_atTop
  have hbound : 0 < min η (min (272*R) (min (272*δ*e^2) 1)) := by positivity
  obtain ⟨i,hi,hLi⟩ := ((hlim.eventually (Iio_mem_nhds hbound)).and
    (hconv.eventually (Iio_mem_nhds hη))).exists
  let t := s (φ i)
  have ht : 0<t := hs _
  have htη : t<η := hi.trans_le (min_le_left _ _)
  have htR : t/272≤R := by
    have hh := hi.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    change t < _ at hh
    linarith
  have hratio : (t/272)/e^2≤δ := by
    apply (div_le_iff₀ (sq_pos_of_pos he)).mpr
    have hh := hi.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    change t < _ at hh
    linarith
  have ht1 : t<1 := hi.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  let c : MovingCenter.InteriorCenter := ⟨cubeCenter,by simp⟩
  have htilt := hsmall c t ht htη hLi
  have hinterior : Metric.ball cubeCenter (t/8) ⊆ {x | ∀ j, 0<x j ∧ x j<1} :=
    Metric.ball_subset_closedBall.trans (MovingCenter.closedBall_interior (c := c) (by linarith))
  have htsp := spatial_tilt_le_blowupTilt hN hp hu cubeCenter n ht hinterior
  have hb : (∫ x in Metric.closedBall (quotientMap cubeCenter) (17*(t/272)), ‖N x-n‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (t/272)^2*e^2 := by
    rw [show 17*(t/272)=t/16 by ring]
    calc
      _ ≤ _ := htsp
      _ ≤ t^2*(e^2/272^2) := mul_le_mul_of_nonneg_left htilt.le (sq_nonneg _)
      _ = _ := by ring
  obtain ⟨g,M,hM,hg,hgC,hinside,hcover,hmod⟩ := hchart cubeCenter (by simp) hcenter
    n (t/272) e hn (by positivity) htR he heδ hratio hb
  let r := (t/272)/1024
  have hr : 0<r := by dsimp [r]; positivity
  have hrepr0 := hcover cubeCenter ⟨hcenter,Metric.mem_ball_self (by positivity)⟩
  have hg0 : g 0=0 := by
    simp only [sub_self,map_zero] at hrepr0
    have hh := congrArg (fun x : Cover ↦ ⟪n,x⟫) hrepr0
    simpa only [normalGraph_inner hn,inner_zero_right] using hh
  refine ⟨n,g,r,M,ρ,hn,hr,hM,hρ,hρs,hg,hg0,hgC,?_,?_,?_⟩
  · intro y hy
    simpa only [quotientMap_add] using (hinside y hy).1
  · intro x hx
    constructor
    · intro hxb
      have hx' : cubeCenter+x∈Metric.ball cubeCenter ((t/272)/128) := by
        rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left]
        have hh : ‖x‖<r := by simpa only [Metric.mem_ball,dist_zero_right] using hx
        dsimp [r] at hh
        linarith
      simpa only [add_sub_cancel_left] using hcover (cubeCenter+x) ⟨hxb,hx'⟩
    · intro heq
      have hy : normalPlaneCoordinates n x∈Metric.ball (0 : Plane) r := by
        rw [Metric.mem_ball,dist_zero_right]
        exact (by simpa using (normalPlaneCoordinates_lipschitz n).dist_le_mul x 0 : ‖normalPlaneCoordinates n x‖≤‖x‖).trans_lt
          (by simpa only [Metric.mem_ball,dist_zero_right] using hx)
      have hh := (hinside (normalPlaneCoordinates n x) hy).1
      rw [heq] at hh
      simpa only [quotientMap_add] using hh

  · intro j x hx y hy hxy
    apply hmod j x hx y hy
    apply hxy.trans
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hρ.le _)
    dsimp [r]
    linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem actual_centered_graph_phase_patch {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E))
    {n : Cover} {g : Plane → ℝ} {r : ℝ} (hn : ‖n‖=1) (hr : 0<r)
    (hg : LipschitzWith (1/4) g) (hg0 : g 0=0)
    (hgC : ContDiffOn ℝ 1 g (Metric.ball 0 r))
    (hcover : ∀ x∈Metric.ball (0 : Cover) r,
      quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n x)=x) :
    ∃ (R ρ : ℝ) (U : Set Cover), R<r ∧
      ‖n‖=1 ∧ LipschitzWith (1/4) g ∧ g 0=0 ∧ 0<R ∧ 0<ρ ∧
      (∀ y∈Metric.closedBall (0 : Plane) R, ContDiffAt ℝ 1 g y) ∧
      IsOpen U ∧ Metric.closedBall cubeCenter (2*ρ) ⊆ U ∧
      U ⊆ Metric.ball cubeCenter R ∧ U ⊆ {x | ∀ i, 0<x i ∧ x i<1} ∧
      (∀ x∈U, quotientMap x∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n (x-cubeCenter))=x-cubeCenter) ∧
      ((∀ᵐ x : Cover ∂volume, x∈U → (quotientMap x∈E ↔ graphSignedHeight cubeCenter n g x<0)) ∨
       (∀ᵐ x : Cover ∂volume, x∈U → (quotientMap x∈E ↔ 0<graphSignedHeight cubeCenter n g x))) := by
  let R := r/2
  let s := min (r/4) (1/8)
  have hR : 0<R := half_pos hr
  have hs : 0<s := lt_min (by positivity) (by norm_num)
  have hsR : s<R := by dsimp [s,R]; exact (min_le_left _ _).trans_lt (by linarith)
  have hcell : Metric.ball cubeCenter s ⊆ {x | ∀ i, 0<x i ∧ x i<1} := by
    let c : MovingCenter.InteriorCenter := ⟨cubeCenter,by simp⟩
    apply Metric.ball_subset_closedBall.trans
    exact MovingCenter.closedBall_interior (c := c) (by
      have hh : s≤1/8 := min_le_right _ _
      linarith)
  have hb (x : Cover) (hx : x∈Metric.ball cubeCenter s) :
      quotientMap x∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n (x-cubeCenter))=x-cubeCenter := by
    have hx' : x-cubeCenter∈Metric.ball (0 : Cover) r := by
      simp only [Metric.mem_ball,dist_zero_right]
      have hh : ‖x-cubeCenter‖<s := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
      have hsr : s<r := by dsimp [R] at hsR; linarith
      exact hh.trans hsr
    simpa only [add_sub_cancel] using hcover (x-cubeCenter) hx'
  have hlift (x : Cover) (hx : x∈Metric.ball cubeCenter s) :=
    isMinimizerAt_lifted_boundary hV hE hmin (hcell hx)
  have hp : cubeCenter∈coverEssentialBoundary (quotientMap ⁻¹' E) :=
    (hlift cubeCenter (Metric.mem_ball_self hs)).mpr hcenter
  obtain ⟨W,hW,hpW,hWU,hphase⟩ := cover_graph_boundary_phases
    (hE.preimage measurable_quotientMap) cubeCenter hn hg.continuous
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hs)) hp
    (fun x hx ha ↦ (hb x hx).mp ((hlift x hx).mp ha))
  obtain ⟨t,ht,htW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hpW)
  let ρ := t/3
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  refine ⟨R,ρ,W,by dsimp [R]; linarith,hn,hg,hg0,hR,hρ,?_,hW,?_,?_,hWU.trans hcell,
    fun x hx ↦ hb x (hWU hx),hphase.symm⟩
  · intro y hy
    apply hgC.contDiffAt
    apply Metric.isOpen_ball.mem_nhds
    apply Metric.closedBall_subset_ball _ hy
    dsimp [R]
    linarith
  · exact (Metric.closedBall_subset_ball (by dsimp [ρ]; linarith)).trans htW
  · exact hWU.trans (Metric.ball_subset_ball hsR.le)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem actual_centered_graph_CMC {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E))
    {n : Cover} {g : Plane → ℝ} {r : ℝ} (hn : ‖n‖=1) (hr : 0<r)
    (hg : LipschitzWith (1/4) g) (hg0 : g 0=0)
    (hgC : ContDiffOn ℝ 1 g (Metric.ball 0 r))
    (hcover : ∀ x∈Metric.ball (0 : Cover) r,
      quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n x)=x) :
    ∃ (R ρ H : ℝ), R<r ∧
      ‖n‖=1 ∧ LipschitzWith (1/4) g ∧ g 0=0 ∧ 0<R ∧ 0<ρ ∧
      (∀ y∈Metric.closedBall (0 : Plane) R, ContDiffAt ℝ 1 g y) ∧
      Metric.closedBall cubeCenter (2*ρ)⊆Metric.ball cubeCenter R ∧
      (∀ x∈Metric.closedBall cubeCenter (2*ρ), quotientMap x∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n (x-cubeCenter))=x-cubeCenter) ∧
      ∀ (F : Cover → Cover), ContDiff ℝ (⊤ : ℕ∞) F →
        tsupport F⊆Metric.closedBall cubeCenter ρ →
        (∫ y : Plane, tangentialDivergence F (cubeCenter+normalGraph n g y)
          (graphSlopeNormal n (gradient g y))*‖graphAreaVector n g y‖)=
          H*(∫ y : Plane, ⟪graphAreaVector n g y,F (cubeCenter+normalGraph n g y)⟫) := by
  obtain ⟨R,ρ,U,hRr,_,_,_,hR,hρ,hgc,hU,hρU,hUR,hUO,hbd,hphase⟩ :=
    actual_centered_graph_phase_patch hV hE hmin hcenter hn hr hg hg0 hgC hcover
  obtain ⟨μ,hμ⟩ := exists_normalMeasure hE hmin.1.2.ne
  obtain ⟨H,hH⟩ := isMinimizerAt_centered_multiplier hV hE hmin hcenter hμ
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
    (hgc y hy).continuousAt_fderiv (by norm_num)
  rcases hphase with hphase|hphase
  · have hp : ∀ᵐ x : Cover ∂volume, x∈U →
        (quotientMap x∈E ↔ ⟪n,x-cubeCenter⟫<graphHeightExtension cubeCenter n g x) := by
      simpa only [graphSignedHeight,sub_neg] using hphase
    refine ⟨R,ρ,H,hRr,hn,hg,hg0,hR,hρ,hgc,hρU.trans hUR,
      fun x hx ↦ hbd x (hρU hx),?_⟩
    intro F hF hsF
    have hFs : HasCompactSupport F := (isCompact_closedBall cubeCenter ρ).of_isClosed_subset isClosed_closure hsF
    exact normalMeasure_C1graph_CMC hE hμ
      (fun F hF hc hs ↦ weakCMC_local_identity hμ hH hF hc hs)
      cubeCenter hn hg hdc hp hφ hsφ hφU hφO hφR hφb hF hFs
      (fun x hx ↦ radialHeightCutoff_one hρ (hsF hx))
  · have hp : ∀ᵐ x : Cover ∂volume, x∈U →
        (x∈(quotientMap ⁻¹' E) ↔ graphHeightExtension cubeCenter n g x<⟪n,x-cubeCenter⟫) := by
      simpa only [graphSignedHeight,sub_pos,mem_preimage] using hphase
    have hp' := graph_superlevel_compl_ae cubeCenter hn hg.continuous hp
    have hμ' := isNormalMeasure_compl hE hμ
    refine ⟨R,ρ,-H,hRr,hn,hg,hg0,hR,hρ,hgc,hρU.trans hUR,
      fun x hx ↦ hbd x (hρU hx),?_⟩
    intro F hF hsF
    have hFs : HasCompactSupport F := (isCompact_closedBall cubeCenter ρ).of_isClosed_subset isClosed_closure hsF
    exact normalMeasure_C1graph_CMC hE.compl hμ'
      (fun F hF hc hs ↦ reverseNormal_local_CMC hμ hH hF hc hs)
      cubeCenter hn hg hdc hp' hφ hsφ hφU hφO hφR hφb hF hFs
      (fun x hx ↦ radialHeightCutoff_one hρ (hsF hx))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem actual_centered_graph_weakCMC {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E))
    {n : Cover} {g : Plane → ℝ} {r₀ : ℝ} (hn : ‖n‖=1) (hr₀ : 0<r₀)
    (hg : LipschitzWith (1/4) g) (hg0 : g 0=0)
    (hgC : ContDiffOn ℝ 1 g (Metric.ball 0 r₀))
    (hcover : ∀ x∈Metric.ball (0 : Cover) r₀,
      quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n x)=x) :
    ∃ (r H : ℝ), r<r₀ ∧ ‖n‖=1 ∧ 0<r ∧
      LipschitzWith (1/4) g ∧ g 0=0 ∧ ContDiffOn ℝ 1 g (Metric.ball 0 r) ∧
      (∀ y∈Metric.ball (0 : Plane) r,
        quotientMap (cubeCenter+normalGraph n g y)∈frontier (openRepresentative E)) ∧
      (∀ x∈Metric.ball (0 : Cover) r,
        quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
          normalGraph n g (normalPlaneCoordinates n x)=x) ∧
      WeakCMCGraph g H (Metric.ball 0 r) := by
  obtain ⟨R,ρ,H,hRr,_,_,_,hR,hρ,hgc,hρR,hbd,hCMC⟩ :=
    actual_centered_graph_CMC hV hE hmin hcenter hn hr₀ hg hg0 hgC hcover
  let r := min (R/2) (ρ/4)
  have hr : 0<r := lt_min (by positivity) (by positivity)
  have hrR : r<R := (min_le_left _ _).trans_lt (by linarith)
  have hrρ : r≤ρ/4 := min_le_right _ _
  have hgb (y : Plane) : ‖normalGraph n g y‖≤(5/4)*‖y‖ := by
    have hh := (normalGraph_lipschitz hn hg).dist_le_mul y 0
    have hz : normalGraph n g 0=0 := by
      change normalPlaneLinearIsometry n 0+g 0 • n=0
      rw [map_zero,hg0,zero_smul,zero_add]
    rw [hz] at hh
    norm_num only [dist_zero_right,NNReal.coe_add,NNReal.coe_one,NNReal.coe_div,
      NNReal.coe_ofNat] at hh ⊢
    exact hh
  have hry (y : Plane) (hy : y∈Metric.ball (0 : Plane) r) :
      cubeCenter+normalGraph n g y∈Metric.ball cubeCenter (ρ/2) := by
    rw [Metric.mem_ball,dist_self_add_left]
    have hyl : ‖y‖<r := by simpa only [Metric.mem_ball,dist_zero_right] using hy
    have hh := hgb y
    nlinarith
  refine ⟨r,H,hrR.trans hRr,hn,hr,hg,hg0,?_,?_,?_,?_⟩
  · intro y hy
    exact (hgc y (Metric.ball_subset_closedBall ((Metric.ball_subset_ball hrR.le) hy))).contDiffWithinAt
  · intro y hy
    have hx := Metric.ball_subset_closedBall ((Metric.ball_subset_ball (by linarith : ρ/2≤2*ρ)) (hry y hy))
    apply (hbd _ hx).mpr
    simp only [add_sub_cancel_left,normalPlaneCoordinates_graph hn]
  · intro x hx
    have hx' : cubeCenter+x∈Metric.closedBall cubeCenter (2*ρ) := by
      rw [Metric.mem_closedBall,dist_self_add_left]
      have hh : ‖x‖<r := by simpa only [Metric.mem_ball,dist_zero_right] using hx
      linarith
    simpa only [add_sub_cancel_left] using hbd (cubeCenter+x) hx'
  · intro ψ hψ _hsψ hsψ
    have hh := CMC_graph_weak_equation cubeCenter hn g H hρ hCMC hψ (fun y hy ↦ hry y (hsψ hy))
    simpa only [cmcFlux,map_smul,smul_eq_mul,graphAreaVector_norm_sqrt hn,div_eq_mul_inv,
      mul_comm] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_centered_holder_CMC {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E)) :
    ∃ (n : Cover) (g : Plane → ℝ) (r H α C : ℝ), ‖n‖=1 ∧ 0<r ∧
      0<α ∧ α≤1 ∧ 0≤C ∧ LipschitzWith (1/4) g ∧ g 0=0 ∧
      ContDiffOn ℝ 1 g (Metric.ball 0 r) ∧
      (∀ y∈Metric.ball (0 : Plane) r,
        quotientMap (cubeCenter+normalGraph n g y)∈frontier (openRepresentative E)) ∧
      (∀ x∈Metric.ball (0 : Cover) r,
        quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
          normalGraph n g (normalPlaneCoordinates n x)=x) ∧
      WeakCMCGraph g H (Metric.ball 0 r) ∧
      (∀ x∈Metric.ball (0 : Plane) r, ∀ y∈Metric.ball (0 : Plane) r,
        dist (fderiv ℝ g x) (fderiv ℝ g y)≤C*(dist x y)^α) := by
  obtain ⟨n,g,R,M,ρ,hn,hR,hM,hρ,hρs,hg,hg0,hgC,hi,hcover,hm⟩ :=
    isMinimizerAt_centered_C1_modulus hV hE hmin hcenter
  have hsub : Metric.ball (0 : Plane) (R/2) ⊆ Metric.ball 0 R :=
    Metric.ball_subset_ball (by linarith)
  obtain ⟨α,C,hα,hα1,hC,hHolder⟩ := holder_bound_of_geometric_modulus
    (f := fderiv ℝ g) (S := Metric.ball (0 : Plane) (R/2)) hρ
    (by linarith : ρ≤1/2) hR hM
    (by
      intro x hx y hy
      have hx' : dist x 0<R/2 := hx
      have hy' : dist y 0<R/2 := hy
      calc
        dist x y ≤ dist x 0+dist y 0 := dist_triangle_right x y 0
        _ ≤ R := by linarith)
    (fun i x hx y hy hxy ↦ hm i x (hsub hx) y (hsub hy) hxy)
  obtain ⟨r,H,hrR,_,hr,_,_,hgc,hinside,hcov,hcmc⟩ :=
    actual_centered_graph_weakCMC hV hE hmin hcenter hn (half_pos hR)
      hg hg0 (hgC.mono hsub)
      (fun x hx ↦ hcover x ((Metric.ball_subset_ball (by linarith : R/2≤R)) hx))
  refine ⟨n,g,r,H,α,C,hn,hr,hα,hα1,hC,hg,hg0,hgc,hinside,hcov,hcmc,?_⟩
  intro x hx y hy
  exact hHolder x ((Metric.ball_subset_ball hrR.le) hx)
    y ((Metric.ball_subset_ball hrR.le) hy)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_centered_C2_graph {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E)) :
    ∃ (n : Cover) (g : Plane → ℝ) (r H : ℝ), ‖n‖=1 ∧ 0<r ∧
      LipschitzWith (1/4) g ∧ g 0=0 ∧ ContDiffOn ℝ 2 g (Metric.ball 0 r) ∧
      (∀ y∈Metric.ball (0 : Plane) r,
        quotientMap (cubeCenter+normalGraph n g y)∈frontier (openRepresentative E)) ∧
      (∀ x∈Metric.ball (0 : Cover) r,
        quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
          normalGraph n g (normalPlaneCoordinates n x)=x) ∧
      WeakCMCGraph g H (Metric.ball 0 r) := by
  obtain ⟨n,g,R,H,α,C,hn,hR,hα,hα1,hC,hg,hg0,hgc,hi,hcover,hw,hHolder⟩ :=
    isMinimizerAt_centered_holder_CMC hV hE hmin hcenter
  obtain ⟨r,hr,hrR,hg2⟩ := hw.local_C2 hg (by norm_num) hR hgc hα hα1 hC hHolder
  refine ⟨n,g,r,H,hn,hr,hg,hg0,hg2,fun y hy ↦ hi y ((Metric.ball_subset_ball hrR) hy),
    fun x hx ↦ hcover x ((Metric.ball_subset_ball hrR) hx),?_⟩
  intro ψ hψ hc hs
  exact hw ψ hψ hc (hs.trans (Metric.ball_subset_ball hrR))

def TorusC2CMCAt (E : Set Torus) (a : Torus) : Prop :=
  ∃ (n : Cover) (g : Plane → ℝ) (r H : ℝ), ‖n‖=1 ∧ 0<r ∧
    LipschitzWith (1/4) g ∧ g 0=0 ∧ ContDiffOn ℝ 2 g (Metric.ball 0 r) ∧
    (∀ y∈Metric.ball (0 : Plane) r,
      a+quotientMap (normalGraph n g y)∈frontier (openRepresentative E)) ∧
    (∀ x∈Metric.ball (0 : Cover) r,
      a+quotientMap x∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n x)=x) ∧
    WeakCMCGraph g H (Metric.ball 0 r)

theorem isMinimizerAt_C2_boundary {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (a : Torus) (ha : a∈frontier (openRepresentative E)) : TorusC2CMCAt E a := by
  let b := a-quotientMap cubeCenter
  let F := (fun z : Torus ↦ z+b) ⁻¹' E
  have hF : MeasurableSet F := hE.preimage (continuous_add_const b).measurable
  have hminF : IsMinimizerAt V F := isMinimizerAt_translation hmin b
  have hbd : frontier (openRepresentative F)=(fun z : Torus ↦ z+b) ⁻¹'
      frontier (openRepresentative E) := frontier_openRepresentative_translation hE b
  have hbase : quotientMap cubeCenter∈frontier (openRepresentative F) := by
    rw [hbd]
    change quotientMap cubeCenter+(a-quotientMap cubeCenter)∈frontier (openRepresentative E)
    convert ha using 1
    abel
  obtain ⟨n,g,r,H,hn,hr,hg,hg0,hgC,hinside,hcover,hw⟩ :=
    isMinimizerAt_centered_C2_graph hV hF hminF hbase
  have he (x : Cover) : quotientMap (cubeCenter+x)+b=a+quotientMap x := by
    rw [quotientMap_add]
    dsimp [b]
    abel
  refine ⟨n,g,r,H,hn,hr,hg,hg0,hgC,?_,?_,hw⟩
  · intro y hy
    have hh := hinside y hy
    rw [hbd,mem_preimage,he] at hh
    exact hh
  · intro x hx
    have hh := hcover x hx
    rw [hbd,mem_preimage,he] at hh
    exact hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_classical_CMC {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (a : Torus) (ha : a∈frontier (openRepresentative E)) :
    ∃ (n : Cover) (g : Plane → ℝ) (r H : ℝ), ‖n‖=1 ∧ 0<r ∧
      LipschitzWith (1/4) g ∧ g 0=0 ∧ ContDiffOn ℝ 2 g (Metric.ball 0 r) ∧
      (∀ y∈Metric.ball (0 : Plane) r,
        a+quotientMap (normalGraph n g y)∈frontier (openRepresentative E)) ∧
      (∀ x∈Metric.ball (0 : Cover) r,
        a+quotientMap x∈frontier (openRepresentative E) ↔
          normalGraph n g (normalPlaneCoordinates n x)=x) ∧
      (∀ y∈Metric.ball (0 : Plane) r,
        planeDivergence (fun z ↦ cmcFlux (gradient g z)) y= -H) := by
  obtain ⟨n,g,R,H,hn,hR,hg,hg0,hgc,hi,hcover,hw⟩ :=
    isMinimizerAt_C2_boundary hV hE hmin a ha
  have hrR : R/2≤R := by linarith
  exact ⟨n,g,R/2,H,hn,by linarith,hg,hg0,
    hgc.mono (Metric.ball_subset_ball hrR),
    fun y hy ↦ hi y ((Metric.ball_subset_ball hrR) hy),
    fun x hx ↦ hcover x ((Metric.ball_subset_ball hrR) hx),
    hw.classical hR hgc⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_smooth_CMC {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (a : Torus) (ha : a∈frontier (openRepresentative E)) :
    ∃ (n : Cover) (g : Plane → ℝ) (r H : ℝ), ‖n‖=1 ∧ 0<r ∧
      LipschitzWith (1/4) g ∧ g 0=0 ∧ ContDiffOn ℝ (⊤ : ℕ∞) g (Metric.ball 0 r) ∧
      (∀ y∈Metric.ball (0 : Plane) r,
        a+quotientMap (normalGraph n g y)∈frontier (openRepresentative E)) ∧
      (∀ x∈Metric.ball (0 : Cover) r,
        a+quotientMap x∈frontier (openRepresentative E) ↔
          normalGraph n g (normalPlaneCoordinates n x)=x) ∧
      WeakCMCGraph g H (Metric.ball 0 r) ∧
      (∀ y∈Metric.ball (0 : Plane) r,
        planeDivergence (fun z ↦ cmcFlux (gradient g z)) y= -H) := by
  obtain ⟨n,g,R,H,hn,hR,hg,hg0,hgc,hi,hcover,hw⟩ :=
    isMinimizerAt_C2_boundary hV hE hmin a ha
  have hrR : R/2≤R := by linarith
  exact ⟨n,g,R/2,H,hn,by linarith,hg,hg0,
    (hw.C2_smooth hg (by norm_num) hgc).mono (Metric.ball_subset_ball hrR),
    fun y hy ↦ hi y ((Metric.ball_subset_ball hrR) hy),
    fun x hx ↦ hcover x ((Metric.ball_subset_ball hrR) hx),
    fun ψ hψ hc ht ↦ hw ψ hψ hc (ht.trans (Metric.ball_subset_ball hrR)),
    hw.classical hR hgc⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_gradient_mul {f g : Plane → ℝ} {x : Plane}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    gradient (fun y ↦ f y*g y) x=f x • gradient g x+g x • gradient f x := by
  apply ext_inner_left ℝ
  intro v
  simp only [inner_gradient_right,inner_add_right,real_inner_smul_right,
    fderiv_fun_mul hf hg,add_apply,smul_apply,smul_eq_mul,starRingEnd_apply,star_trivial]

lemma plane_gradient_contDiff {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (gradient f) :=
  (InnerProductSpace.toDual ℝ Plane).symm.toContinuousLinearEquiv.contDiff.comp
    (hf.fderiv_right (by simp))

def graphJacobiForm (A : Plane → Plane →L[ℝ] Plane) (q φ ψ : Plane → ℝ) : ℝ :=
  ∫ y,(q y)^2*⟪gradient φ y,A y (gradient ψ y)⟫-
    q y*planeDivergence (fun z ↦ A z (gradient q z)) y*φ y*ψ y

theorem graphJacobiForm_transform {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hAs : ∀ y v w,⟪v,A y w⟫=⟪w,A y v⟫)
    {q φ ψ : Plane → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) :
    graphJacobiForm A q φ ψ=
      ∫ y,⟪gradient (fun z ↦ q z*φ z) y,A y (gradient (fun z ↦ q z*ψ z) y)⟫ := by
  have hgq := plane_gradient_contDiff hq
  have hgφ := plane_gradient_contDiff hφ
  have hgψ := plane_gradient_contDiff hψ
  let F : Plane → Plane := fun y ↦ A y (gradient q y)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := hA.clm_apply hgq
  have htest : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ q y*φ y*ψ y) := (hq.mul hφ).mul hψ
  have htestc : HasCompactSupport (fun y ↦ q y*φ y*ψ y) := hc.mul_left
  have hibp := plane_divergence_integration_by_parts (hF.of_le (by simp))
    (htest.of_le (by simp)) htestc
  have hmain : Integrable (fun y ↦ (q y)^2*⟪gradient φ y,A y (gradient ψ y)⟫) := by
    apply ((hq.continuous.pow 2).mul (hgφ.continuous.inner (hA.continuous.clm_apply hgψ.continuous))).integrable_of_hasCompactSupport
    apply hc.mono'
    intro y hy
    by_contra hys
    have he := fderiv_of_notMem_tsupport ℝ hys
    have hge : gradient ψ y=0 := by simp [gradient,he]
    simp [hge] at hy
  have hpot : Integrable (fun y ↦ q y*planeDivergence F y*φ y*ψ y) :=
    (((hq.continuous.mul (planeDivergence_continuous (hF.of_le (by simp)))).mul hφ.continuous).mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hcross : Integrable (fun y ↦ fderiv ℝ (fun z ↦ q z*φ z*ψ z) y (F y)) :=
    ((htest.continuous_fderiv (by simp)).clm_apply hF.continuous).integrable_of_hasCompactSupport
      (htestc.mono' (by
        intro y hy
        by_contra hn
        have he := fderiv_of_notMem_tsupport ℝ hn
        simp [he] at hy))
  have hpoint (y : Plane) :
      ⟪gradient (fun z ↦ q z*φ z) y,A y (gradient (fun z ↦ q z*ψ z) y)⟫=
        (q y)^2*⟪gradient φ y,A y (gradient ψ y)⟫+
          fderiv ℝ (fun z ↦ q z*φ z*ψ z) y (F y) := by
    rw [plane_gradient_mul (hq.differentiable (by simp) y) (hφ.differentiable (by simp) y),
      plane_gradient_mul (hq.differentiable (by simp) y) (hψ.differentiable (by simp) y)]
    simp only [map_add,map_smul,inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
      fderiv_fun_mul ((hq.mul hφ).differentiable (by simp) y) (hψ.differentiable (by simp) y),
      fderiv_fun_mul (hq.differentiable (by simp) y) (hφ.differentiable (by simp) y),
      add_apply,smul_apply,smul_eq_mul]
    simp only [← inner_gradient_left,F]
    rw [hAs y (gradient q y) (gradient ψ y)]
    ring
  unfold graphJacobiForm
  rw [integral_sub hmain hpot]
  simp_rw [hpoint]
  rw [integral_add hmain hcross]
  have he : (∫ y,q y*planeDivergence F y*φ y*ψ y)=
      -(∫ y,fderiv ℝ (fun z ↦ q z*φ z*ψ z) y (F y)) := by
    convert hibp using 1
    congr 1; funext y; ring
  rw [he,sub_neg_eq_add]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_inner_components (u v : Plane) : ⟪u,v⟫=u 0*v 0+u 1*v 1 := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,star_trivial]
  ring

lemma plane_gradient_component (f : Plane → ℝ) (y : Plane) (i : Fin 2) :
    gradient f y i=fderiv ℝ f y (EuclideanSpace.single i 1) := by
  rw [← inner_gradient_left, EuclideanSpace.inner_single_right]
  simp

lemma planeDivergence_add {F G : Plane → Plane} {y : Plane}
    (hF : DifferentiableAt ℝ F y) (hG : DifferentiableAt ℝ G y) :
    planeDivergence (fun z ↦ F z+G z) y=planeDivergence F y+planeDivergence G y := by
  simp only [planeDivergence,fderiv_fun_add hF hG,add_apply,PiLp.add_apply]
  ring

lemma planeDivergence_smul {a : Plane → ℝ} {F : Plane → Plane} {y : Plane}
    (ha : DifferentiableAt ℝ a y) (hF : DifferentiableAt ℝ F y) :
    planeDivergence (fun z ↦ a z • F z) y=
      a y*planeDivergence F y+⟪gradient a y,F y⟫ := by
  rw [plane_inner_components]
  simp only [plane_gradient_component,planeDivergence,fderiv_fun_smul ha hF,
    add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  ring

lemma plane_gradient_weight {p : Plane → Plane} (hp : ContDiff ℝ (⊤ : ℕ∞) p) (y : Plane) :
    gradient (fun z ↦ cmcWeight (p z)) y=
      (cmcWeight (p y))⁻¹ •
        (p y 0 • gradient (fun z ↦ p z 0) y+p y 1 • gradient (fun z ↦ p z 1) y) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left]
  have he := ((cmcWeight_hasFDerivAt (p y)).comp y
    ((hp.differentiable (by simp) y).hasFDerivAt)).fderiv
  change fderiv ℝ (fun z ↦ cmcWeight (p z)) y=_ at he
  rw [he]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,innerSL_apply_apply,
    smul_eq_mul,inner_add_left,real_inner_smul_left,inner_gradient_left,
    plane_component_fderiv (hp.of_le (by simp)),plane_inner_components]

lemma plane_gradient_div {a b : Plane → ℝ} {y : Plane}
    (ha : DifferentiableAt ℝ a y) (hb : DifferentiableAt ℝ b y) (hby : b y≠0) :
    gradient (fun z ↦ a z/b z) y=
      (b y)⁻¹ • gradient a y-(a y/(b y)^2) • gradient b y := by
  apply ext_inner_right ℝ
  intro v
  have hi := (hasDerivAt_inv hby).comp_hasFDerivAt y hb.hasFDerivAt
  have hd := (ha.hasFDerivAt.mul hi).fderiv
  change fderiv ℝ (fun z ↦ a z*(b z)⁻¹) y=_ at hd
  simp only [div_eq_mul_inv,inner_gradient_left,inner_sub_left,real_inner_smul_left,hd,
    add_apply,smul_apply,smul_eq_mul,Function.comp_def]
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

lemma plane_hessian_direction {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (y v : Plane) : fderiv ℝ (gradient g) y v=
      gradient (fun z ↦ fderiv ℝ g z v) y := by
  ext i
  rw [← plane_component_fderiv ((plane_gradient_contDiff hg).of_le (by simp))]
  simp_rw [plane_gradient_component]
  rw [fderiv_fderiv_apply hg,fderiv_fderiv_apply hg]
  exact (hg.contDiffAt.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)) v _

lemma plane_hessian_symmetric {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (y v w : Plane) : ⟪fderiv ℝ (gradient g) y v,w⟫=⟪v,fderiv ℝ (gradient g) y w⟫ := by
  rw [plane_hessian_direction hg,plane_hessian_direction hg]
  conv_rhs => rw [real_inner_comm]
  rw [inner_gradient_left,inner_gradient_left,fderiv_fderiv_apply hg,fderiv_fderiv_apply hg]
  exact (hg.contDiffAt.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)) w v

def graphShapeOperator (g : Plane → ℝ) (y : Plane) : Plane →L[ℝ] Plane :=
  (cmcJacobian (gradient g y)).comp (fderiv ℝ (gradient g) y)

def planeTraceSquare (L : Plane →L[ℝ] Plane) : ℝ :=
  (L (EuclideanSpace.single 0 1) 0)^2+
    2*L (EuclideanSpace.single 0 1) 1*L (EuclideanSpace.single 1 1) 0+
    (L (EuclideanSpace.single 1 1) 1)^2

def graphSquaredSecondFundamentalForm (g : Plane → ℝ) (y : Plane) : ℝ :=
  planeTraceSquare (graphShapeOperator g y)

lemma plane_shape_trace_identity (p : Plane) (L : Plane →L[ℝ] Plane)
    (hL : ∀ v w : Plane,⟪L v,w⟫=⟪v,L w⟫) :
    (⟪L (EuclideanSpace.single 0 1),cmcJacobian p (L (EuclideanSpace.single 0 1))⟫+
      ⟪L (EuclideanSpace.single 1 1),cmcJacobian p (L (EuclideanSpace.single 1 1))⟫-
      ⟪(cmcWeight p)⁻¹ • L p,cmcJacobian p ((cmcWeight p)⁻¹ • L p)⟫)/cmcWeight p=
      planeTraceSquare ((cmcJacobian p).comp L) := by
  have hc : L (EuclideanSpace.single 0 1) 1=L (EuclideanSpace.single 1 1) 0 := by
    simpa only [EuclideanSpace.inner_single_right,EuclideanSpace.inner_single_left,
      conj_trivial,one_mul] using hL (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
  have he : L p=p 0 • L (EuclideanSpace.single 0 1)+p 1 • L (EuclideanSpace.single 1 1) := by
    conv_lhs => rw [plane_decompose p]
    simp only [map_add,map_smul]
  simp only [planeTraceSquare,ContinuousLinearMap.comp_apply,cmcJacobian_apply,
    inner_sub_right,real_inner_smul_left,real_inner_smul_right,he,inner_add_left,inner_add_right,
    plane_inner_components,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,hc]
  field_simp
  ring

lemma graphSquaredSecondFundamentalForm_formula {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : Plane) :
    graphSquaredSecondFundamentalForm g y=
      (⟪gradient (fun z ↦ gradient g z 0) y,cmcJacobian (gradient g y) (gradient (fun z ↦ gradient g z 0) y)⟫+
        ⟪gradient (fun z ↦ gradient g z 1) y,cmcJacobian (gradient g y) (gradient (fun z ↦ gradient g z 1) y)⟫-
        ⟪gradient (fun z ↦ cmcWeight (gradient g z)) y,
          cmcJacobian (gradient g y) (gradient (fun z ↦ cmcWeight (gradient g z)) y)⟫)/cmcWeight (gradient g y) := by
  have hi (i : Fin 2) : gradient (fun z ↦ gradient g z i) y=
      fderiv ℝ (gradient g) y (EuclideanSpace.single i 1) := by
    simp_rw [plane_gradient_component]
    exact (plane_hessian_direction hg y _).symm
  have hq : gradient (fun z ↦ cmcWeight (gradient g z)) y=
      (cmcWeight (gradient g y))⁻¹ • fderiv ℝ (gradient g) y (gradient g y) := by
    rw [plane_gradient_weight (plane_gradient_contDiff hg),hi 0,hi 1]
    congr 1
    conv_rhs => rw [plane_decompose (gradient g y)]
    simp only [map_add,map_smul]
  rw [hi 0,hi 1,hq]
  exact (plane_shape_trace_identity (gradient g y) (fderiv ℝ (gradient g) y)
    (plane_hessian_symmetric hg y)).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeTrace (L : Plane →L[ℝ] Plane) : ℝ :=
  ∑ i : Fin 2,L (EuclideanSpace.single i 1) i

lemma plane_decompose_sum (v : Plane) : v=∑ i : Fin 2,v i • EuclideanSpace.single i 1 := by
  rw [Fin.sum_univ_two]
  exact plane_decompose v

lemma plane_cover_clm_component (L : Plane →L[ℝ] Cover) (v : Plane) (i : Fin 3) :
    L v i=∑ j : Fin 2,v j*L (EuclideanSpace.single j 1) i := by
  change (EuclideanSpace.proj i : Cover →L[ℝ] ℝ) (L v)=_
  conv_lhs => rw [plane_decompose_sum v,map_sum,map_sum]
  simp only [map_smul,smul_eq_mul]
  rfl

lemma cover_plane_clm_component (L : Cover →L[ℝ] Plane) (v : Cover) (i : Fin 2) :
    L v i=∑ j : Fin 3,v j*L (EuclideanSpace.single j 1) i := by
  change (EuclideanSpace.proj i : Plane →L[ℝ] ℝ) (L v)=_
  conv_lhs => rw [cover_decompose v,map_sum,map_sum]
  simp only [map_smul,smul_eq_mul]
  rfl

lemma rectangular_trace (L : Plane →L[ℝ] Cover) (P : Cover →L[ℝ] Plane) :
    coverTrace (L.comp P)=planeTrace (P.comp L) := by
  simp only [coverTrace,planeTrace,ContinuousLinearMap.comp_apply]
  conv_lhs => enter [2,i]; rw [plane_cover_clm_component]
  conv_rhs => enter [2,i]; rw [cover_plane_clm_component]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma planeTrace_square (L : Plane →L[ℝ] Plane) :
    planeTrace (L.comp L)=planeTraceSquare L := by
  simp only [planeTrace,Fin.sum_univ_two,ContinuousLinearMap.comp_apply]
  rw [plane_decompose (L (EuclideanSpace.single 0 1)),
    plane_decompose (L (EuclideanSpace.single 1 1))]
  simp only [map_add,map_smul,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  unfold planeTraceSquare
  ring

@[simp] lemma planeTrace_neg (L : Plane →L[ℝ] Plane) : planeTrace (-L)= -planeTrace L := by
  simp [planeTrace,Finset.sum_neg_distrib]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cmcJacobian_inner_slope (p v : Plane) :
    ⟪p,cmcJacobian p v⟫=((cmcWeight p)^3)⁻¹*⟪p,v⟫ := by
  rw [cmcJacobian_apply,inner_sub_right,inner_smul_right,inner_smul_right,real_inner_self_eq_norm_sq]
  have hs := cmcWeight_sq p
  have hn := (cmcWeight_pos p).ne'
  field_simp [hn]
  nlinarith [congrArg (fun r : ℝ ↦ r*⟪p,v⟫) hs]

lemma normalGraph_fderiv_apply {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (n : Cover) (y v : Plane) :
    fderiv ℝ (normalGraph n g) y v=normalPlaneEmbedding n v+⟪gradient g y,v⟫ • n := by
  rw [(normalGraph_hasFDerivAt (hg.differentiable (by simp) y)).fderiv]
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,inner_gradient_left]
  rfl

lemma graphSlopeNormal_weight {n : Cover} (hn : ‖n‖=1) (p : Plane) :
    graphSlopeNormal n p=(cmcWeight p)⁻¹ • (n-normalPlaneEmbedding n p) := by
  have he : ‖n-normalPlaneEmbedding n p‖=cmcWeight p := by
    rw [cmcWeight,← graphSlopeVector_norm_sq hn p,Real.sqrt_sq (norm_nonneg _)]
  simp only [graphSlopeNormal,he]

theorem graph_weingarten {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y v : Plane) :
    fderiv ℝ (fun z ↦ graphSlopeNormal n (gradient g z)) y v=
      -fderiv ℝ (normalGraph n g) y (graphShapeOperator g y v) := by
  let p := gradient g y
  let L := fderiv ℝ (gradient g) y
  have hp := plane_gradient_contDiff hg
  have hq := (cmcWeight_hasFDerivAt p).comp y
    ((hp.differentiable (by simp) y).hasFDerivAt)
  have hi := (hasDerivAt_inv (cmcWeight_pos p).ne').comp_hasFDerivAt y hq
  have hN := (hasFDerivAt_const n y).sub
    ((normalPlaneLinearIsometry n).toContinuousLinearMap.hasFDerivAt.comp y
      ((hp.differentiable (by simp) y).hasFDerivAt))
  have hd := (hi.smul hN).fderiv
  have he : (fun z ↦ graphSlopeNormal n (gradient g z))=
      (fun z ↦ (cmcWeight (gradient g z))⁻¹ • (n-normalPlaneEmbedding n (gradient g z))) :=
    funext fun z ↦ graphSlopeNormal_weight hn _
  rw [he]
  change fderiv ℝ (fun z ↦ (cmcWeight (gradient g z))⁻¹ •
    (n-normalPlaneEmbedding n (gradient g z))) y=_ at hd
  rw [hd,normalGraph_fderiv_apply hg]
  change _= -(normalPlaneEmbedding n (cmcJacobian p (L v))+⟪p,cmcJacobian p (L v)⟫ • n)
  rw [cmcJacobian_inner_slope,cmcJacobian_apply]
  have hE : normalPlaneEmbedding n=(normalPlaneLinearIsometry n).toContinuousLinearMap := rfl
  rw [hE]
  simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply,
    neg_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, smul_eq_mul,
    Function.comp_def, Pi.sub_apply, p, L, map_sub, map_smul, smul_sub,
    zero_sub, smul_neg, neg_add_rev, ← inv_pow]
  module

end CubicTorus
end
end
end

end OAI
