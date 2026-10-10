import Mathlib
import OAI.Geometry.CubicTorus.Estimates.PlaneQuadraticWeight

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem plane_interior_ball_at_frontier {D : Set Plane} (hD : IsOpen D)
    {a : Plane} (ha : a∈frontier D) {ε : ℝ} (hε : 0<ε) :
    ∃ (c y : Plane) (R : ℝ),0<R ∧
      Metric.ball c R⊆D ∧ ‖y-c‖=R ∧ y∈frontier D ∧
      Metric.closedBall c R⊆Metric.ball a ε := by
  have hac : a∈closure D := frontier_subset_closure ha
  have had : a∉D := by
    rw [frontier, hD.interior_eq] at ha
    exact ha.2
  obtain ⟨c,hcD,hca⟩ := Metric.mem_closure_iff.mp hac (ε/4) (by positivity)
  have hcomp : Dᶜ.Nonempty := ⟨a,had⟩
  let R := Metric.infDist c Dᶜ
  have hR : 0<R := (hD.isClosed_compl.notMem_iff_infDist_pos hcomp).mp (by simpa using hcD)
  have hRa : R≤dist c a := Metric.infDist_le_dist_of_mem had
  obtain ⟨y,hyc,hRy⟩ := hD.isClosed_compl.exists_infDist_eq_dist hcomp c
  have hball : Metric.ball c R⊆D := Metric.ball_infDist_compl_subset
  have hyR : ‖y-c‖=R := by
    rw [← dist_eq_norm,dist_comm]
    exact hRy.symm
  have hycl : y∈closure D := by
    apply closure_mono hball
    rw [closure_ball c hR.ne']
    simpa only [Metric.mem_closedBall,dist_eq_norm,hyR] using (le_refl R)
  refine ⟨c,y,R,hR,hball,hyR,?_,?_⟩
  · rw [frontier,hD.interior_eq]
    exact ⟨hycl,hyc⟩
  · intro z hz
    have hzR : dist z c≤R := hz
    have hca' : dist c a<ε/4 := by simpa only [dist_comm] using hca
    have hza := dist_triangle z c a
    change dist z a<ε
    linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeElliptic_continue_ball {A : Plane → Plane →L[ℝ] Plane}
    {f : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hf : PlaneSmooth f)
    (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    {U : Set Plane} (hU : IsOpen U) {a c : Plane} (ha : a∈U)
    {ℓ R : ℝ} (hℓ : 0<ℓ) (hR : 0<R) (hd : ‖a-c‖=R)
    (hell : ∀ v,ℓ*‖v‖^2≤⟪v,A a v⟫)
    (heq : ∀ x∈U,planeElliptic A f x=0)
    (hz : ∀ x∈Metric.ball c R,f x=0) :
    a∈interior {x | f x=0} := by
  let n : Plane := (1/R) • (c-a)
  have hn : ‖n‖=1 := by
    dsimp [n]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (show 0<1/R by positivity),norm_sub_rev,hd]
    exact one_div_mul_cancel hR.ne'
  have hc : a+R • n=c := by
    dsimp [n]
    rw [smul_smul,mul_one_div_cancel hR.ne',one_smul]
    abel
  exact planeElliptic_continue_tangent_ball hA hf hAs hU ha hn hℓ hR hell heq (by simpa [hc] using hz)

theorem planeElliptic_unique_continuation {A : Plane → Plane →L[ℝ] Plane}
    {f : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hf : PlaneSmooth f)
    (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    {U : Set Plane} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hell : ∀ x∈U,∃ ℓ>0,∀ v,ℓ*‖v‖^2≤⟪v,A x v⟫)
    (heq : ∀ x∈U,planeElliptic A f x=0)
    (hpatch : (U∩interior {x | f x=0}).Nonempty) :
    ∀ x∈U,f x=0 := by
  let D := interior {x | f x=0}
  have hD : IsOpen D := isOpen_interior
  have hno : Disjoint (frontier D) U := by
    rw [Set.disjoint_left]
    intro a ha haU
    obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU a haU
    obtain ⟨c,y,R,hR,hball,hyR,hyD,hsub⟩ := plane_interior_ball_at_frontier hD ha hε
    have hyU : y∈U := hεU (hsub (by
      simpa only [Metric.mem_closedBall,dist_eq_norm,hyR] using (le_refl R)))
    obtain ⟨ℓ,hℓ,hell⟩ := hell y hyU
    have hyz := planeElliptic_continue_ball hA hf hAs hU hyU hℓ hR hyR hell heq
      (fun x hx => show x∈{y | f y=0} from interior_subset (hball hx))
    have hyn : y∉D := by
      rw [frontier,hD.interior_eq] at hyD
      exact hyD.2
    exact hyn hyz
  have hsub : U⊆D := hUc.subset_of_closure_inter_subset hD hpatch (by
    intro x hx
    by_contra hn
    apply Set.disjoint_left.mp hno ?_ hx.2
    rw [frontier,hD.interior_eq]
    exact ⟨hx.1,hn⟩)
  exact fun x hx => show x∈{y | f y=0} from interior_subset (hsub hx)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeSymbolDrift (A : Plane → Plane →L[ℝ] Plane) (x : Plane) : Plane :=
  ∑ j : Fin 2,planeDivergence (fun z => A z (EuclideanSpace.single j 1)) x •
    EuclideanSpace.single j 1

lemma planeDivergence_symbol {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) {u : Plane → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x : Plane) :
    planeDivergence (fun z => A z (gradient u z)) x=
      planeTrace ((A x).comp (fderiv ℝ (gradient u) x))+
        ⟪gradient u x,planeSymbolDrift A x⟫ := by
  have hda := (hA.differentiable (by simp) x).hasFDerivAt
  have hdu := ((plane_gradient_contDiff hu).differentiable (by simp) x).hasFDerivAt
  have hprod := hda.clm_apply hdu
  have hc (j : Fin 2) := hda.clm_apply (hasFDerivAt_const (EuclideanSpace.single j (1 : ℝ)) x)
  simp only [planeSymbolDrift,planeDivergence,planeTrace]
  rw [hprod.fderiv]
  simp_rw [(hc _).fderiv]
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    zero_apply,ContinuousLinearMap.flip_apply,ContinuousLinearMap.comp_zero,
    Fin.sum_univ_two,inner_add_right,real_inner_smul_right,
    EuclideanSpace.inner_single_right,conj_trivial,one_mul,PiLp.add_apply]
  rw [plane_decompose (gradient u x)]
  simp only [map_add,map_smul,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,
    PiLp.single_apply,ite_true,mul_one]
  norm_num
  ring

lemma cmc_compress_hessian_trace (p : Plane) (L : Plane →L[ℝ] Plane) :
    (∑ i : Fin 2,⟪L (cmcCompress p (EuclideanSpace.single i 1)),
      cmcCompress p (EuclideanSpace.single i 1)⟫)=
      cmcWeight p*planeTrace ((cmcJacobian p).comp L) := by
  calc
    _ = planeTrace ((cmcCompress p).comp (L.comp (cmcCompress p))) := by
      simp only [planeTrace,ContinuousLinearMap.comp_apply,← cmcCompress_symm,
        EuclideanSpace.inner_single_right,conj_trivial,one_mul]
    _ = planeTrace ((L.comp (cmcCompress p)).comp (cmcCompress p)) := planeTrace_comp_comm _ _
    _ = planeTrace (L.comp ((cmcCompress p).comp (cmcCompress p))) := by rfl
    _ = planeTrace (((cmcCompress p).comp (cmcCompress p)).comp L) := planeTrace_comp_comm _ _
    _ = _ := by
      simp only [planeTrace,ContinuousLinearMap.comp_apply,cmcCompress_sq,PiLp.smul_apply,
        smul_eq_mul,← Finset.mul_sum]

lemma cmc_frame_operator {g u : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x : Plane) :
    planeFrameOperator (fun y i => cmcCompress (gradient g y) (EuclideanSpace.single i 1))
      (fun y => cmcWeight (gradient g y) •
        planeSymbolDrift (fun z => cmcJacobian (gradient g z)) y) u x=
      cmcWeight (gradient g x)*planeDivergence
        (fun y => cmcJacobian (gradient g y) (gradient u y)) x := by
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun z => cmcJacobian (gradient g z)) :=
    cmcJacobian_contDiff.comp (plane_gradient_contDiff hg)
  rw [planeDivergence_symbol hA hu]
  simp only [planeFrameOperator,cmc_compress_hessian_trace,real_inner_smul_right]
  ring

lemma cmc_frame_ellipticity {p : Plane} (hp : ‖p‖≤1) (v : Plane) :
    (1/4 : ℝ)*‖v‖^2≤∑ i : Fin 2,⟪v,cmcCompress p (EuclideanSpace.single i 1)⟫^2 := by
  have he : (∑ i : Fin 2,⟪v,cmcCompress p (EuclideanSpace.single i 1)⟫^2)=‖cmcCompress p v‖^2 := by
    simp only [← cmcCompress_symm,EuclideanSpace.inner_single_right,conj_trivial,one_mul]
    rw [EuclideanSpace.norm_sq_eq]
    simp
  rw [he]
  have hh := cmcStretch_norm hp (cmcCompress p v)
  rw [cmcStretch_compress] at hh
  nlinarith [norm_nonneg (cmcCompress p v),norm_nonneg v]

lemma cmc_frame_bound {p : Plane} (hp : ‖p‖≤1) :
    (∑ i : Fin 2,‖cmcCompress p (EuclideanSpace.single i 1)‖^2)≤8 := by
  have hh (i : Fin 2) : ‖cmcCompress p (EuclideanSpace.single i 1)‖≤2 := by
    simpa using cmcCompress_norm hp (EuclideanSpace.single i 1)
  rw [Fin.sum_univ_two]
  nlinarith [hh 0,hh 1,norm_nonneg (cmcCompress p (EuclideanSpace.single 0 1)),
    norm_nonneg (cmcCompress p (EuclideanSpace.single 1 1))]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeSymbolDrift_continuous {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) : Continuous (planeSymbolDrift A) := by
  unfold planeSymbolDrift
  apply continuous_finsetSum
  intro i _
  exact (planeDivergence_continuous ((hA.clm_apply contDiff_const).of_le (by simp))).smul continuous_const

theorem LinearCMCEquation.hopf {g u : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {c y : Plane} {R : ℝ} (hR : 0<R)
    (hp : ∀ x∈Metric.closedBall c R,‖gradient g x‖≤1)
    (hw : LinearCMCEquation u (gradient g) (fun _ => 0) (Metric.ball c R))
    (hpos : ∀ x∈Metric.ball c R,0<u x)
    (hy : ‖y-c‖=R) (huy : u y=0) :
    0<fderiv ℝ u y (c-y) := by
  let A : Plane → Plane →L[ℝ] Plane := fun x => cmcJacobian (gradient g x)
  let b : Plane → Plane := fun x => cmcWeight (gradient g x) • planeSymbolDrift A x
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := cmcJacobian_contDiff.comp (plane_gradient_contDiff hg)
  have hb : Continuous b := (cmcWeight_contDiff.comp (plane_gradient_contDiff hg)).continuous.smul
    (planeSymbolDrift_continuous hA)
  obtain ⟨C,hC⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hb.continuousOn
  let K := max 8 (max C 0)
  have hK8 : 8≤K := le_max_left _ _
  have hKC : C≤K := (le_max_left C 0).trans (le_max_right _ _)
  have hK : 0≤K := (le_max_right C 0).trans (le_max_right _ _)
  apply planeFrameOperator_hopf
    (fun x i => cmcCompress (gradient g x) (EuclideanSpace.single i 1)) b hu c hR
    (by norm_num : 0<(1/4 : ℝ)) hK ?_ ?_ ?_ hy huy
  · intro x _ hxR
    have hx : x∈Metric.closedBall c R := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hxR
    exact ⟨cmc_frame_ellipticity (hp x hx) (x-c),
      (cmc_frame_bound (hp x hx)).trans hK8,(hC x hx).trans hKC⟩
  · intro x hx
    change planeFrameOperator _ (fun y => cmcWeight (gradient g y) •
      planeSymbolDrift (fun z => cmcJacobian (gradient g z)) y) u x≤0
    rw [cmc_frame_operator hg hu,hw.classical_zero hg hu Metric.isOpen_ball x
      (by simpa only [Metric.mem_ball,dist_eq_norm] using hx),mul_zero]
  · intro x hx
    exact hpos x (by simpa only [Metric.mem_ball,dist_eq_norm] using hx)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cmcJacobian_strict_coercive (p v : Plane) :
    (1/(cmcWeight p)^3)*‖v‖^2≤⟪v,cmcJacobian p v⟫ := by
  rw [cmcJacobian_self]
  have hp := cmcWeight_pos p
  have hw := cmcWeight_sq p
  have hcs := real_inner_mul_inner_self_le p v
  simp only [real_inner_self_eq_norm_sq] at hcs
  rw [one_div_mul_eq_div,div_le_div_iff_of_pos_right (by positivity : 0<(cmcWeight p)^3)]
  nlinarith

theorem LinearCMCEquation.unique_continuation {g u : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {U : Set Plane} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hw : LinearCMCEquation u (gradient g) (fun _ => 0) U)
    (hpatch : (U∩interior {x | u x=0}).Nonempty) : ∀ x∈U,u x=0 := by
  exact planeElliptic_unique_continuation (cmcJacobian_contDiff.comp (plane_gradient_contDiff hg)) hu
    (fun x v w => (cmcJacobian_symmetric _ _ _).trans (real_inner_comm _ _)) hU hUc
    (fun x _ => ⟨1/(cmcWeight (gradient g x))^3,by have hh := cmcWeight_pos (gradient g x); positivity,cmcJacobian_strict_coercive _⟩)
    (hw.classical_zero hg hu hU) hpatch

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem actual_centered_normal_linear_chart {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    ∃ (n : Cover) (f : Plane → ℝ) (σ : ℝ),‖n‖=1 ∧
      ContDiff ℝ (⊤ : ℕ∞) f ∧ f 0=0 ∧ (σ=1 ∨ σ= -1) ∧
      (∀ᶠ y in 𝓝 (0 : Plane),N (cubeCenter+normalGraph n f y)=
        σ • graphSlopeNormal n (gradient f y) ∧
        quotientMap (cubeCenter+normalGraph n f y)∈frontier (openRepresentative E)) ∧
      (∀ᶠ v in 𝓝 (0 : Cover),quotientMap (cubeCenter+v)∈frontier (openRepresentative E) ↔
        normalGraph n f (normalPlaneCoordinates n v)=v) ∧
      ∃ r : ℝ,0<r ∧ (∀ y∈Metric.ball (0 : Plane) r,‖gradient f y‖≤1) ∧
        ∀ i : Fin 2,LinearCMCEquation
          (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) (gradient f)
          (fun _ => 0) (Metric.ball 0 r) := by
  obtain ⟨n,g,r,H,hn,hr,hg,hg0,hgc,hi,hcover,hw,_⟩ :=
    isMinimizerAt_smooth_CMC hV hE hmin (quotientMap cubeCenter) hcenter
  obtain ⟨f,Kf,p,rj,D,hrj,hrjr,hf,hfc,hfL,hfg,hp0,hpb,hD,hpf,hpD,hlin⟩ :=
    hw.smooth_jacobi_data hg (by norm_num) hr hgc
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
      ∀ᵐ z ∂(μ : Measure NormalBundle),0<φ z.1 →
        σ • graphUnitNormalExtension cubeCenter n f z.1=(z.2 : Cover) := by
    rcases hphase with hphase|hphase
    · have hh : ∀ᵐ x : Cover ∂volume,x∈U →
          (quotientMap x∈E ↔ ⟪n,x-cubeCenter⟫<graphHeightExtension cubeCenter n g x) := by
        simpa only [graphSignedHeight,sub_neg] using hphase
      refine ⟨1,Or.inl rfl,?_⟩
      filter_upwards [normalMeasure_graph_normal_ae hE hμ cubeCenter hn hg hdc hh
        hφ hsφ hφU hφO hφR hφb] with z hz hpos
      rw [one_smul,hNfg _ (subset_tsupport _ hpos.ne')]
      exact (hz hpos).symm
    · have hh : ∀ᵐ x : Cover ∂volume,x∈U →
          (x∈quotientMap ⁻¹' E ↔ graphHeightExtension cubeCenter n g x<⟪n,x-cubeCenter⟫) := by
        simpa only [graphSignedHeight,sub_pos,mem_preimage] using hphase
      have hh' := graph_superlevel_compl_ae cubeCenter hn hg.continuous hh
      have hh'' := normalMeasure_graph_normal_ae hE.compl (isNormalMeasure_compl hE hμ)
        cubeCenter hn hg hdc hh' hφ hsφ hφU hφO hφR hφb
      have hm : ∀ᵐ z ∂(μ : Measure NormalBundle),0<φ z.1 →
          -(z.2 : Cover)=graphUnitNormalExtension cubeCenter n g z.1 :=
        ae_of_ae_map continuous_reverseNormal.measurable.aemeasurable hh''
      refine ⟨-1,Or.inr rfl,?_⟩
      filter_upwards [hm] with z hz hpos
      rw [neg_one_smul,hNfg _ (subset_tsupport _ hpos.ne'),← hz hpos,neg_neg]
  obtain ⟨σ,hσ,hσae⟩ := hsign
  let F : Cover → Cover := fun x ↦ φ x • (N x-σ • graphUnitNormalExtension cubeCenter n f x)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := hφ.smul
    (hN.sub ((graphUnitNormalExtension_contDiff _ hn hf).const_smul σ))
  have hsF : HasCompactSupport F := hsφ.smul_right
  have hFO : tsupport F⊆{x | ∀ i,0<x i ∧ x i<1} :=
    (tsupport_smul_subset_left _ _).trans hφO
  have he := latticePeriodize_eventuallyEq hsF hFO
    (show ∀ i,0≤cubeCenter i ∧ cubeCenter i≤1 by intro i; norm_num [cubeCenter])
  have hz : ∀ᵐ z ∂(μ : Measure NormalBundle),latticePeriodize F z.1=(0 : Cover) := by
    filter_upwards [hae,hσae] with z hz hloc
    rw [(latticePeriodize_eventuallyEq hsF hFO (compactCell_coordinates z.1)).eq_of_nhds]
    change φ z.1 • (N z.1-σ • graphUnitNormalExtension cubeCenter n f z.1)=0
    by_cases hpos : 0<φ z.1
    · rw [hz,hloc hpos,sub_self,smul_zero]
    · have hzφ : φ z.1=0 := le_antisymm (le_of_not_gt hpos) (hφb z.1).1
      rw [hzφ,zero_smul]
  have hb (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
      latticePeriodize F x=0 := by
    have hboundary : latticePeriodize F x+N x=N x :=
      isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ
        ((latticePeriodize_contDiff hF hsF).continuous.add hN.continuous) hN.continuous
        (fun shift point => by simp only [Pi.add_apply,latticePeriodize_periodic,hp]) hp
        (hz.mono fun point hzero => by simp only [Pi.add_apply,hzero,zero_add]) x hx
    exact add_right_cancel (hboundary.trans (zero_add _).symm)
  have hf0 : f 0=0 := (hfg (by simpa using (half_pos hr))).trans hg0
  have ht : Tendsto (fun y ↦ cubeCenter+normalGraph n f y) (𝓝 (0 : Plane)) (𝓝 cubeCenter) := by
    have hc : Continuous (fun y ↦ cubeCenter+normalGraph n f y) :=
      continuous_const.add ((normalPlaneLinearIsometry n).continuous.add
        (hf.continuous.smul continuous_const))
    have hz : cubeCenter+normalGraph n f 0=cubeCenter := by
      simp only [normalGraph,hf0,zero_smul,add_zero]
      change cubeCenter+(normalPlaneLinearIsometry n) 0=cubeCenter
      rw [map_zero,add_zero]
    simpa only [ContinuousAt,hz] using hc.continuousAt (x := 0)
  have hone : ∀ᶠ x in 𝓝 cubeCenter,φ x=1 := by
    filter_upwards [Metric.ball_mem_nhds cubeCenter hρ] with x hx
    exact radialHeightCutoff_one hρ (Metric.ball_subset_closedBall hx)
  refine ⟨n,f,σ,hn,hf,hf0,hσ,?_,?_,rj,hrj,?_,hlin⟩
  ·
    filter_upwards [ht.eventually he,ht.eventually hone,Metric.ball_mem_nhds (0 : Plane) (half_pos hr)]
      with y hey hoy hy
    have hgraph : normalGraph n f y=normalGraph n g y := by simp only [normalGraph,hfg hy]
    have hby : quotientMap (cubeCenter+normalGraph n f y)∈frontier (openRepresentative E) := by
      rw [quotientMap_add,hgraph]
      exact hi y ((Metric.ball_subset_ball (by linarith)) hy)
    have hzero := hb _ hby
    rw [hey] at hzero
    change φ (cubeCenter+normalGraph n f y) •
      (N (cubeCenter+normalGraph n f y)-σ • graphUnitNormalExtension cubeCenter n f
        (cubeCenter+normalGraph n f y))=0 at hzero
    rw [hoy,one_smul,graphUnitNormalExtension_graph cubeCenter hn f f y] at hzero
    exact ⟨sub_eq_zero.mp hzero,hby⟩
  · filter_upwards [Metric.ball_mem_nhds (0 : Cover) (half_pos hr)] with v hv
    have hpv : normalPlaneCoordinates n v∈Metric.ball (0 : Plane) (r/2) := by
      rw [Metric.mem_ball,dist_zero_right] at hv ⊢
      exact (normalPlaneCoordinates_norm_le _ _).trans_lt hv
    rw [hcover' v hv]
    simp only [normalGraph,hfg hpv]

  · intro y hy
    rw [← hpf hy]
    exact hpb y

theorem isMinimizerAt_normal_linear_chart {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
    ∃ (n : Cover) (f : Plane → ℝ) (σ : ℝ),‖n‖=1 ∧
      ContDiff ℝ (⊤ : ℕ∞) f ∧ f 0=0 ∧ (σ=1 ∨ σ= -1) ∧
      (∀ᶠ y in 𝓝 (0 : Plane),N (x+normalGraph n f y)=σ • graphSlopeNormal n (gradient f y) ∧
        quotientMap (x+normalGraph n f y)∈frontier (openRepresentative E)) ∧
      (∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈frontier (openRepresentative E) ↔
        normalGraph n f (normalPlaneCoordinates n v)=v) ∧
      ∃ r : ℝ,0<r ∧ (∀ y∈Metric.ball (0 : Plane) r,‖gradient f y‖≤1) ∧
        ∀ i : Fin 2,LinearCMCEquation
          (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) (gradient f)
          (fun _ => 0) (Metric.ball 0 r) := by
  let a := x-cubeCenter
  let E' := (fun z : Torus ↦ z+quotientMap a) ⁻¹' E
  have hE' : MeasurableSet E' := (continuous_add_const _).measurable hE
  have hmin' : IsMinimizerAt V E' := isMinimizerAt_translation hmin _
  have hc : quotientMap cubeCenter∈frontier (openRepresentative E') := by
    rw [frontier_openRepresentative_translation hE]
    change quotientMap cubeCenter+quotientMap a∈frontier (openRepresentative E)
    rw [← quotientMap_add]
    convert hx using 1
    dsimp [a]
    congr 1
    abel
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
  obtain ⟨n,f,σ,hn,hf,hf0,hσ,hm,hcov,hlin⟩ := actual_centered_normal_linear_chart hV hE' hmin' hc
    (isNormalMeasure_translation hE hμ a) hN' hp' hae'
  have ht (v : Cover) : (cubeCenter+v)+a=x+v := by dsimp [a]; abel
  have htrans (v : Cover) : quotientMap (cubeCenter+v)∈frontier (openRepresentative E') ↔
      quotientMap (x+v)∈frontier (openRepresentative E) := by
    rw [frontier_openRepresentative_translation hE]
    change quotientMap (cubeCenter+v)+quotientMap a∈frontier (openRepresentative E) ↔ _
    rw [← quotientMap_add,ht]
  refine ⟨n,f,σ,hn,hf,hf0,hσ,?_,?_,hlin⟩
  · filter_upwards [hm] with y hy
    refine ⟨?_,(htrans _).mp hy.2⟩
    have hh := hy.1
    change N ((cubeCenter+normalGraph n f y)+a)=_ at hh
    rwa [ht] at hh
  · filter_upwards [hcov] with v hv
    exact (htrans v).symm.trans hv

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma LinearCMCEquation.affine_zero {u v : Plane → ℝ} {p : Plane → Plane}
    {U : Set Plane} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hp : Continuous p)
    (hue : LinearCMCEquation u p (fun _ => 0) U)
    (hve : LinearCMCEquation v p (fun _ => 0) U) (c a b : ℝ) :
    LinearCMCEquation (fun y => c+a*u y+b*v y) p (fun _ => 0) U := by
  have hg (y : Plane) : gradient (fun z => c+a*u z+b*v z) y=
      a • gradient u y+b • gradient v y := by
    have hd := ((hasFDerivAt_const c y).add
      ((hu.differentiable (by simp) y).hasFDerivAt.const_mul a)).add
        ((hv.differentiable (by simp) y).hasFDerivAt.const_mul b)
    have he : fderiv ℝ (fun z => c+a*u z+b*v z) y=
        0+a • fderiv ℝ u y+b • fderiv ℝ v y := hd.fderiv
    simp only [gradient,he,zero_add,map_add,map_smul]
  intro ψ hψ hc hs
  have hi (w : Plane → ℝ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
      Integrable (fun y => fderiv ℝ ψ y (cmcJacobian (p y) (gradient w y))) := by
    apply ((hψ.continuous_fderiv (by simp)).clm_apply
      ((cmcJacobian_contDiff.continuous.comp hp).clm_apply
        (plane_gradient_contDiff hw).continuous)).integrable_of_hasCompactSupport
    apply (hc.fderiv ℝ).mono
    intro y hy hz
    exact hy (by simp only [hz,zero_apply])
  simp_rw [hg,sub_zero,map_add,map_smul,smul_eq_mul]
  rw [integral_add ((hi u hu).const_mul a) ((hi v hv).const_mul b),
    integral_const_mul,integral_const_mul]
  have hu0 := hue ψ hψ hc hs
  have hv0 := hve ψ hψ hc hs
  simp only [sub_zero] at hu0 hv0
  rw [hu0,hv0,mul_zero,mul_zero,add_zero]

def normalTranslationNumerator (n : Cover) (g : Plane → ℝ) (v : Cover) (σ : ℝ)
    (y : Plane) : ℝ := σ*(⟪v,n⟫-⟪normalPlaneCoordinates n v,gradient g y⟫)

lemma normalTranslationNumerator_contDiff (n : Cover) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : Cover) (σ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (normalTranslationNumerator n g v σ) :=
  contDiff_const.mul (contDiff_const.sub (contDiff_const.inner ℝ (plane_gradient_contDiff hg)))

lemma normalTranslationNumerator_eq (n : Cover) (g : Plane → ℝ) (v : Cover) (σ : ℝ)
    (y : Plane) : normalTranslationNumerator n g v σ y=
      σ*⟪v,n⟫+(-σ*(normalPlaneCoordinates n v) 0)*
        fderiv ℝ g y (EuclideanSpace.single 0 1)+
      (-σ*(normalPlaneCoordinates n v) 1)*fderiv ℝ g y (EuclideanSpace.single 1 1) := by
  simp only [normalTranslationNumerator,plane_inner_components,plane_gradient_component]
  ring

lemma normalTranslationNumerator_linear (n : Cover) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : Cover) (σ : ℝ) {U : Set Plane}
    (hlin : ∀ i : Fin 2,LinearCMCEquation
      (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g) (fun _ => 0) U) :
    LinearCMCEquation (normalTranslationNumerator n g v σ) (gradient g) (fun _ => 0) U := by
  simp_rw [show normalTranslationNumerator n g v σ = fun y =>
    σ*⟪v,n⟫+(-σ*(normalPlaneCoordinates n v) 0)*
      fderiv ℝ g y (EuclideanSpace.single 0 1)+
    (-σ*(normalPlaneCoordinates n v) 1)*fderiv ℝ g y (EuclideanSpace.single 1 1)
      from funext (normalTranslationNumerator_eq n g v σ)]
  exact (hlin 0).affine_zero
    ((hg.fderiv_right (by simp)).clm_apply contDiff_const)
    ((hg.fderiv_right (by simp)).clm_apply contDiff_const)
    (plane_gradient_contDiff hg).continuous (hlin 1) _ _ _

lemma normalTranslationNumerator_weight {n : Cover} (hn : ‖n‖=1)
    (g : Plane → ℝ) (v : Cover) (σ : ℝ) (y : Plane) :
    normalTranslationNumerator n g v σ y=
      cmcWeight (gradient g y)*⟪v,σ • graphSlopeNormal n (gradient g y)⟫ := by
  rw [graphSlopeNormal_weight hn]
  simp only [normalTranslationNumerator,inner_smul_right,inner_sub_right]
  have he : ⟪normalPlaneCoordinates n v,gradient g y⟫=
      ⟪v,normalPlaneEmbedding n (gradient g y)⟫ :=
    ContinuousLinearMap.adjoint_inner_left _ _ _
  rw [he]
  field_simp [(cmcWeight_pos (gradient g y)).ne']

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma contDiffAt_occupied_graph_transition {S : Set Torus} {F : Torus → ℝ}
    {x : Cover} {G : Plane → Cover} {a : Plane}
    (hG : ContDiffAt ℝ (⊤ : ℕ∞) G a)
    (hGS : ∀ᶠ y in 𝓝 a,quotientMap (x+G y)∈S)
    {n : Cover} {f : Plane → ℝ} {s : ℝ} (hs : 0<s)
    (hcover : ∀ z∈Metric.ball (0 : Cover) s,
      quotientMap ((x+G a)+z)∈S → normalGraph n f (normalPlaneCoordinates n z)=z)
    (hF : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y => F (quotientMap ((x+G a)+normalGraph n f y))) 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => F (quotientMap (x+G y))) a := by
  let P : Plane → Plane := fun y => normalPlaneCoordinates n (G y-G a)
  have hP : ContDiffAt ℝ (⊤ : ℕ∞) P a :=
    (normalPlaneCoordinates n).contDiff.contDiffAt.comp a (hG.sub contDiffAt_const)
  have hP0 : P a=0 := by simp [P]
  have hF' : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y => F (quotientMap ((x+G a)+normalGraph n f y))) (P a) := by
    rw [hP0]; exact hF
  have hcomp := hF'.comp a hP
  apply hcomp.congr_of_eventuallyEq
  have ht : Tendsto (fun y => G y-G a) (𝓝 a) (𝓝 (0 : Cover)) := by
    have hc : ContinuousAt (fun y => G y-G a) a := hG.continuousAt.sub continuousAt_const
    simpa only [sub_self] using hc.tendsto
  filter_upwards [hGS,ht.eventually (Metric.ball_mem_nhds _ hs)] with y hy hys
  have hy' : quotientMap ((x+G a)+(G y-G a))∈S := by
    convert hy using 1; congr 1; abel
  have he := hcover (G y-G a) hys hy'
  change F (quotientMap (x+G y))=F (quotientMap ((x+G a)+normalGraph n f (P y)))
  rw [show normalGraph n f (P y)=G y-G a from he]
  congr 2
  abel

theorem isMinimizerAt_H1_jacobi_parametric_smooth {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hNu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      ∀ᶠ y in 𝓝 x,‖N y‖=1)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hhom : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u z=0)
    {F : Torus → ℝ} (hFm : Measurable F)
    (hF : ContinuousOn F (frontier (openRepresentative E)))
    (hFu : (u.1 : NormalBundle → ℝ)=ᵐ[(μ : Measure NormalBundle)] F ∘ normalProjection)
    (x : Cover) {G : Plane → Cover} {a : Plane}
    (hG : ContDiffAt ℝ (⊤ : ℕ∞) G a)
    (hGS : ∀ᶠ y in 𝓝 a,quotientMap (x+G y)∈frontier (openRepresentative E)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => F (quotientMap (x+G y))) a := by
  obtain ⟨n,f,s,_,hs,_,_,_,hc,hr⟩ := isMinimizerAt_H1_jacobi_smooth
    hV hE hmin hμ N hN hp hae hNu hu hhom hFm hF hFu (x+G a) hGS.self_of_nhds
  exact contDiffAt_occupied_graph_transition hG hGS hs (fun z hz => (hc z hz).mp) hr

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma quotient_graph_closure {S D : Set Torus} (hDS : D⊆S)
    {x : Cover} {G : Plane → Cover} {P : Cover →L[ℝ] Plane}
    (hcover : ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈S → G (P v)=v)
    (hx : quotientMap x∈closure D) :
    (0 : Plane)∈closure ((fun y => quotientMap (x+G y)) ⁻¹' D) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hP : ∀ᶠ v in 𝓝 (0 : Cover),P v∈Metric.ball (0 : Plane) ε := by
    have ht : Tendsto P (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) := by
      simpa only [map_zero] using P.continuous.tendsto (0 : Cover)
    exact ht.eventually (Metric.ball_mem_nhds _ hε)
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp (hcover.and hP)
  obtain ⟨a,haD,hax⟩ := Metric.mem_closure_iff.mp hx δ hδ
  have ha : a∈Metric.ball (quotientMap x) δ := by
    simpa only [Metric.mem_ball,dist_comm] using hax
  rw [← quotientMap_image_ball x δ] at ha
  obtain ⟨z,hzx,hza⟩ := ha
  have hz : z-x∈Metric.ball (0 : Cover) δ := by
    simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hzx
  obtain ⟨hi,hp⟩ := hsub hz
  have hzs : quotientMap (x+(z-x))∈S := by
    simpa only [add_sub_cancel,hza] using hDS haD
  refine ⟨P (z-x),?_,?_⟩
  · change quotientMap (x+G (P (z-x)))∈D
    rw [hi hzs,add_sub_cancel,hza]
    exact haD
  · simpa only [Metric.mem_ball,dist_comm] using hp

lemma planar_positive_piece_frontier_zero {f : Plane → ℝ} (hf : Continuous f)
    {D C B : Set Plane} (hD : IsOpen D) (hC : IsClosed C)
    (hsub : D⊆{x | 0<f x}∩C)
    (hDC : ∀ x∈B,0<f x → x∈C → x∈D)
    {y : Plane} (hy : y∈frontier D) (hyB : y∈B) : f y=0 := by
  have hclC : closure D⊆C := closure_minimal (hsub.trans inter_subset_right) hC
  have hclP : closure D⊆{x | 0≤f x} := closure_minimal
    (fun x hx => show 0≤f x from (hsub hx).1.le) (isClosed_le continuous_const hf)
  have hyc := frontier_subset_closure hy
  have hnD : y∉D := by rw [hD.frontier_eq] at hy; exact hy.2
  exact le_antisymm (le_of_not_gt fun hp => hnD (hDC y hyB hp (hclC hyc))) (hclP hyc)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def relativeZeroNeighborhood (S : Set Torus) (F : Torus → ℝ) : Set Torus :=
  interior (Sᶜ∪{a | F a=0})

lemma relativeZeroNeighborhood_zero {S : Set Torus} {F : Torus → ℝ} {a : Torus}
    (ha : a∈S) (hz : a∈relativeZeroNeighborhood S F) : F a=0 := by
  have h : a∈Sᶜ∪{a | F a=0} := interior_subset hz
  exact h.resolve_left (fun hn => hn ha)

lemma quotient_graph_zero_germ {S : Set Torus} {F : Torus → ℝ}
    {x : Cover} {G : Plane → Cover} {P : Cover →L[ℝ] Plane}
    (hcover : ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈S → G (P v)=v)
    (hz : ∀ᶠ y in 𝓝 (0 : Plane),F (quotientMap (x+G y))=0) :
    quotientMap x∈relativeZeroNeighborhood S F := by
  have hP : Tendsto P (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) := by
    simpa only [map_zero] using P.continuous.tendsto (0 : Cover)
  have hev : ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈S → F (quotientMap (x+v))=0 := by
    filter_upwards [hcover,hP.eventually hz] with v hv hvz hS
    rwa [hv hS] at hvz
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hev
  change quotientMap x∈interior (Sᶜ∪{a | F a=0})
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (Metric.ball_mem_nhds (quotientMap x) hδ)
  intro a ha
  by_cases haS : a∈S
  · right
    rw [← quotientMap_image_ball x δ] at ha
    obtain ⟨z,hz,hza⟩ := ha
    have hz' : z-x∈Metric.ball (0 : Cover) δ := by
      simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hz
    have hh := hball hz'
    change F a=0
    simpa only [add_sub_cancel,hza] using hh (by simpa only [add_sub_cancel,hza] using haS)
  · exact Or.inl haS

lemma preconnected_zero_of_closed_germ {S : Set Torus} {F : Torus → ℝ}
    (hS : IsPreconnected S) (hD : IsClosed (S∩relativeZeroNeighborhood S F))
    (hpatch : (S∩relativeZeroNeighborhood S F).Nonempty) : ∀ a∈S,F a=0 := by
  let Z := relativeZeroNeighborhood S F
  have hZ : IsOpen Z := isOpen_interior
  have hsub : S⊆Z := by
    intro a ha
    by_contra hn
    have hcover : S⊆Z∪(S∩Z)ᶜ := by
      intro b hb
      by_cases hz : b∈Z
      · exact Or.inl hz
      · exact Or.inr (fun hd => hz hd.2)
    obtain ⟨b,hbS,hbZ,hbn⟩ := hS Z (S∩Z)ᶜ hZ hD.isOpen_compl hcover hpatch
      ⟨a,ha,fun hd => hn hd.2⟩
    exact hbn ⟨hbS,hbZ⟩
  exact fun a ha => relativeZeroNeighborhood_zero ha (hsub ha)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_normal_zero_germs_closed {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (v : Cover) :
    IsClosed (frontier (openRepresentative E)∩relativeZeroNeighborhood
      (frontier (openRepresentative E)) (fun a => ⟪v,N (representative a)⟫)) := by
  let S := frontier (openRepresentative E)
  let F : Torus → ℝ := fun a => ⟪v,N (representative a)⟫
  let Z := relativeZeroNeighborhood S F
  let D := S∩Z
  have hD : D⊆S := inter_subset_left
  apply isClosed_of_closure_subset
  intro a ha
  have haS : a∈S := closure_minimal hD isClosed_frontier ha
  let x := representative a
  have hxa : quotientMap x=a := quotientMap_representative a
  have hx : quotientMap x∈S := by rwa [hxa]
  obtain ⟨n,g,σ,hn,hg,hg0,hσ,hm,hcover,r,hr,hgrad,hlin⟩ :=
    isMinimizerAt_normal_linear_chart hV hE hmin hμ hN hp hae x hx
  let G := normalGraph n g
  let φ : Plane → Torus := fun y => quotientMap (x+G y)
  have hG : ContDiff ℝ (⊤ : ℕ∞) G :=
    (normalPlaneLinearIsometry n).contDiff.add (hg.smul contDiff_const)
  have hφ : Continuous φ := continuous_quotientMap.comp (continuous_const.add hG.continuous)
  obtain ⟨ρ,hρ,hρm⟩ := Metric.mem_nhds_iff.mp hm
  let ε := min r ρ
  have hε : 0<ε := lt_min hr hρ
  have hεr : ε≤r := min_le_left _ _
  have hερ : ε≤ρ := min_le_right _ _
  have hb (y : Plane) (hy : y∈Metric.ball (0 : Plane) ε) :
      N (x+G y)=σ • graphSlopeNormal n (gradient g y) ∧ φ y∈S :=
    hρm (Metric.ball_subset_ball hερ hy)
  let w := normalTranslationNumerator n g v σ
  have hw : PlaneSmooth w := normalTranslationNumerator_contDiff n hg v σ
  have hws (y : Plane) (hy : y∈Metric.ball (0 : Plane) ε) :
      w y=cmcWeight (gradient g y)*F (φ y) := by
    change w y=cmcWeight (gradient g y)*⟪v,N (representative (φ y))⟫
    rw [show N (representative (φ y))=N (x+G y) from periodic_representative hp _,(hb y hy).1]
    exact normalTranslationNumerator_weight hn g v σ y
  have hc : (0 : Plane)∈closure (φ ⁻¹' D) := quotient_graph_closure hD
    (hcover.mono fun z hz => hz.mp) (by rwa [hxa])
  obtain ⟨y,hyD,hyd⟩ := Metric.mem_closure_iff.mp hc ε hε
  have hyb : y∈Metric.ball (0 : Plane) ε := by
    simpa only [Metric.mem_ball,dist_comm] using hyd
  have hO : IsOpen (φ ⁻¹' Z∩Metric.ball 0 ε) :=
    (isOpen_interior.preimage hφ).inter Metric.isOpen_ball
  have hyO : y∈φ ⁻¹' Z∩Metric.ball 0 ε := ⟨hyD.2,hyb⟩
  have hzeroO : φ ⁻¹' Z∩Metric.ball 0 ε⊆{z | w z=0} := by
    intro z hz
    change w z=0
    rw [hws z hz.2,relativeZeroNeighborhood_zero (hb z hz.2).2 hz.1,mul_zero]
  have hpatch : (Metric.ball (0 : Plane) ε∩interior {z | w z=0}).Nonempty :=
    ⟨y,hyb,(hO.subset_interior_iff.mpr hzeroO) hyO⟩
  have hvan := (normalTranslationNumerator_linear n hg v σ hlin |>.mono
    (Metric.ball_subset_ball hεr)).unique_continuation hg hw Metric.isOpen_ball
      (convex_ball (0 : Plane) ε).isPreconnected hpatch
  refine ⟨haS,?_⟩
  rw [← hxa]
  apply quotient_graph_zero_germ (hcover.mono fun z hz => hz.mp)
  filter_upwards [Metric.ball_mem_nhds (0 : Plane) hε] with y hy
  have hz := hvan y hy
  rw [hws y hy] at hz
  exact (mul_eq_zero.mp hz).resolve_left (cmcWeight_pos _).ne'

theorem isMinimizerAt_normal_unique_continuation {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hS : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (v : Cover)
    {U : Set Torus} (hU : IsOpen U) (hpatch : (frontier (openRepresentative E)∩U).Nonempty)
    (hz : ∀ a∈frontier (openRepresentative E)∩U,⟪v,N (representative a)⟫=0) :
    ∀ a∈frontier (openRepresentative E),⟪v,N (representative a)⟫=0 := by
  apply preconnected_zero_of_closed_germ hS
    (isMinimizerAt_normal_zero_germs_closed hV hE hmin hμ hN hp hae v)
  obtain ⟨a,haS,haU⟩ := hpatch
  refine ⟨a,haS,?_⟩
  apply hU.subset_interior_iff.mpr ?_ haU
  intro b hb
  by_cases hbs : b∈frontier (openRepresentative E)
  · exact Or.inr (hz b ⟨hbs,hb⟩)
  · exact Or.inl hbs

end CubicTorus

end
end

end OAI
