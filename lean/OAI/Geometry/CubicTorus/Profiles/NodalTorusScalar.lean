import Mathlib
import OAI.Geometry.CubicTorus.Profiles.PlanarWeakGradient

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem positiveNodalPiece_continuousOn (f : smoothPeriodicScalars) {S D : Set Torus}
    (hD : IsPositiveNodalPiece f S D) :
    ContinuousOn (D.indicator (fun a ↦ f.val (representative a))) S := by
  obtain ⟨⟨U,hU,hDU⟩,⟨C,hC,hDC⟩⟩ := hD
  have hf : Continuous (fun a : S ↦ f.val (representative a.val)) :=
    (continuous_periodic_descent f.property.1.continuous f.property.2).comp continuous_subtype_val
  let D' : Set S := Subtype.val ⁻¹' D
  have hDo : ∃ U' : Set S,IsOpen U' ∧ D'={a | 0<f.val (representative a.val)}∩U' := by
    refine ⟨Subtype.val ⁻¹' U,hU.preimage continuous_subtype_val,?_⟩
    ext a
    simp [D',hDU]
  have hDc : ∃ C' : Set S,IsClosed C' ∧ D'={a | 0<f.val (representative a.val)}∩C' := by
    refine ⟨Subtype.val ⁻¹' C,hC.preimage continuous_subtype_val,?_⟩
    ext a
    simp [D',hDC]
  rw [continuousOn_iff_continuous_domRestrict]
  convert sibling_continuous_indicator_positive_piece hf hDo hDc using 1
  ext a
  change D.indicator _ a.val = D'.indicator _ a
  by_cases ha : a.val∈D
  · rw [Set.indicator_of_mem ha,Set.indicator_of_mem (show a∈D' from ha)]
  · rw [Set.indicator_of_notMem ha,Set.indicator_of_notMem (show a∉D' from ha)]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma CenteredJacobiChart.scalar_representative_ae
    {E : Set Torus} {μ : FiniteMeasure NormalBundle} {N : Cover → Cover}
    (c : CenteredJacobiChart E μ N) (hN : Continuous N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (haeN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    {F : Torus → ℝ} (hF : Measurable F)
    (haeF : ∀ᵐ z ∂(μ : Measure NormalBundle),u.1 z=F (normalProjection z)) :
    (fun y ↦ F (quotientMap (c.parameter y)))=ᵐ[volume.restrict (Metric.closedBall (0 : Plane) c.r)]
      c.value u := by
  obtain ⟨v,G,hv,hG,haeu⟩ := surfaceH1_spatial_representatives hN hp haeN hu
  have hsp : F=ᵐ[(spatialNormalMeasure μ : Measure Torus)] v := by
    apply (ae_map_iff normalProjection_continuous.measurable.aemeasurable
      (measurableSet_eq_fun hF (Lp.stronglyMeasurable v).measurable)).mpr
    filter_upwards [haeF,haeu] with z h₁ h₂
    exact h₁.symm.trans h₂.1
  have hmap := (Measure.absolutelyContinuous_of_le_smul c.domination).ae_eq hsp
  have hf := measurable_quotientMap.comp c.parameter_smooth.continuous.measurable
  have hchart := ae_of_ae_map hf.aemeasurable hmap
  filter_upwards [hchart,c.representatives_ae v G hv hG] with y h₁ h₂
  exact h₁.trans h₂.1.symm

theorem CenteredJacobiChart.boundary_continuous_C1
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
    {F : Torus → ℝ} (hFm : Measurable F)
    (hF : ContinuousOn F (frontier (openRepresentative E)))
    (haeF : ∀ᵐ z ∂(μ : Measure NormalBundle),u.1 z=F (normalProjection z)) :
    ∃ s : ℝ,0<s ∧ s≤c.r/32 ∧
      ContDiffOn ℝ 1 (fun y ↦ F (quotientMap (c.parameter y))) (Metric.ball 0 s) := by
  apply c.continuous_representative_C1 hE hμ hN hp haeN q hu hju hjw
  · exact hF.comp (continuous_quotientMap.comp c.parameter_smooth.continuous).continuousOn
      (fun y hy ↦ c.boundary_disk y (Metric.ball_subset_closedBall hy))
  · exact c.scalar_representative_ae hN.continuous hp haeN hu hFm haeF

def nodalTorusScalar (f : smoothPeriodicScalars) (D : Set Torus) : Torus → ℝ :=
  D.indicator (fun a ↦ f.val (representative a))

lemma nodalTorusScalar_measurable (f : smoothPeriodicScalars) {D : Set Torus}
    (hD : MeasurableSet D) : Measurable (nodalTorusScalar f D) :=
  (continuous_periodic_descent f.property.1.continuous f.property.2).measurable.indicator hD

lemma nodalSurfaceJet_scalar_ae (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars)
    (D : Set Torus) (hD : MeasurableSet D) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),(nodalSurfaceJet μ f D hD).1 z=
      nodalTorusScalar f D (normalProjection z) := by
  filter_upwards [(nodalSurfaceValue_memLp μ f D hD).coeFn_toLp] with z hz
  change (nodalSurfaceJet μ f D hD).1 z=nodalSurfaceValue f D z at hz
  rw [hz]
  by_cases hd : normalProjection z∈D
  · simp only [nodalSurfaceValue,nodalTorusScalar,
      Set.indicator_of_mem hd,Set.indicator_of_mem (show z∈normalProjection ⁻¹' D from hd)]
    exact (periodic_representative f.property.2 z.1).symm
  · simp only [nodalSurfaceValue,nodalTorusScalar,
      Set.indicator_of_notMem hd,Set.indicator_of_notMem (show z∉normalProjection ⁻¹' D from hd)]

lemma surfaceNodalBalance_scalar_ae (μ : FiniteMeasure NormalBundle)
    (f g : smoothPeriodicScalars) (D A : Set Torus) (hD : MeasurableSet D) (hA : MeasurableSet A) :
    let d := nodalSurfaceJet μ f D hD
    let a := nodalSurfaceJet μ g A hA
    ∀ᵐ z ∂(μ : Measure NormalBundle),(surfaceNodalBalance μ d a).1 z=
      surfaceMean μ a*nodalTorusScalar f D (normalProjection z)-
        surfaceMean μ d*nodalTorusScalar g A (normalProjection z) := by
  dsimp only
  let d := nodalSurfaceJet μ f D hD
  let a := nodalSurfaceJet μ g A hA
  filter_upwards [nodalSurfaceJet_scalar_ae μ f D hD,nodalSurfaceJet_scalar_ae μ g A hA,
    Lp.coeFn_add (surfaceMean μ a • d.1) ((-surfaceMean μ d) • a.1),
    Lp.coeFn_smul (surfaceMean μ a) d.1,Lp.coeFn_smul (-surfaceMean μ d) a.1] with
    z hd ha hadd hsm hsa
  change ((surfaceMean μ a • d.1+(-surfaceMean μ d) • a.1 : Lp ℝ 2 _) : NormalBundle → ℝ) z=_
  rw [hadd,Pi.add_apply,hsm,hsa]
  change surfaceMean μ a*d.1 z+(-surfaceMean μ d)*a.1 z=_
  rw [hd,ha]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma localMin_second_derivative_nonneg {f : ℝ → ℝ} {x : ℝ}
    (hmin : IsLocalMin f x) (hc : ContinuousAt f x) : 0≤deriv (deriv f) x := by
  by_contra hn
  have hh : deriv (deriv f) x<0 := lt_of_not_ge hn
  have hmax := isLocalMax_of_deriv_deriv_neg hh hmin.deriv_eq_zero hc
  have he : f=ᶠ[𝓝 x] fun _ ↦ f x := by
    filter_upwards [hmin,hmax] with y h₁ h₂
    exact le_antisymm h₂ h₁
  have hde : deriv f=ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
    filter_upwards [he.deriv] with y hy
    simpa only [deriv_const] using hy
  have hz : deriv (deriv f) x=0 := by rw [hde.deriv_eq,deriv_const]
  linarith

lemma plane_localMin_hessian_nonneg {f : Plane → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {x : Plane} (hm : IsLocalMin f x) (v : Plane) :
    0≤⟪fderiv ℝ (gradient f) x v,v⟫ := by
  let γ : ℝ → Plane := fun t ↦ x+t•v
  have hγ (t : ℝ) : HasDerivAt γ v t := by
    simpa only [γ, id_eq, one_smul] using (hasDerivAt_id t).smul_const v |>.const_add x
  have hγc : ContDiff ℝ (⊤ : ℕ∞) γ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hm' : IsLocalMin (f ∘ γ) (0 : ℝ) :=
    (show IsLocalMin f (γ 0) by simpa only [γ,zero_smul,add_zero] using hm).comp_continuous
      hγc.continuous.continuousAt
  have hd (t : ℝ) : deriv (f ∘ γ) t=fderiv ℝ f (γ t) v :=
    ((hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t (hγ t)).deriv
  have hdall : deriv (f ∘ γ)=fun t ↦ fderiv ℝ f (γ t) v := funext hd
  have hcf : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ fderiv ℝ f y v) :=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  have hdd : deriv (deriv (f ∘ γ)) 0=
      fderiv ℝ (fun y ↦ fderiv ℝ f y v) x v := by
    rw [hdall]
    have he := ((hcf.differentiable (by simp) (γ 0)).hasFDerivAt.comp_hasDerivAt 0 (hγ 0)).deriv
    simpa only [γ,zero_smul,add_zero,Function.comp_def] using he
  have hn := localMin_second_derivative_nonneg hm' (hf.continuous.comp hγc.continuous).continuousAt
  rw [hdd] at hn
  rwa [plane_hessian_direction hf,inner_gradient_left]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeTrace_smul (a : ℝ) (L : Plane →L[ℝ] Plane) :
    planeTrace (a • L)=a*planeTrace L := by
  simp only [planeTrace,smul_apply,PiLp.smul_apply,smul_eq_mul,Finset.mul_sum]

lemma planeTrace_cmc_nonneg (p : Plane) (L : Plane →L[ℝ] Plane)
    (hL : ∀ v : Plane,0≤⟪L v,v⟫) : 0≤planeTrace ((cmcJacobian p).comp L) := by
  let C := cmcCompress p
  have he : (cmcJacobian p).comp L=(cmcWeight p)⁻¹ • (C.comp (C.comp L)) := by
    ext v i
    simp only [ContinuousLinearMap.comp_apply,smul_apply,cmcJacobian_compress,C]
  have ht : planeTrace (C.comp (C.comp L))=planeTrace (C.comp (L.comp C)) := by
    rw [planeTrace_comp_comm C (C.comp L)]
    congr 1
  rw [he,planeTrace_smul,ht]
  apply mul_nonneg (inv_nonneg.mpr (cmcWeight_pos p).le)
  unfold planeTrace
  simp only [ContinuousLinearMap.comp_apply]
  apply Finset.sum_nonneg
  intro i _
  have hh := hL (C (EuclideanSpace.single i 1))
  have hi := cmcCompress_symm p (L (C (EuclideanSpace.single i 1))) (EuclideanSpace.single i 1)
  have hi' : (C (L (C (EuclideanSpace.single i 1)))) i=
      ⟪L (C (EuclideanSpace.single i 1)),C (EuclideanSpace.single i 1)⟫ := by
    simpa only [C,EuclideanSpace.inner_single_right,conj_trivial,one_mul] using hi
  rw [hi']
  exact hh

lemma plane_gradient_eq_zero_of_localMin {f : Plane → ℝ} {x : Plane}
    (hm : IsLocalMin f x) : gradient f x=0 := by
  simp only [gradient,hm.fderiv_eq_zero,map_zero]

lemma cmc_divergence_nonneg_at_localMin {p : Plane → Plane} {f : Plane → ℝ}
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {x : Plane} (hm : IsLocalMin f x) :
    0≤planeDivergence (fun y ↦ cmcJacobian (p y) (gradient f y)) x := by
  rw [planeDivergence_eq_trace,
    fderiv_clm_apply (show DifferentiableAt ℝ (fun y ↦ cmcJacobian (p y)) x from
      (cmcJacobian_contDiff.comp hp).differentiable (by simp) x)
      ((plane_gradient_contDiff hf).differentiable (by simp) x),
    plane_gradient_eq_zero_of_localMin hm,map_zero,add_zero]
  exact planeTrace_cmc_nonneg _ _ (plane_localMin_hessian_nonneg hf hm)

lemma cmc_strict_minimum_principle {p : Plane → Plane} {f : Plane → ℝ}
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {K U : Set Plane} (hK : IsCompact K) (hU : IsOpen U) (hUK : U⊆K)
    (hb : ∀ x∈K,x∉U → 0≤f x)
    (hL : ∀ x∈U,planeDivergence (fun y ↦ cmcJacobian (p y) (gradient f y)) x<0) :
    ∀ x∈K,0≤f x := by
  intro x hx
  by_contra hn
  have hn' : f x<0 := lt_of_not_ge hn
  obtain ⟨z,hz,hmin⟩ := hK.exists_isMinOn ⟨x,hx⟩ hf.continuous.continuousOn
  have hneg : f z<0 := lt_of_le_of_lt (hmin hx) hn'
  have hzu : z∈U := by
    by_contra hzout
    exact (not_le.mpr hneg) (hb z hz hzout)
  have hm : IsLocalMin f z := hmin.isLocalMin (mem_of_superset (hU.mem_nhds hzu) hUK)
  exact (not_lt_of_ge (cmc_divergence_nonneg_at_localMin hp hf hm)) (hL z hzu)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeRadialExp (a : Plane) (k : ℝ) (y : Plane) : ℝ :=
  Real.exp (-k*‖y-a‖^2)

lemma planeRadialExp_contDiff (a : Plane) (k : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (planeRadialExp a k) := by
  have hh : ContDiff ℝ (⊤ : ℕ∞) (fun y : Plane ↦ y-a) := contDiff_id.sub contDiff_const
  exact (contDiff_const.mul (hh.norm_sq ℝ)).exp

lemma planeRadialExp_pos (a : Plane) (k : ℝ) (y : Plane) : 0<planeRadialExp a k y :=
  Real.exp_pos _

lemma planeRadialExp_gradient (a : Plane) (k : ℝ) (y : Plane) :
    gradient (planeRadialExp a k) y=(-2*k*planeRadialExp a k y) • (y-a) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left]
  have hh := ((((hasFDerivAt_id y).sub_const a).norm_sq).const_mul (-k)).exp.fderiv
  change fderiv ℝ (planeRadialExp a k) y=_ at hh
  rw [hh]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
    innerSL_apply_apply,smul_eq_mul,real_inner_smul_left,planeRadialExp,id_eq]
  ring

lemma planeDivergence_const_smul {F : Plane → Plane} {y : Plane}
    (hF : DifferentiableAt ℝ F y) (c : ℝ) :
    planeDivergence (fun z ↦ c • F z) y=c*planeDivergence F y := by
  rw [planeDivergence_smul (differentiableAt_const c) hF,gradient_fun_const,inner_zero_left,add_zero]

lemma sibling_planeDivergence_contDiff {F : Plane → Plane}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) : ContDiff ℝ (⊤ : ℕ∞) (planeDivergence F) := by
  unfold planeDivergence
  exact (((EuclideanSpace.proj 0 : Plane →L[ℝ] ℝ).contDiff.comp
    ((hF.fderiv_right (by simp)).clm_apply contDiff_const)).add
    ((EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).contDiff.comp
      ((hF.fderiv_right (by simp)).clm_apply contDiff_const)))

lemma planeRadialExp_cmc_divergence {p : Plane → Plane}
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) (a : Plane) (k : ℝ) (y : Plane) :
    planeDivergence (fun z ↦ cmcJacobian (p z) (gradient (planeRadialExp a k) z)) y=
      planeRadialExp a k y*(4*k^2*⟪y-a,cmcJacobian (p y) (y-a)⟫-
        2*k*planeDivergence (fun z ↦ cmcJacobian (p z) (z-a)) y) := by
  let F : Plane → Plane := fun z ↦ cmcJacobian (p z) (z-a)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    (cmcJacobian_contDiff.comp hp).clm_apply (contDiff_id.sub contDiff_const)
  have he : (fun z ↦ cmcJacobian (p z) (gradient (planeRadialExp a k) z))=
      (fun z ↦ (-2*k) • (planeRadialExp a k z • F z)) := by
    funext z
    rw [planeRadialExp_gradient,map_smul,smul_smul]
  rw [he,planeDivergence_const_smul
    (show DifferentiableAt ℝ (fun z ↦ planeRadialExp a k z • F z) y from
      ((planeRadialExp_contDiff a k).smul hF).differentiable (by simp) y),
    planeDivergence_smul ((planeRadialExp_contDiff a k).differentiable (by simp) y)
      (hF.differentiable (by simp) y),planeRadialExp_gradient,real_inner_smul_left]
  change (-2*k)*(planeRadialExp a k y*planeDivergence F y+
    (-2*k*planeRadialExp a k y)*⟪y-a,F y⟫)=_
  dsimp only [F]
  ring

lemma planeRadialExp_cmc_positive {p : Plane → Plane}
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) {a y : Plane} {R k M : ℝ}
    (hR : 0<R) (hk : 0<k) (hkM : 16*M<k*R^2)
    (hy : R/2≤‖y-a‖) (hpy : ‖p y‖≤1)
    (hD : planeDivergence (fun z ↦ cmcJacobian (p z) (z-a)) y≤M) :
    0<planeDivergence (fun z ↦ cmcJacobian (p z) (gradient (planeRadialExp a k) z)) y := by
  rw [planeRadialExp_cmc_divergence hp]
  apply mul_pos (planeRadialExp_pos _ _ _)
  have hA := cmcJacobian_coercive hpy (y-a)
  have hn : R^2≤4*‖y-a‖^2 := by nlinarith [norm_nonneg (y-a)]
  have hmul := mul_le_mul_of_nonneg_left (show R^2≤32*⟪y-a,cmcJacobian (p y) (y-a)⟫ by linarith) hk.le
  have hi : 0<2*k*⟪y-a,cmcJacobian (p y) (y-a)⟫-
      planeDivergence (fun z ↦ cmcJacobian (p z) (z-a)) y := by nlinarith
  convert mul_pos (by positivity : 0<2*k) hi using 1
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_gradient_linear {f g : Plane → ℝ} {x : Plane}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (c d : ℝ) :
    gradient (fun y ↦ f y+c*g y+d) x=gradient f x+c • gradient g x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_add_left,real_inner_smul_left]
  simp only [inner_gradient_left,fderiv_add_const,
    fderiv_fun_add hf (hg.const_mul c),fderiv_const_mul hg c,add_apply,smul_apply,smul_eq_mul]

lemma cmc_divergence_linear {p : Plane → Plane} {f g : Plane → ℝ}
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (c d : ℝ) (x : Plane) :
    planeDivergence (fun y ↦ cmcJacobian (p y) (gradient (fun z ↦ f z+c*g z+d) y)) x=
      planeDivergence (fun y ↦ cmcJacobian (p y) (gradient f y)) x+
        c*planeDivergence (fun y ↦ cmcJacobian (p y) (gradient g y)) x := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ cmcJacobian (p y) (gradient f y)) :=
    (cmcJacobian_contDiff.comp hp).clm_apply (plane_gradient_contDiff hf)
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ cmcJacobian (p y) (gradient g y)) :=
    (cmcJacobian_contDiff.comp hp).clm_apply (plane_gradient_contDiff hg)
  have he : (fun y ↦ cmcJacobian (p y) (gradient (fun z ↦ f z+c*g z+d) y))=
      (fun y ↦ cmcJacobian (p y) (gradient f y)+c • cmcJacobian (p y) (gradient g y)) := by
    funext y
    rw [plane_gradient_linear (hf.differentiable (by simp) y)
      (hg.differentiable (by simp) y),map_add,map_smul]
  rw [he,planeDivergence_add (hF.differentiable (by simp) x)
    (show DifferentiableAt ℝ (fun y ↦ c • cmcJacobian (p y) (gradient g y)) x from
      (hG.differentiable (by simp) x).const_smul c),
    planeDivergence_const_smul (hG.differentiable (by simp) x)]

theorem cmc_annulus_barrier {p : Plane → Plane} {f : Plane → ℝ}
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {a : Plane} {R : ℝ} (hR : 0<R)
    (hpb : ∀ y∈Metric.closedBall a R,‖p y‖≤1)
    (hpos : ∀ y∈Metric.ball a R,0<f y)
    (hL : ∀ y∈Metric.ball a R,
      planeDivergence (fun z ↦ cmcJacobian (p z) (gradient f z)) y=0) :
    ∃ k c : ℝ,0<k ∧ 0<c ∧ ∀ y∈Metric.closedBall a R,
      R/2≤‖y-a‖ → c*(planeRadialExp a k y-Real.exp (-k*R^2))≤f y := by
  have hnonneg : ∀ y∈Metric.closedBall a R,0≤f y := by
    have hs : closure (Metric.ball a R)⊆{y | 0≤f y} :=
      (isClosed_le continuous_const hf.continuous).closure_subset_iff.mpr
        (fun y hy ↦ (hpos y hy).le)
    rwa [closure_ball a hR.ne'] at hs
  obtain ⟨c,hc,hcf⟩ := (isCompact_closedBall a (R/2)).exists_forall_le'
    hf.continuous.continuousOn (fun y hy ↦ hpos y (show dist y a<R from
      lt_of_le_of_lt (show dist y a≤R/2 from hy) (by linarith)))
  let F : Plane → Plane := fun z ↦ cmcJacobian (p z) (z-a)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    (cmcJacobian_contDiff.comp hp).clm_apply (contDiff_id.sub contDiff_const)
  obtain ⟨M,hM⟩ := (isCompact_closedBall a R).exists_bound_of_continuousOn
    (sibling_planeDivergence_contDiff hF).continuous.continuousOn
  let k : ℝ := 16*(|M|+1)/R^2
  have hk : 0<k := div_pos (by positivity) (sq_pos_of_pos hR)
  have hkM : 16*M<k*R^2 := by
    have he : k*R^2=16*(|M|+1) := div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hR))
    rw [he]
    linarith [le_abs_self M]
  let q := planeRadialExp a k
  let d := c*Real.exp (-k*R^2)
  let h : Plane → ℝ := fun y ↦ f y+(-c)*q y+d
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := planeRadialExp_contDiff a k
  have hh : ContDiff ℝ (⊤ : ℕ∞) h := (hf.add (contDiff_const.mul hq)).add contDiff_const
  let K := Metric.closedBall a R \ Metric.ball a (R/2)
  let U := Metric.ball a R \ Metric.closedBall a (R/2)
  have hK : IsCompact K := (isCompact_closedBall a R).diff Metric.isOpen_ball
  have hU : IsOpen U := Metric.isOpen_ball.sdiff Metric.isClosed_closedBall
  have hUK : U⊆K := by
    intro y hy
    exact ⟨Metric.ball_subset_closedBall hy.1,fun hh ↦ hy.2 (Metric.ball_subset_closedBall hh)⟩
  have hb : ∀ y∈K,y∉U → 0≤h y := by
    intro y hy hyout
    have hyo : ‖y-a‖≤R := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hy.1
    have hyi : R/2≤‖y-a‖ := by simpa only [Metric.mem_ball,dist_eq_norm,not_lt] using hy.2
    have hcase : ‖y-a‖=R ∨ ‖y-a‖=R/2 := by
      by_contra hn
      push Not at hn
      exact hyout ⟨by simpa only [Metric.mem_ball,dist_eq_norm] using lt_of_le_of_ne hyo hn.1,
        by simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using lt_of_le_of_ne hyi (Ne.symm hn.2)⟩
    rcases hcase with ho|hi
    · have hqe : q y=Real.exp (-k*R^2) := by simp only [q,planeRadialExp,ho]
      have hfy := hnonneg y hy.1
      dsimp only [h,d]
      rw [hqe]
      linarith
    · have hfy := hcf y (by simpa only [Metric.mem_closedBall,dist_eq_norm,hi] using (le_refl (R/2)))
      have hqb : q y≤1 := by
        change Real.exp (-k*‖y-a‖^2)≤1
        exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk.le) (sq_nonneg _))
      have hd : 0≤d := mul_nonneg hc.le (Real.exp_pos _).le
      have hmul := mul_le_mul_of_nonneg_left hqb hc.le
      dsimp only [h]
      nlinarith
  have hstrict : ∀ y∈U,
      planeDivergence (fun z ↦ cmcJacobian (p z) (gradient h z)) y<0 := by
    intro y hy
    have hD : planeDivergence F y≤M := (le_abs_self _).trans (hM y (Metric.ball_subset_closedBall hy.1))
    have hrad := planeRadialExp_cmc_positive hp hR hk hkM
      (show R/2≤‖y-a‖ from le_of_lt (by simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hy.2))
      (hpb y (Metric.ball_subset_closedBall hy.1)) hD
    dsimp only [h]
    rw [cmc_divergence_linear hp hf hq,hL y hy.1,zero_add]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hc) hrad
  have hbound := cmc_strict_minimum_principle hp hh hK hU hUK hb hstrict
  refine ⟨k,c,hk,hc,?_⟩
  intro y hy hyi
  have hh := hbound y ⟨hy,by simpa only [Metric.mem_ball,dist_eq_norm,not_lt] using hyi⟩
  dsimp only [h,d,q] at hh
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_annulus_radial_tangent {a x : Plane} {R : ℝ}
    (hR : 0<R) (hx : ‖x-a‖=R) :
    segment ℝ x (x+(1/2 : ℝ) • (a-x))⊆
      Metric.closedBall a R \ Metric.ball a (R/2) := by
  rw [segment_eq_image']
  rintro y ⟨t,ht,rfl⟩
  have he : x+t • (x+(1/2 : ℝ) • (a-x)-x)-a=(1-t/2) • (x-a) := by module
  have hn : ‖x+t • (x+(1/2 : ℝ) • (a-x)-x)-a‖=(1-t/2)*R := by
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith [ht.2]),hx]
  constructor
  · simp only [Metric.mem_closedBall,dist_eq_norm,hn]
    nlinarith [ht.1]
  · simp only [Metric.mem_ball,dist_eq_norm,hn,not_lt]
    nlinarith [ht.2]

lemma radial_barrier_inward_derivative {f : Plane → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {a x : Plane} {R k c : ℝ}
    (hR : 0<R) (hk : 0<k) (hc : 0<c) (hx : ‖x-a‖=R) (hfx : f x=0)
    (hb : ∀ y∈Metric.closedBall a R,R/2≤‖y-a‖ →
      c*(planeRadialExp a k y-Real.exp (-k*R^2))≤f y) :
    0<fderiv ℝ f x (a-x) := by
  let q := planeRadialExp a k
  let d := c*Real.exp (-k*R^2)
  let h : Plane → ℝ := fun y ↦ f y+(-c)*q y+d
  let K := Metric.closedBall a R \ Metric.ball a (R/2)
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := planeRadialExp_contDiff a k
  have hh : ContDiff ℝ (⊤ : ℕ∞) h := (hf.add (contDiff_const.mul hq)).add contDiff_const
  have hqx : q x=Real.exp (-k*R^2) := by simp only [q,planeRadialExp,hx]
  have hxzero : h x=0 := by dsimp only [h,d]; rw [hfx,hqx]; ring
  have hm : IsMinOn h K x := by
    intro y hy
    rw [hxzero]
    have hby := hb y hy.1 (by simpa only [Metric.mem_ball,dist_eq_norm,not_lt] using hy.2)
    change 0 ≤ f y+(-c)*planeRadialExp a k y+c*Real.exp (-k*R^2)
    linarith only [hby]
  have htan := sub_mem_posTangentConeAt_of_segment_subset (plane_annulus_radial_tangent hR hx)
  have hder := hm.isLocalMinOn.hasFDerivWithinAt_nonneg
    ((hh.differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt) htan
  have hgrad : gradient h x=gradient f x+(-c) • ((-2*k*q x) • (x-a)) := by
    dsimp only [h]
    rw [plane_gradient_linear (hf.differentiable (by simp) x) (hq.differentiable (by simp) x)]
    rw [show gradient q x=(-2*k*q x) • (x-a) from planeRadialExp_gradient a k x]
  have hi : ⟪x-a,a-x⟫= -R^2 := by
    rw [show a-x= -(x-a) by abel,inner_neg_right,real_inner_self_eq_norm_sq,hx]
  rw [← inner_gradient_left,hgrad] at hder
  simp only [add_sub_cancel_left,inner_add_left,real_inner_smul_left,real_inner_smul_right,
    inner_gradient_left,hi,map_smul,smul_eq_mul] at hder
  have hp := mul_pos (mul_pos (mul_pos hc hk) (planeRadialExp_pos a k x)) (sq_pos_of_pos hR)
  change 0<c*k*q x*R^2 at hp
  nlinarith

theorem cmc_hopf_inward_derivative {p : Plane → Plane} {f : Plane → ℝ}
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {a x : Plane} {R : ℝ} (hR : 0<R) (hx : ‖x-a‖=R) (hfx : f x=0)
    (hpb : ∀ y∈Metric.closedBall a R,‖p y‖≤1)
    (hpos : ∀ y∈Metric.ball a R,0<f y)
    (hL : ∀ y∈Metric.ball a R,
      planeDivergence (fun z ↦ cmcJacobian (p z) (gradient f z)) y=0) :
    0<fderiv ℝ f x (a-x) := by
  obtain ⟨k,c,hk,hc,hb⟩ := cmc_annulus_barrier hp hf hR hpb hpos hL
  exact radial_barrier_inward_derivative hf hR hk hc hx hfx hb

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma CenteredJacobiChart.smooth_scalar_ae
    {E : Set Torus} {μ : FiniteMeasure NormalBundle} {N : Cover → Cover}
    (c : CenteredJacobiChart E μ N) (hN : Continuous N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (haeN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (f : smoothPeriodicScalars) :
    (fun y ↦ f.val (c.parameter y))=ᵐ[volume.restrict (Metric.closedBall (0 : Plane) c.r)]
      c.value (surfaceSmoothJet μ f) := by
  have hf := c.scalar_representative_ae hN hp haeN (subset_closure (LinearMap.mem_range_self _ _))
    (continuous_periodic_descent f.property.1.continuous f.property.2).measurable
    (show ∀ᵐ z ∂(μ : Measure NormalBundle),(surfaceSmoothJet μ f).1 z=
      f.val (representative (normalProjection z)) from by
      filter_upwards [(smoothScalarValue f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)] with z hz
      change (surfaceSmoothJet μ f).1 z=f.val z.1 at hz
      rw [hz]
      exact (periodic_representative f.property.2 z.1).symm)
  simpa only [periodic_representative f.property.2] using hf

theorem CenteredJacobiChart.classical_ground_state
    {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (haeN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (c : CenteredJacobiChart E μ N)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (f : smoothPeriodicScalars)
    (hjf : ∀ v∈surfaceH1 μ,surfaceJacobiB μ q (surfaceSmoothJet μ f) v=0)
    (hjw : ∀ v∈surfaceH1 μ,surfaceJacobiB μ q
      (surfaceSmoothJet μ (directionalNormalScalar N hN hp c.n)) v=0) :
    ∀ y∈Metric.ball (0 : Plane) (c.r/2),
      planeDivergence (fun z ↦ cmcJacobian (gradient c.g z)
        (gradient (fun w ↦ c.weight w*f.val (c.parameter w)) z)) y=0 := by
  let F : Plane → ℝ := fun y ↦ c.weight y*f.val (c.parameter y)
  let u := surfaceSmoothJet μ f
  have hu : u∈surfaceH1 μ := subset_closure (LinearMap.mem_range_self _ _)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := c.weight_smooth.mul (f.property.1.comp c.parameter_smooth)
  obtain ⟨huL,hGL,hw⟩ := c.weighted_weak_gradient hN.continuous hp haeN hu
  have he := (ae_restrict_iff' measurableSet_closedBall).mp (c.smooth_scalar_ae hN.continuous hp haeN f)
  have hFe : F=ᵐ[volume.restrict (Metric.ball (0 : Plane) (c.r/2))] c.weightedValue u := by
    apply (ae_restrict_iff' measurableSet_ball).mpr
    filter_upwards [he] with y hy hys
    have hD : y∈Metric.closedBall (0 : Plane) c.r :=
      Metric.ball_subset_closedBall (Metric.ball_subset_ball (by linarith [c.r_pos]) hys)
    simp only [F,CenteredJacobiChart.weightedValue,Set.indicator_of_mem hD,hy hD,u]
  have hW : PlaneWeakGradient (Metric.ball (0 : Plane) (c.r/2)) F (c.weightedGradient u) :=
    hw.local_congr measurableSet_ball hFe EventuallyEq.rfl
  have hGe := PlaneWeakGradient.unique Metric.isOpen_ball (hGL.locallyIntegrable (by norm_num))
    (plane_gradient_contDiff hF).continuous.locallyIntegrable hW
    (C1_weak_gradient (hF.of_le (by simp)) _)
  apply LinearCMCEquation.classical_zero c.smooth hF Metric.isOpen_ball
  intro ψ hψ hc hs
  have hd := c.weighted_divergence hE hμ hN hp haeN q hu hjf hjw hψ hc hs
  simp only [sub_zero]
  rw [← hd]
  apply integral_congr_ae
  have hGe' := (ae_restrict_iff' measurableSet_ball).mp hGe
  filter_upwards [hGe'] with y hy
  by_cases hys : y∈Metric.ball (0 : Plane) (c.r/2)
  · rw [hy hys]
  · rw [fderiv_of_notMem_tsupport ℝ (fun ht ↦ hys (hs ht))]
    rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma positiveNodalPiece_subset (f : smoothPeriodicScalars) {S D : Set Torus}
    (hD : IsPositiveNodalPiece f S D) : D⊆S := by
  intro a ha
  rw [hD.1.choose_spec.2] at ha
  exact ha.1.1

lemma positiveNodalPiece_boundary_zero (f : smoothPeriodicScalars) {S D : Set Torus}
    (hS : IsClosed S) (hD : IsPositiveNodalPiece f S D) {a : Torus}
    (ha : a∈closure D) (haD : a∉D) : f.val (representative a)=0 := by
  have hf := continuous_periodic_descent f.property.1.continuous f.property.2
  have hpos : closure D⊆{b | 0≤f.val (representative b)} :=
    (isClosed_le continuous_const hf).closure_subset_iff.mpr (by
      intro b hb
      rw [hD.1.choose_spec.2] at hb
      exact hb.1.2.le)
  obtain ⟨C,hC,hDC⟩ := hD.2
  have hsub : closure D⊆C := hC.closure_subset_iff.mpr (by
    intro b hb
    rw [hDC] at hb
    exact hb.2)
  have haS : a∈S := hS.closure_subset_iff.mpr (positiveNodalPiece_subset f hD) ha
  apply le_antisymm _ (hpos ha)
  by_contra hh
  exact haD (by rw [hDC]; exact ⟨⟨haS,lt_of_not_ge hh⟩,hsub ha⟩)

lemma positiveNodalPiece_boundary_nonempty (f : smoothPeriodicScalars) {S D : Set Torus}
    (hS : IsPreconnected S) (hD : IsPositiveNodalPiece f S D)
    (hDn : D.Nonempty) (hother : (S\D).Nonempty) : (closure D\D).Nonempty := by
  by_contra hh
  have hclosed : IsClosed D := isClosed_of_closure_subset (by
    intro a ha
    by_contra hn
    exact hh ⟨a,ha,hn⟩)
  obtain ⟨U,hU,hDU,_⟩ := positiveNodalPiece_open_patch f S D hD hDn
  obtain ⟨a,ha⟩ := hDn
  obtain ⟨b,hbS,hbD⟩ := hother
  have hab := hS U Dᶜ hU hclosed.isOpen_compl (by
      intro x hx
      by_cases hxD : x∈D
      · left; have h := hxD; rw [← hDU] at h; exact h.1
      · exact Or.inr hxD)
    ⟨a,positiveNodalPiece_subset f hD ha,(by rw [← hDU] at ha; exact ha.1)⟩ ⟨b,hbS,hbD⟩
  obtain ⟨x,hxS,hxU,hxD⟩ := hab
  exact hxD (by rw [← hDU]; exact ⟨hxU,hxS⟩)

lemma CenteredJacobiChart.parameter_zero
    {E : Set Torus} {μ : FiniteMeasure NormalBundle} {N : Cover → Cover}
    (c : CenteredJacobiChart E μ N) : c.parameter 0=cubeCenter := by
  simp only [CenteredJacobiChart.parameter,normalGraph,c.zero,zero_smul,add_zero]
  change cubeCenter+(normalPlaneLinearIsometry c.n) 0=cubeCenter
  rw [map_zero,add_zero]

lemma CenteredJacobiChart.closure_pullback
    {E : Set Torus} {μ : FiniteMeasure NormalBundle} {N : Cover → Cover}
    (c : CenteredJacobiChart E μ N) {D : Set Torus}
    (hD : D⊆frontier (openRepresentative E))
    (hcl : quotientMap cubeCenter∈closure D) {r : ℝ} (hr : 0<r) :
    (0 : Plane)∈closure (Metric.ball (0 : Plane) r∩
      (fun y ↦ quotientMap (c.parameter y)) ⁻¹' D) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp c.cover_germ
  let t := min δ (min r ε)
  have ht : 0<t := lt_min hδ (lt_min hr hε)
  obtain ⟨b,hbD,hb⟩ := Metric.mem_closure_iff.mp hcl t ht
  have hbball : b∈Metric.ball (quotientMap cubeCenter) t := by
    simpa only [Metric.mem_ball,dist_comm] using hb
  rw [← quotientMap_image_ball cubeCenter t] at hbball
  obtain ⟨z,hz,hzb⟩ := hbball
  let v := z-cubeCenter
  have hv : ‖v‖<t := by simpa only [Metric.mem_ball,dist_eq_norm] using hz
  have hvδ : v∈Metric.ball (0 : Cover) δ := by
    simpa only [Metric.mem_ball,dist_zero_right] using hv.trans_le (min_le_left _ _)
  have hsurf : quotientMap (cubeCenter+v)∈frontier (openRepresentative E) := by
    simpa only [v,add_sub_cancel,hzb] using hD hbD
  have he := (hδsub hvδ).mp hsurf
  let y := normalPlaneCoordinates c.n v
  have hy : ‖y‖<t := (normalPlaneCoordinates_norm_le _ _).trans_lt hv
  refine ⟨y,⟨?_,?_⟩,?_⟩
  · simpa only [Metric.mem_ball,dist_zero_right] using
      hy.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  · change quotientMap (cubeCenter+normalGraph c.n c.g y)∈D
    rw [he]
    simpa only [v,add_sub_cancel,hzb] using hbD
  · simpa only [dist_zero_left] using hy.trans_le ((min_le_right _ _).trans (min_le_right _ _))

lemma CenteredJacobiChart.positive_piece_pullback_open
    {E : Set Torus} {μ : FiniteMeasure NormalBundle} {N : Cover → Cover}
    (c : CenteredJacobiChart E μ N) (f : smoothPeriodicScalars) {D : Set Torus}
    (hD : IsPositiveNodalPiece f (frontier (openRepresentative E)) D) :
    IsOpen (Metric.ball (0 : Plane) c.r∩(fun y ↦ quotientMap (c.parameter y)) ⁻¹' D) := by
  obtain ⟨U,hU,hDU⟩ := hD.1
  have he : Metric.ball (0 : Plane) c.r∩(fun y ↦ quotientMap (c.parameter y)) ⁻¹' D=
      Metric.ball (0 : Plane) c.r∩{y | 0<f.val (c.parameter y)}∩
        (fun y ↦ quotientMap (c.parameter y)) ⁻¹' U := by
    ext y
    simp only [mem_inter_iff,mem_preimage,hDU,mem_ofPred_eq,periodic_representative f.property.2]
    constructor
    · rintro ⟨hy,⟨_,hp⟩,hU⟩; exact ⟨⟨hy,hp⟩,hU⟩
    · rintro ⟨⟨hy,hp⟩,hU⟩
      exact ⟨hy,⟨c.boundary_disk y (Metric.ball_subset_closedBall hy),hp⟩,hU⟩
  rw [he]
  exact (Metric.isOpen_ball.inter (isOpen_lt continuous_const
    (f.property.1.continuous.comp c.parameter_smooth.continuous))).inter
      (hU.preimage (continuous_quotientMap.comp c.parameter_smooth.continuous))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def sibling_planeElliptic (A : Plane → Plane →L[ℝ] Plane) (f : Plane → ℝ) : Plane → ℝ :=
  planeDivergence (fun y ↦ A y (gradient f y))

lemma sibling_planeElliptic_contDiff {A : Plane → Plane →L[ℝ] Plane} {f : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (sibling_planeElliptic A f) :=
  sibling_planeDivergence_contDiff (hA.clm_apply (plane_gradient_contDiff hf))

lemma compact_inner_left {b p : Plane → Plane} (hc : HasCompactSupport p) :
    HasCompactSupport (fun y ↦ ⟪p y,b y⟫) := by
  apply hc.mono
  intro y hy
  contrapose! hy
  simp only [Function.mem_support,not_not] at hy ⊢
  rw [hy,inner_zero_left]

lemma compact_inner_right {b p : Plane → Plane} (hc : HasCompactSupport p) :
    HasCompactSupport (fun y ↦ ⟪b y,p y⟫) := by
  simpa only [real_inner_comm] using compact_inner_left (b := b) hc

lemma compact_clm_apply {A : Plane → Plane →L[ℝ] Plane} {p : Plane → Plane}
    (hc : HasCompactSupport p) : HasCompactSupport (fun y ↦ A y (p y)) := by
  apply hc.mono
  intro y hy
  contrapose! hy
  simp only [Function.mem_support,not_not] at hy ⊢
  rw [hy,map_zero]

lemma sibling_planeDivergence_compact {F : Plane → Plane} (hc : HasCompactSupport F) :
    HasCompactSupport (planeDivergence F) := by
  have h0 : HasCompactSupport (fun y ↦ (fderiv ℝ F y (EuclideanSpace.single 0 1)) 0) :=
    (hc.fderiv_apply ℝ _).comp_left (g := fun v : Plane ↦ v 0) (by simp)
  have h1 : HasCompactSupport (fun y ↦ (fderiv ℝ F y (EuclideanSpace.single 1 1)) 1) :=
    (hc.fderiv_apply ℝ _).comp_left (g := fun v : Plane ↦ v 1) (by simp)
  exact h0.add h1

lemma sibling_planeElliptic_compact {A : Plane → Plane →L[ℝ] Plane} {f : Plane → ℝ}
    (hc : HasCompactSupport f) : HasCompactSupport (sibling_planeElliptic A f) :=
  sibling_planeDivergence_compact (compact_clm_apply (plane_gradient_compact hc))

lemma planeElliptic_ibp {A : Plane → Plane →L[ℝ] Plane} {f g : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) :
    (∫ y,sibling_planeElliptic A f y*g y)= -(∫ y,⟪gradient g y,A y (gradient f y)⟫) := by
  simpa only [sibling_planeElliptic,inner_gradient_left] using
    plane_divergence_integration_by_parts
      ((hA.clm_apply (plane_gradient_contDiff hf)).of_le (by simp))
      (hg.of_le (by simp)) hc

lemma plane_inner_fderiv {p q : Plane → Plane} {y v : Plane}
    (hp : DifferentiableAt ℝ p y) (hq : DifferentiableAt ℝ q y) :
    fderiv ℝ (fun z ↦ ⟪p z,q z⟫) y v=
      ⟪fderiv ℝ p y v,q y⟫+⟪p y,fderiv ℝ q y v⟫ := by
  rw [(hp.hasFDerivAt.inner ℝ hq.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.comp_apply, fderivInnerCLM_apply, ContinuousLinearMap.prod_apply]
  exact add_comm _ _

lemma plane_clm_fderiv {A : Plane → Plane →L[ℝ] Plane} {p : Plane → Plane}
    {y v : Plane} (hA : DifferentiableAt ℝ A y) (hp : DifferentiableAt ℝ p y) :
    fderiv ℝ (fun z ↦ A z (p z)) y v=(fderiv ℝ A y v) (p y)+A y (fderiv ℝ p y v) := by
  rw [(hA.hasFDerivAt.clm_apply hp.hasFDerivAt).fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  exact add_comm _ _

lemma plane_energy_fderiv {A : Plane → Plane →L[ℝ] Plane} {f : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫) (y v : Plane) :
    fderiv ℝ (fun z ↦ ⟪gradient f z,A z (gradient f z)⟫) y v=
      2*⟪A y (gradient f y),fderiv ℝ (gradient f) y v⟫+
        ⟪gradient f y,(fderiv ℝ A y v) (gradient f y)⟫ := by
  have hp := (plane_gradient_contDiff hf).differentiable (by simp) y
  rw [plane_inner_fderiv hp ((hA.differentiable (by simp) y).clm_apply hp),
    plane_clm_fderiv (hA.differentiable (by simp) y) hp,inner_add_right,
    hAs y (gradient f y) (fderiv ℝ (gradient f) y v)]
  rw [real_inner_comm (A y (gradient f y))]
  ring

lemma plane_transport_gradient {b : Plane → Plane} {f : Plane → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (y q : Plane) :
    ⟪gradient (fun z ↦ ⟪b z,gradient f z⟫) y,q⟫=
      ⟪gradient f y,fderiv ℝ b y q⟫+
        ⟪q,fderiv ℝ (gradient f) y (b y)⟫ := by
  rw [inner_gradient_left,plane_inner_fderiv (hb.differentiable (by simp) y)
    ((plane_gradient_contDiff hf).differentiable (by simp) y),
    real_inner_comm (fderiv ℝ b y q),← plane_hessian_symmetric hf,
    real_inner_comm (fderiv ℝ (gradient f) y (b y))]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeTransport (b : Plane → Plane) (f : Plane → ℝ) (y : Plane) : ℝ :=
  2*⟪b y,gradient f y⟫+planeDivergence b y*f y

lemma planeTransport_contDiff {b : Plane → Plane} {f : Plane → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (planeTransport b f) :=
  (contDiff_const.mul (hb.inner ℝ (plane_gradient_contDiff hf))).add
    ((sibling_planeDivergence_contDiff hb).mul hf)

lemma planeTransport_compact {b : Plane → Plane} {f : Plane → ℝ}
    (hc : HasCompactSupport f) : HasCompactSupport (planeTransport b f) :=
  (compact_inner_right (plane_gradient_compact hc)).mul_left.add hc.mul_left

end CubicTorus
end
end
end

end OAI
