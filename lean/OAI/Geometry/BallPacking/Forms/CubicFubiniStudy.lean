import Mathlib
import OAI.Geometry.BallPacking.Surfaces.QuadricAnnulusDomain
import OAI.Geometry.BallPacking.Forms.ManifoldMapDifferential

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian

 def planeAffine : PlaneBase →L[ℂ] Affine 1 :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).prod
    (ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.snd ℂ ℂ ℂ)

 theorem planeAffine_injective : Injective planeAffine := by
  intro z w h
  exact Prod.ext (congrArg (fun q : Affine 1 => q.1) h)
    (congrArg (fun q : Affine 1 => q.2 0) h)

 def projectiveInclusion (x : BaseCurve) : Affine 1 := planeAffine (inclusion x)
 def phaseInclusion (x : BaseCurve) : PlanePhase (Option (Fin 1)) :=
  affinePhase 1 (projectiveInclusion x)

 theorem phaseInclusion_smooth :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,PlanePhase (Option (Fin 1))) ∞ phaseInclusion :=
  (affinePhase 1).contDiff.contMDiff.comp
    ((planeAffine.restrictScalars ℝ).contDiff.contMDiff.comp
      ((projection_contDiff.restrict_scalars ℝ).contMDiff.comp
        (real_inclusion_contMDiff (parameters 0))))

 def curveFSPrimitive (c : ℝ) : ManifoldOneForm RealModel BaseCurve :=
  manifoldPullbackOneForm (fun _ => affineFSPrimitive c) phaseInclusion 0
 def curveFSForm (c : ℝ) : ManifoldTwoForm RealModel BaseCurve :=
  manifoldPullbackTwoForm (fun _ => affineFSForm c) phaseInclusion 0

 theorem curveFSPrimitive_smooth (c : ℝ) :
    SmoothOneFormFamily (fun _ : ℝ => curveFSPrimitive c) := by
  have hα : SmoothOneFormFamily (fun _ : ℝ =>
      (affineFSPrimitive c : PlanePhase (Option (Fin 1)) → _)) :=
    vector_oneForm_smooth (affineFSPrimitive_smooth c)
  intro b
  exact manifoldPullbackOneForm_smooth (α := fun _ : ℝ =>
    (affineFSPrimitive c : PlanePhase (Option (Fin 1)) → _)) phaseInclusion_smooth hα b

 theorem curveFSForm_smooth (c : ℝ) : SmoothTwoForm (curveFSForm c) := by
  have hΩ : SmoothTwoForm (affineFSForm c : PlanePhase (Option (Fin 1)) → _) :=
    vector_twoForm_smooth (affineFSForm_smooth c)
  have hΩf : SmoothTwoFormFamily (fun _ : ℝ =>
      (affineFSForm c : PlanePhase (Option (Fin 1)) → _)) := SmoothTwoFormFamily.const hΩ
  have hs : SmoothTwoFormFamily (fun t : ℝ =>
      manifoldPullbackTwoForm (fun _ => (affineFSForm c : PlanePhase (Option (Fin 1)) → _))
        phaseInclusion t) :=
    manifoldPullbackTwoForm_smooth (Ω := fun _ =>
      (affineFSForm c : PlanePhase (Option (Fin 1)) → _)) phaseInclusion_smooth hΩf
  exact hs.eval 0

 theorem curveFSPrimitive_exterior (c : ℝ) :
    manifoldExteriorOneForm (curveFSPrimitive c)=curveFSForm c := by
  have hα : ∀ z : PlanePhase (Option (Fin 1)),ContDiffOn ℝ ∞
      (chartOneForm (affineFSPrimitive c) z) (extChartAt 𝓘(ℝ,PlanePhase (Option (Fin 1))) z).target := by
    intro z
    rw [show chartOneForm (affineFSPrimitive c) z=affineFSPrimitive c from
      funext (vector_chartOneForm (affineFSPrimitive c) z)]
    exact (affineFSPrimitive_smooth c).contDiffOn
  funext x
  change manifoldExteriorOneForm (manifoldPullbackOneForm
    (fun _ => (affineFSPrimitive c : PlanePhase (Option (Fin 1)) → _)) phaseInclusion 0) x=_
  rw [manifold_pullback_exterior hα phaseInclusion_smooth x]
  rw [vector_exteriorOneForm,← affineFSForm_eq_exterior]
  rfl

 theorem curveFSForm_skew (c : ℝ) (x : BaseCurve) (v w : RealModel) :
    curveFSForm c x v w= -curveFSForm c x w v := affineFSForm_skew c _ _ _

 def cubicChart (b : BaseCurve) : ℂ → Affine 1 :=
  planeAffine ∘ projection ∘ (normalChartAt (parameters 0) b).inclusionChart b

 theorem cubicChart_smooth (b : BaseCurve) : ContDiffOn ℂ ∞ (cubicChart b)
    ((normalChartAt (parameters 0) b).sliceChart b).target :=
  planeAffine.contDiff.comp_contDiffOn (projection_contDiff.comp_contDiffOn
    ((normalChartAt (parameters 0) b).inclusionChart_smooth b))

 theorem cubicChart_derivative_one_ne (b : BaseCurve) {y : ℂ}
    (hy : y∈((normalChartAt (parameters 0) b).sliceChart b).target) :
    fderiv ℂ (cubicChart b) y 1≠0 := by
  let e := normalChartAt (parameters 0) b
  let f := e.inclusionChart b
  have hf : DifferentiableAt ℂ f y :=
    ((e.inclusionChart_smooth b).contDiffAt ((e.sliceChart b).open_target.mem_nhds hy)).differentiableAt (by simp)
  have hp : DifferentiableAt ℂ (projection ∘ f) y := (projection_contDiff.differentiable (by simp) (f y)).comp y hf
  have hne : (projection (f y)).1≠0 := inclusion_fst_ne_zero ((e.sliceChart b).symm y)
  have hr : DifferentiableAt ℂ recovery (projection (f y)) :=
    (recovery_contDiffOn.contDiffAt ((isOpen_ne_fun continuous_fst continuous_const).mem_nhds hne)).differentiableAt (by simp)
  have heq : recovery ∘ (projection ∘ f)=f := by
    funext z
    exact recovery_inclusion ((e.sliceChart b).symm z)
  have hd : (fderiv ℂ recovery (projection (f y))).comp (fderiv ℂ (projection ∘ f) y)=fderiv ℂ f y := by
    calc
      _=fderiv ℂ (recovery ∘ (projection ∘ f)) y := by
        simpa only [Function.comp_apply] using (fderiv_comp y hr hp).symm
      _=_ := congrArg (fun g => fderiv ℂ g y) heq
  intro hz
  have hz' : planeAffine (fderiv ℂ (projection ∘ f) y 1)=0 := by
    change (fderiv ℂ (planeAffine ∘ (projection ∘ f)) y) 1=0 at hz
    rw [fderiv_comp y planeAffine.differentiableAt hp,ContinuousLinearMap.fderiv] at hz
    exact hz
  have hp0 : fderiv ℂ (projection ∘ f) y 1=0 :=
    planeAffine_injective (by simpa only [map_zero] using hz')
  apply e.inclusionChart_derivative_one_ne b hy
  have hx := congrArg (fun L : ℂ→L[ℂ] Affine 2 => L 1) hd
  simpa only [ContinuousLinearMap.comp_apply,hp0,map_zero] using hx.symm

 theorem phase_chart_function (b : BaseCurve) :
    (phaseInclusion ∘ (extChartAt 𝓘(ℝ,RealModel) b).symm)=
      affinePhase 1 ∘ cubicChart b ∘ Complex.equivRealProdCLM.symm := by
  funext y
  have he : chartAt RealModel b=realChart (parameters 0) b := rfl
  simp only [mfld_simps,he,realChart,Function.comp_apply,phaseInclusion,
    projectiveInclusion,cubicChart,inclusion,NormalChart.inclusionChart]
  rfl

 theorem phase_chart_derivative (b : BaseCurve) {y : RealModel}
    (hy : y∈(extChartAt 𝓘(ℝ,RealModel) b).target) :
    manifoldMapDifferential (E := PlanePhase (Option (Fin 1))) (F := RealModel)
      (phaseInclusion ∘ (extChartAt 𝓘(ℝ,RealModel) b).symm) y=
    realPhaseDerivative (fderiv ℂ (cubicChart b) (Complex.equivRealProdCLM.symm y)) := by
  change mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,PlanePhase (Option (Fin 1))) _ y=_
  rw [mfderiv_eq_fderiv,phase_chart_function]
  have hdf := ((cubicChart_smooth b).contDiffAt
    (((normalChartAt (parameters 0) b).sliceChart b).open_target.mem_nhds
      (realChart_complex_target (parameters 0) b hy))).differentiableAt (by simp)
  exact ((affinePhase 1).hasFDerivAt.comp y
    ((hdf.hasFDerivAt.restrictScalars ℝ).comp y Complex.equivRealProdCLM.symm.hasFDerivAt)).fderiv

 theorem curveFSForm_positive {c : ℝ} (hc : 0<c) (b : BaseCurve) {y : RealModel}
    (hy : y∈(extChartAt 𝓘(ℝ,RealModel) b).target) :
    0<chartTwoForm (curveFSForm c) b y (1,0) (0,1) := by
  rw [curveFSForm,chartTwoForm_manifoldPullback phaseInclusion_smooth (p := (0,y)) hy]
  change 0<affineFSForm c _
    (manifoldMapDifferential (E := PlanePhase (Option (Fin 1))) (F := RealModel)
      (phaseInclusion ∘ (extChartAt 𝓘(ℝ,RealModel) b).symm) y (1,0))
    (manifoldMapDifferential (E := PlanePhase (Option (Fin 1))) (F := RealModel)
      (phaseInclusion ∘ (extChartAt 𝓘(ℝ,RealModel) b).symm) y (0,1))
  rw [phase_chart_derivative b hy]
  apply affineFSForm_holomorphic_positive hc
  exact cubicChart_derivative_one_ne b (realChart_complex_target (parameters 0) b hy)

def weightedProjection (D m : ℕ) (z : PlaneBase) : Affine 3 :=
  (z.1^(D-m),![z.2^(D-m),z.1^(D-m)*z.2^m,z.1^m*z.2^(D-m)])

def weightedHomogeneous (D m : ℕ) (u v w : ℂ) : Fin 5 → ℂ :=
  ![u^D,u^m*v^(D-m),u^m*w^(D-m),v^(D-m)*w^m,v^m*w^(D-m)]

 theorem weightedProjection_contDiff (D m : ℕ) : ContDiff ℂ ∞ (weightedProjection D m) := by
  apply ContDiff.prodMk (contDiff_fst.pow (D-m))
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · exact contDiff_snd.pow (D-m)
  · exact (contDiff_fst.pow (D-m)).mul (contDiff_snd.pow m)
  · exact (contDiff_fst.pow m).mul (contDiff_snd.pow (D-m))

 theorem weightedHomogeneous_homogeneous (D m : ℕ) (hm : m≤D) (ζ u v w : ℂ) :
    weightedHomogeneous D m (ζ*u) (ζ*v) (ζ*w)=ζ^D • weightedHomogeneous D m u v w := by
  have hD : m+(D-m)=D := Nat.add_sub_of_le hm
  have hD' : (D-m)+m=D := Nat.sub_add_cancel hm
  funext j
  fin_cases j
  · change (ζ*u)^D=ζ^D*u^D
    exact mul_pow ζ u D
  · change (ζ*u)^m*(ζ*v)^(D-m)=ζ^D*(u^m*v^(D-m))
    calc
      _=(ζ^m*ζ^(D-m))*(u^m*v^(D-m)) := by simp only [mul_pow]; ring
      _=_ := by rw [←pow_add,hD]
  · change (ζ*u)^m*(ζ*w)^(D-m)=ζ^D*(u^m*w^(D-m))
    calc
      _=(ζ^m*ζ^(D-m))*(u^m*w^(D-m)) := by simp only [mul_pow]; ring
      _=_ := by rw [←pow_add,hD]
  · change (ζ*v)^(D-m)*(ζ*w)^m=ζ^D*(v^(D-m)*w^m)
    calc
      _=(ζ^(D-m)*ζ^m)*(v^(D-m)*w^m) := by simp only [mul_pow]; ring
      _=_ := by rw [←pow_add,hD']
  · change (ζ*v)^m*(ζ*w)^(D-m)=ζ^D*(v^m*w^(D-m))
    calc
      _=(ζ^m*ζ^(D-m))*(v^m*w^(D-m)) := by simp only [mul_pow]; ring
      _=_ := by rw [←pow_add,hD]

 theorem weightedProjection_fderiv_fst (D m : ℕ) (z v : PlaneBase) :
    (fderiv ℂ (weightedProjection D m) z v).1=(D-m:ℕ)*z.1^(D-m-1)*v.1 := by
  have h := ((hasFDerivAt_fst (𝕜 := ℂ) (p := z)).pow (D-m))
  have hc := (ContinuousLinearMap.fst ℂ ℂ (Fin 3→ℂ)).hasFDerivAt.comp z
    ((weightedProjection_contDiff D m).differentiable (by simp) z).hasFDerivAt
  have he : (ContinuousLinearMap.fst ℂ ℂ (Fin 3→ℂ)) ∘ weightedProjection D m=
      fun z : PlaneBase => z.1^(D-m) := rfl
  rw [he] at hc
  have hd := hc.unique h
  have hh := congrArg (fun A : PlaneBase→L[ℂ] ℂ => A v) hd
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',
    smul_apply,nsmul_eq_mul,smul_eq_mul] using hh

 theorem weightedProjection_fderiv_snd (D m : ℕ) (z v : PlaneBase) :
    (fderiv ℂ (weightedProjection D m) z v).2 0=(D-m:ℕ)*z.2^(D-m-1)*v.2 := by
  let P : Affine 3→L[ℂ] ℂ := (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.snd ℂ ℂ (Fin 3→ℂ))
  have h := ((hasFDerivAt_snd (𝕜 := ℂ) (p := z)).pow (D-m))
  have hc := P.hasFDerivAt.comp z
    ((weightedProjection_contDiff D m).differentiable (by simp) z).hasFDerivAt
  have he : P ∘ weightedProjection D m=fun z : PlaneBase => z.2^(D-m) := rfl
  rw [he] at hc
  have hd := hc.unique h
  have hh := congrArg (fun A : PlaneBase→L[ℂ] ℂ => A v) hd
  simpa only [P,ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.proj_apply,smul_apply,nsmul_eq_mul,smul_eq_mul] using hh

 theorem weightedProjection_fderiv_kernel {D m : ℕ} (hm : m<D) {z : PlaneBase}
    (hzv : z.1≠0) (hzw : z.2≠0) {v : PlaneBase}
    (hv : fderiv ℂ (weightedProjection D m) z v=0) : v=0 := by
  have hL : (D-m:ℕ)≠0 := (Nat.sub_pos_of_lt hm).ne'
  have hLc : ((D-m:ℕ):ℂ)≠0 := by exact_mod_cast hL
  have hv0 := weightedProjection_fderiv_fst D m z v
  have hw0 := weightedProjection_fderiv_snd D m z v
  rw [hv] at hv0 hw0
  apply Prod.ext
  · exact (mul_eq_zero.mp hv0.symm).resolve_left (mul_ne_zero hLc (pow_ne_zero _ hzv))
  · exact (mul_eq_zero.mp hw0.symm).resolve_left (mul_ne_zero hLc (pow_ne_zero _ hzw))

 def weightedInclusion (D m : ℕ) (x : BaseCurve) : Affine 3 :=
  weightedProjection D m (inclusion x)

 theorem weightedInclusion_smooth (D m : ℕ) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,Affine 3) ∞ (weightedInclusion D m) :=
  (weightedProjection_contDiff D m).contMDiff.comp inclusion_contMDiff

 def weightedChart (D m : ℕ) (b : BaseCurve) : ℂ → Affine 3 :=
  weightedProjection D m ∘ projection ∘ (normalChartAt (parameters 0) b).inclusionChart b

 theorem weightedChart_smooth (D m : ℕ) (b : BaseCurve) :
    ContDiffOn ℂ ∞ (weightedChart D m b) ((normalChartAt (parameters 0) b).sliceChart b).target :=
  (weightedProjection_contDiff D m).comp_contDiffOn
    (projection_contDiff.comp_contDiffOn ((normalChartAt (parameters 0) b).inclusionChart_smooth b))

 theorem weightedChart_derivative_one_ne {D m : ℕ} (hm : m<D) (b : BaseCurve) {y : ℂ}
    (hy : y∈((normalChartAt (parameters 0) b).sliceChart b).target) :
    fderiv ℂ (weightedChart D m b) y 1≠0 := by
  let e := normalChartAt (parameters 0) b
  let f := projection ∘ e.inclusionChart b
  have hf : DifferentiableAt ℂ f y :=
    ((projection_contDiff.comp_contDiffOn (e.inclusionChart_smooth b)).contDiffAt
      ((e.sliceChart b).open_target.mem_nhds hy)).differentiableAt (by simp)
  intro hz
  change fderiv ℂ (weightedProjection D m ∘ f) y 1=0 at hz
  rw [fderiv_comp y ((weightedProjection_contDiff D m).differentiable (by simp) _) hf] at hz
  have hz' : fderiv ℂ f y 1=0 := weightedProjection_fderiv_kernel hm
    (inclusion_fst_ne_zero ((e.sliceChart b).symm y))
    (inclusion_snd_ne_zero ((e.sliceChart b).symm y)) hz
  apply cubicChart_derivative_one_ne b hy
  change fderiv ℂ (planeAffine ∘ f) y 1=0
  rw [fderiv_comp y planeAffine.differentiableAt hf,ContinuousLinearMap.fderiv,
    ContinuousLinearMap.comp_apply,hz',map_zero]

 def weightedPhaseInclusion (D m : ℕ) (x : BaseCurve) : PlanePhase (Option (Fin 3)) :=
  affinePhase 3 (weightedInclusion D m x)

 theorem weightedPhaseInclusion_smooth (D m : ℕ) :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,PlanePhase (Option (Fin 3))) ∞ (weightedPhaseInclusion D m) :=
  (affinePhase 3).contDiff.contMDiff.comp
    (((weightedProjection_contDiff D m).restrict_scalars ℝ).contMDiff.comp
      ((projection_contDiff.restrict_scalars ℝ).contMDiff.comp
        (real_inclusion_contMDiff (parameters 0))))

 def weightedFSPrimitive (D m : ℕ) (c : ℝ) : ManifoldOneForm RealModel BaseCurve :=
  manifoldPullbackOneForm (fun _ => affineFSPrimitive c) (weightedPhaseInclusion D m) 0
 def weightedFSForm (D m : ℕ) (c : ℝ) : ManifoldTwoForm RealModel BaseCurve :=
  manifoldPullbackTwoForm (fun _ => affineFSForm c) (weightedPhaseInclusion D m) 0

 theorem weightedFSPrimitive_smooth (D m : ℕ) (c : ℝ) :
    SmoothOneFormFamily (fun _ : ℝ => weightedFSPrimitive D m c) := by
  have hα : SmoothOneFormFamily (fun _ : ℝ =>
      (affineFSPrimitive c : PlanePhase (Option (Fin 3)) → _)) :=
    vector_oneForm_smooth (affineFSPrimitive_smooth c)
  intro b
  exact manifoldPullbackOneForm_smooth (α := fun _ : ℝ =>
    (affineFSPrimitive c : PlanePhase (Option (Fin 3)) → _)) (weightedPhaseInclusion_smooth D m) hα b

 theorem weightedFSForm_smooth (D m : ℕ) (c : ℝ) : SmoothTwoForm (weightedFSForm D m c) := by
  have hΩ : SmoothTwoForm (affineFSForm c : PlanePhase (Option (Fin 3)) → _) :=
    vector_twoForm_smooth (affineFSForm_smooth c)
  have hΩf : SmoothTwoFormFamily (fun _ : ℝ =>
      (affineFSForm c : PlanePhase (Option (Fin 3)) → _)) := SmoothTwoFormFamily.const hΩ
  have hs : SmoothTwoFormFamily (fun t : ℝ =>
      manifoldPullbackTwoForm (fun _ => (affineFSForm c : PlanePhase (Option (Fin 3)) → _))
        (weightedPhaseInclusion D m) t) :=
    manifoldPullbackTwoForm_smooth (Ω := fun _ =>
      (affineFSForm c : PlanePhase (Option (Fin 3)) → _)) (weightedPhaseInclusion_smooth D m) hΩf
  exact hs.eval 0

 theorem weightedFSPrimitive_exterior (D m : ℕ) (c : ℝ) :
    manifoldExteriorOneForm (weightedFSPrimitive D m c)=weightedFSForm D m c := by
  have hα : ∀ z : PlanePhase (Option (Fin 3)),ContDiffOn ℝ ∞
      (chartOneForm (affineFSPrimitive c) z) (extChartAt 𝓘(ℝ,PlanePhase (Option (Fin 3))) z).target := by
    intro z
    rw [show chartOneForm (affineFSPrimitive c) z=affineFSPrimitive c from
      funext (vector_chartOneForm (affineFSPrimitive c) z)]
    exact (affineFSPrimitive_smooth c).contDiffOn
  funext x
  change manifoldExteriorOneForm (manifoldPullbackOneForm
    (fun _ => (affineFSPrimitive c : PlanePhase (Option (Fin 3)) → _)) (weightedPhaseInclusion D m) 0) x=_
  rw [manifold_pullback_exterior hα (weightedPhaseInclusion_smooth D m) x]
  rw [vector_exteriorOneForm,← affineFSForm_eq_exterior]
  rfl

 theorem weightedFSForm_skew (D m : ℕ) (c : ℝ) (x : BaseCurve) (v w : RealModel) :
    weightedFSForm D m c x v w= -weightedFSForm D m c x w v := affineFSForm_skew c _ _ _

 theorem weighted_phase_chart_function (D m : ℕ) (b : BaseCurve) :
    (weightedPhaseInclusion D m ∘ (extChartAt 𝓘(ℝ,RealModel) b).symm)=
      affinePhase 3 ∘ weightedChart D m b ∘ Complex.equivRealProdCLM.symm := by
  funext y
  have he : chartAt RealModel b=realChart (parameters 0) b := rfl
  simp only [mfld_simps,he,realChart,Function.comp_apply,weightedPhaseInclusion,
    weightedInclusion,weightedChart,inclusion,NormalChart.inclusionChart]
  rfl

 theorem weighted_phase_chart_derivative (D m : ℕ) (b : BaseCurve) {y : RealModel}
    (hy : y∈(extChartAt 𝓘(ℝ,RealModel) b).target) :
    manifoldMapDifferential (E := PlanePhase (Option (Fin 3))) (F := RealModel)
      (weightedPhaseInclusion D m ∘ (extChartAt 𝓘(ℝ,RealModel) b).symm) y=
    realPhaseDerivative (fderiv ℂ (weightedChart D m b) (Complex.equivRealProdCLM.symm y)) := by
  change mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,PlanePhase (Option (Fin 3))) _ y=_
  rw [mfderiv_eq_fderiv,weighted_phase_chart_function]
  have hdf := ((weightedChart_smooth D m b).contDiffAt
    (((normalChartAt (parameters 0) b).sliceChart b).open_target.mem_nhds
      (realChart_complex_target (parameters 0) b hy))).differentiableAt (by simp)
  exact ((affinePhase 3).hasFDerivAt.comp y
    ((hdf.hasFDerivAt.restrictScalars ℝ).comp y Complex.equivRealProdCLM.symm.hasFDerivAt)).fderiv

 theorem weightedFSForm_positive {D m : ℕ} (hm : m<D) {c : ℝ} (hc : 0<c) (b : BaseCurve) {y : RealModel}
    (hy : y∈(extChartAt 𝓘(ℝ,RealModel) b).target) :
    0<chartTwoForm (weightedFSForm D m c) b y (1,0) (0,1) := by
  rw [weightedFSForm,chartTwoForm_manifoldPullback (weightedPhaseInclusion_smooth D m) (p := (0,y)) hy]
  change 0<affineFSForm c _
    (manifoldMapDifferential (E := PlanePhase (Option (Fin 3))) (F := RealModel)
      (weightedPhaseInclusion D m ∘ (extChartAt 𝓘(ℝ,RealModel) b).symm) y (1,0))
    (manifoldMapDifferential (E := PlanePhase (Option (Fin 3))) (F := RealModel)
      (weightedPhaseInclusion D m ∘ (extChartAt 𝓘(ℝ,RealModel) b).symm) y (0,1))
  rw [weighted_phase_chart_derivative D m b hy]
  apply affineFSForm_holomorphic_positive hc
  exact weightedChart_derivative_one_ne hm b (realChart_complex_target (parameters 0) b hy)

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Topology
open Set Function
open Hamiltonian
open scoped BigOperators ComplexConjugate
section

variable {m : ℕ} (a : Fin m → ℂ) (ε : Fin m → Bool)

def infinityRegularPoint (s : ℂ) : Affine m := (s,infinityRoot a ε s)

theorem infinityRegularPoint_contDiffAt {s : ℂ} (hs : s∈infinityRegion a) :
    ContDiffAt ℂ ∞ (infinityRegularPoint a ε) s :=
  contDiffAt_id.prodMk (infinityRoot_contDiffAt a ε hs)

theorem infinityRegularPoint_fderiv {s : ℂ} (hs : s∈infinityRegion a) (u : ℂ) :
    fderiv ℂ (infinityRegularPoint a ε) s u=(u,fderiv ℂ (infinityRoot a ε) s u) := by
  have hr := ((infinityRoot_contDiffAt a ε hs).differentiableAt (by simp)).hasFDerivAt
  have H := (hasFDerivAt_id s).prodMk hr
  change HasFDerivAt (infinityRegularPoint a ε) _ s at H
  rw [H.fderiv]
  rfl

theorem infinityPoint_fderiv {s : ℂ} (hs : s∈infinityDomain a) (u : ℂ) :
    fderiv ℂ (infinityPoint a ε) s u=
      (-u/s^2,fun j => (fderiv ℂ (infinityRoot a ε) s u j)/s-
        (infinityRoot a ε s j/s)*(u/s)) := by
  have hi := (hasDerivAt_inv hs.1).hasFDerivAt
  have hr := ((infinityRoot_contDiffAt a ε hs.2).differentiableAt (by simp)).hasFDerivAt
  have H := hi.prodMk (hi.smul hr)
  change HasFDerivAt (infinityPoint a ε) _ s at H
  rw [H.fderiv]
  apply Prod.ext
  · change u * (-(s^2)⁻¹)= -u/s^2
    ring
  · funext j
    change s⁻¹ * (fderiv ℂ (infinityRoot a ε) s u j)+
      (u * (-(s^2)⁻¹))*infinityRoot a ε s j=_
    ring

theorem realPhaseDerivative_fderiv {f : ℂ → Affine m} {s : ℂ}
    (hf : DifferentiableAt ℂ f s) :
    fderiv ℝ (fun y : Plane => affinePhase m (f (Complex.equivRealProdCLM.symm y)))
      (Complex.equivRealProdCLM s)=realPhaseDerivative (fderiv ℂ f s) := by
  have hd := (affinePhase m).hasFDerivAt.comp (Complex.equivRealProdCLM s)
    ((hf.hasFDerivAt.restrictScalars ℝ).comp (Complex.equivRealProdCLM s)
      Complex.equivRealProdCLM.symm.hasFDerivAt)
  simpa only [ContinuousLinearEquiv.symm_apply_apply,Function.comp_def,realPhaseDerivative] using hd.fderiv

end

 def complexArea (z v : ℂ) : ℝ := (conj z*v).im

 theorem complexArea_apply (z v : ℂ) : complexArea z v=z.re*v.im-z.im*v.re := by
  simp only [complexArea,Complex.mul_im,Complex.conj_re,Complex.conj_im]
  ring

 theorem complexArea_sub (z v w : ℂ) : complexArea z (v-w)=complexArea z v-complexArea z w := by
  simp only [complexArea,mul_sub,Complex.sub_im]

 theorem complexArea_mul (s z v : ℂ) : complexArea (s*z) (s*v)=Complex.normSq s*complexArea z v := by
  unfold complexArea
  rw [map_mul]
  have he : conj s*conj z*(s*v)=(Complex.normSq s : ℂ)*(conj z*v) := by
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  rw [he]
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]

 theorem complexArea_self_mul (z u : ℂ) : complexArea z (z*u)=Complex.normSq z*u.im := by
  unfold complexArea
  rw [← mul_assoc,← Complex.normSq_eq_conj_mul_self]
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]

 theorem complex_div_im (s u : ℂ) : (u/s).im=complexArea s u/Complex.normSq s := by
  rw [Complex.div_im,complexArea_apply]
  ring

 theorem complexArea_div_derivative (s w u v : ℂ) :
    complexArea (w/s) (v/s-(w/s)*(u/s))=
      complexArea w v/Complex.normSq s - Complex.normSq w/(Complex.normSq s)^2*complexArea s u := by
  rw [complexArea_sub,complexArea_self_mul,Complex.normSq_div,complex_div_im]
  have h : complexArea (w/s) (v/s)=complexArea w v/Complex.normSq s := by
    rw [div_eq_mul_inv,div_eq_mul_inv,mul_comm w,mul_comm v,complexArea_mul,Complex.normSq_inv]
    ring
  rw [h]
  ring

 theorem phaseSq_affinePhase {m : ℕ} (z : Affine m) :
    phaseSq (affinePhase m z)=Complex.normSq z.1+∑ j,Complex.normSq (z.2 j) := by
  simp only [phaseSq,phaseDot_apply,Fintype.sum_option,affinePhase_none,affinePhase_some]
  rfl

 theorem phaseArea_affinePhase {m : ℕ} (z v : Affine m) :
    phaseArea (affinePhase m z) (affinePhase m v)=complexArea z.1 v.1+∑ j,complexArea (z.2 j) (v.2 j) := by
  simp only [phaseArea_apply,Fintype.sum_option,affinePhase_none,affinePhase_some,complexArea_apply]

 theorem affineFSPrimitive_complex {m : ℕ} (c : ℝ) (z v : Affine m) :
    affineFSPrimitive c (affinePhase m z) (affinePhase m v)=
      c/(2*(1+Complex.normSq z.1+∑ j,Complex.normSq (z.2 j)))*
        (complexArea z.1 v.1+∑ j,complexArea (z.2 j) (v.2 j)) := by
  change c/(2*(1+phaseSq (affinePhase m z)))*phaseArea (affinePhase m z) (affinePhase m v)=_
  rw [phaseSq_affinePhase,phaseArea_affinePhase]
  rw [add_assoc]

 theorem affineFSPrimitive_projective_swap {m : ℕ} (c : ℝ) {s : ℂ} (hs : s≠0)
    (w : Fin m → ℂ) (u : ℂ) (v : Fin m → ℂ) :
    affineFSPrimitive c (affinePhase m (s⁻¹,fun j => w j/s))
      (affinePhase m (-u/s^2,fun j => v j/s-(w j/s)*(u/s)))=
    affineFSPrimitive c (affinePhase m (s,w)) (affinePhase m (u,v))-
      c/(2*Complex.normSq s)*complexArea s u := by
  have hq : Complex.normSq s≠0 := mt Complex.normSq_eq_zero.mp hs
  have hden : 0<1+Complex.normSq s+∑ j,Complex.normSq (w j) := by
    have hw : 0≤∑ j,Complex.normSq (w j) := Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
    linarith [Complex.normSq_nonneg s]
  have hbase : complexArea (s⁻¹) (-u/s^2)= -(complexArea s u)/(Complex.normSq s)^2 := by
    have h := complexArea_div_derivative s 1 u 0
    have he : (0 : ℂ)/s-(1/s)*(u/s)= -u/s^2 := by ring
    rw [he] at h
    simp only [one_div,complexArea_apply,Complex.one_re,Complex.one_im,Complex.zero_re,
      Complex.zero_im,mul_zero,sub_zero,Complex.normSq_one,zero_div,zero_sub] at h ⊢
    exact h.trans (by ring)
  rw [affineFSPrimitive_complex,affineFSPrimitive_complex,hbase,Complex.normSq_inv]
  simp only [Complex.normSq_div,complexArea_div_derivative,Finset.sum_sub_distrib,
    ← Finset.sum_div,← Finset.sum_mul]
  have hd : 1+Complex.normSq s+∑ j,Complex.normSq (w j)≠0 := ne_of_gt hden
  field_simp [hq,hd]
  ring_nf
  field_simp [hd]
  ring

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.Hamiltonian
open scoped Manifold ContDiff

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M N P : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N] [TopologicalSpace P] [ChartedSpace G P]

 theorem manifoldMapDifferential_comp {g : N → M} {f : P → N} {x : P}
    (hg : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) g (f x))
    (hf : MDifferentiableAt 𝓘(ℝ,G) 𝓘(ℝ,F) f x) :
    manifoldMapDifferential (E := E) (F := G) (g ∘ f) x=
      (manifoldMapDifferential (E := E) (F := F) g (f x)).comp (manifoldMapDifferential (E := F) (F := G) f x) :=
  (hg.hasMFDerivAt.comp x hf.hasMFDerivAt).mfderiv

 theorem euclideanPullbackOneForm_comp {g : N → M} {f : G → N} {x : G}
    (hg : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) g (f x))
    (hf : MDifferentiableAt 𝓘(ℝ,G) 𝓘(ℝ,F) f x)
    (α : ManifoldOneForm E M) :
    euclideanPullbackOneForm (E := F) (F := G) (fun _ => manifoldPullbackOneForm (E := E) (F := F) (fun _ => α) g 0) f (0,x)=
      euclideanPullbackOneForm (E := E) (F := G) (fun _ => α) (g ∘ f) (0,x) := by
  change (α (g (f x))).comp
    ((manifoldMapDifferential (E := E) (F := F) g (f x)).comp
      (manifoldMapDifferential (E := F) (F := G) f x))=
    (α (g (f x))).comp (manifoldMapDifferential (E := E) (F := G) (g ∘ f) x)
  rw [manifoldMapDifferential_comp hg hf]

end PackingSufficiencySupport.Hamiltonian
end

end OAI
