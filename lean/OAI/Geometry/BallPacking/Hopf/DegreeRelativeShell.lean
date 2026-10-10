import Mathlib
import OAI.Geometry.BallPacking.CircleAction.DegreeCircleCovariance

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold
open scoped ContDiff Manifold Topology BigOperators

section

variable {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]

 theorem exists_shell_profile {a b : ℝ} (ha : 0<a) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ χ=ᶠ[𝓝 (0:ℝ)] 0 ∧
      (∀ x,χ x∈Icc (0:ℝ) 1) ∧ ∀ x∈Icc a b,χ=ᶠ[𝓝 x] 1 := by
  obtain ⟨χ,hχ,_,hχU,hχ1,hχr⟩ := exists_smooth_cutoff (isCompact_Icc (a := a) (b := b))
    isOpen_Ioi (fun x hx => lt_of_lt_of_le ha hx.1)
  have hn : (0:ℝ)∉tsupport χ := by
    intro h
    exact (lt_irrefl (0:ℝ)) (hχU h)
  refine ⟨χ,hχ,?_,hχr,?_⟩
  · exact (notMem_tsupport_iff_eventuallyEq.mp hn)
  · intro x hx
    exact hχ1.filter_mono (nhds_le_nhdsSet hx)

 theorem cutoffDegreeForm_shell {F : PlanePhase ι → PlanePhase κ}
    {χ : ℝ → ℝ} {z : PlanePhase ι} (hχz : χ=ᶠ[𝓝 (phaseSq z)] 1)
    (q c d : ℝ) :
    euclideanExteriorOneForm (cutoffDegreePrimitive q F c d χ 1) z=
      euclideanExteriorOneForm (degreeConePrimitive q F c d) z := by
  have he : cutoffDegreePrimitive q F c d χ 1=ᶠ[𝓝 z] degreeConePrimitive q F c d := by
    filter_upwards [hχz.comp_tendsto phaseSq_smooth.continuous.continuousAt] with y hy
    change χ (phaseSq y)=1 at hy
    rw [cutoffDegreePrimitive_eq,radialDegreeConePrimitive,hy,one_mul,mul_one]
  simp only [euclideanExteriorOneForm,he.fderiv_eq]

 theorem exists_degree_relative_shell_maps
    {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (hF0 : ∀ z,z≠0 → F z≠0) {q : ℝ}
    (hD : ∀ z,fderiv ℝ F z z=q•F z)
    (hJ : ∀ z v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v))
    (e : PlanePhase ν →L[ℝ] PlanePhase ι) (P : PlanePhase ι →L[ℝ] PlanePhase ν)
    (hPe : P.comp e=ContinuousLinearMap.id ℝ (PlanePhase ν))
    (he : IsSmoothEmbedding 𝓘(ℝ,PlanePhase ν) 𝓘(ℝ,PlanePhase ι) ∞ e)
    (heD : ∀ z v,phaseDot (e z) (e v)=phaseDot z v)
    (heA : ∀ z v,phaseArea (e z) (e v)=phaseArea z v)
    (heJ : ∀ z,e (phaseJ z)=phaseJ (e z))
    {a b c d : ℝ} (ha : 0<a) (hc : 0<c) (hd : 0≤d) (hq : 0≤q) (hdq : q*d<1) :
    ∃ f g : PlanePhase ι → PlanePhase ι,
      ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ g ∧ LeftInverse g f ∧ RightInverse g f ∧
      (∀ z,phaseSq (f z)=phaseSq z) ∧ (∀ z,phaseSq (g z)=phaseSq z) ∧
      (∀ z,f z∈range e ↔ z∈range e) ∧ (∀ z,g z∈range e ↔ z∈range e) ∧
      (∀ s z,z∈phaseShell a b → f (phaseRotate s z)=phaseRotate s (f z)) ∧
      (∀ s z,z∈phaseShell a b → g (phaseRotate s z)=phaseRotate s (g z)) ∧
      (∀ z∈phaseShell a b,∀ v w,
        euclideanExteriorOneForm (degreeConePrimitive q F c d) (f z)
          (fderiv ℝ f z v) (fderiv ℝ f z w)=c*phaseArea v w) := by
  obtain ⟨χ,hχ,hχ0,hχr,hχ1⟩ := exists_shell_profile (b := b) ha
  have hKr (x : PlanePhase ι) (hx : x∈phaseShell a b) (y : PlanePhase ι)
      (hy : phaseSq y=phaseSq x) : y∈phaseShell a b := phaseShell_radial a b hx hy
  obtain ⟨Φ,Ψ,hΦ,hΨ,_,hi,hr,hepres,hω⟩ := exists_degree_relative_radial_moser
    hF hF0 hD hJ e P hPe he heD heA heJ hχ hχ0 hχr hc hd hq hdq (phaseShell_isCompact a b) hKr
  have h1 : (1:ℝ)∈Icc (0:ℝ) 1 := by simp
  let f := fun z => Φ (1,z)
  let g := fun z => Ψ (1,z)
  have hf : ContDiff ℝ ∞ f := hΦ.comp (contDiff_const.prodMk contDiff_id)
  have hg : ContDiff ℝ ∞ g := hΨ.comp (contDiff_const.prodMk contDiff_id)
  have hgf : LeftInverse g f := fun z => (hi 1 h1 z).1
  have hfg : RightInverse g f := fun z => (hi 1 h1 z).2
  have hfr : ∀ z,phaseSq (f z)=phaseSq z := hr 1 h1
  have hgr (z) : phaseSq (g z)=phaseSq z := by
    have hh := hfr (g z)
    rw [hfg z] at hh
    exact hh.symm
  have hfe (z) : f z∈range e ↔ z∈range e := by
    constructor
    · intro hz
      rw [←hepres 1 h1] at hz
      rcases hz with ⟨x,hx,hfx⟩
      exact hgf.injective hfx ▸ hx
    · intro hz
      have hh := mem_image_of_mem f hz
      rwa [hepres 1 h1] at hh
  have hge (z) : g z∈range e ↔ z∈range e := by
    have hh := hfe (g z)
    rw [hfg z] at hh
    exact hh.symm
  let Ω := fun z => euclideanExteriorOneForm (cutoffDegreePrimitive q F c d χ 1) z
  have hω' (z) (hz : z∈phaseShell a b) (v w) :
      Ω (f z) (fderiv ℝ f z v) (fderiv ℝ f z w)=c*phaseArea v w := by
    simpa only [manifoldPullback,vector_exteriorOneForm,preferredDifferential,mfderiv_eq_fderiv,ContinuousLinearMap.bilinearComp_apply] using hω 1 h1 z hz v w
  have hDJ (z : PlanePhase ι) : fderiv ℝ F z (phaseJ z)=q•phaseJ (F z) := by rw [hJ,hD,map_smul]
  have hfJ (z) (hz : z∈phaseShell a b) : fderiv ℝ f z (phaseJ z)=phaseJ (f z) := by
    apply moment_pullback_generator hf hg hgf hfg hfr
      (fun y v w => by simp only [euclideanExteriorOneForm,sub_apply,ContinuousLinearMap.flip_apply]; ring)
      (cutoffDegreePrimitive_nondegenerate hF hF0 hD hJ hχ hχ0 hχr hc hd hq hdq h1 (f z))
      (fun y v => ?_) (hω' z hz)
    simpa only [vector_exteriorOneForm] using cutoffDegreePrimitive_circle_contraction hF hF0 hDJ hχ c d 1 y v
  have hfc (s z) (hz : z∈phaseShell a b) : f (phaseRotate s z)=phaseRotate s (f z) :=
    circle_equivariant_on_radius hf hKr hfJ s hz
  refine ⟨f,g,hf,hg,hgf,hfg,hfr,hgr,hfe,hge,hfc,?_,?_⟩
  · intro s z hz
    apply hgf.injective
    rw [hfg,hfc s (g z) (hKr z hz _ (hgr z)),hfg]
  · intro z hz v w
    rw [←cutoffDegreeForm_shell (hχ1 (phaseSq (f z)) (hKr z hz _ (hfr z))) q c d]
    exact hω' z hz v w

end

section

variable {ι : Type} [Fintype ι]

 def phaseOptionSplit : (PlanePhase ι × Plane) ≃L[ℝ] PlanePhase (Option ι) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p j => match j with | none => p.2 | some i => p.1 i
      invFun := fun z => (fun i => z (some i),z none)
      left_inv := by intro p; rfl
      right_inv := by intro z; funext j; cases j <;> rfl
      map_add' := by intros; funext j; cases j <;> rfl
      map_smul' := by intros; funext j; cases j <;> rfl }

 def phaseInfinityInclusion : PlanePhase ι →L[ℝ] PlanePhase (Option ι) := splitInclusion phaseOptionSplit
 def phaseInfinityProjection : PlanePhase (Option ι) →L[ℝ] PlanePhase ι :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (some i)

 @[simp] theorem phaseInfinityInclusion_none (z : PlanePhase ι) : phaseInfinityInclusion z none=0 := rfl
 @[simp] theorem phaseInfinityInclusion_some (z : PlanePhase ι) (i : ι) : phaseInfinityInclusion z (some i)=z i := rfl
 theorem phaseInfinity_left : (phaseInfinityProjection (ι := ι)).comp phaseInfinityInclusion=ContinuousLinearMap.id ℝ _ := rfl
 theorem phaseInfinity_embedding : IsSmoothEmbedding 𝓘(ℝ,PlanePhase ι) 𝓘(ℝ,PlanePhase (Option ι)) ∞ (phaseInfinityInclusion (ι := ι)) := by
  unfold phaseInfinityInclusion
  exact splitInclusion_isSmoothEmbedding (phaseOptionSplit (ι := ι))
 theorem phaseInfinity_dot (z v : PlanePhase ι) :
    phaseDot (phaseInfinityInclusion z) (phaseInfinityInclusion v)=phaseDot z v := by
  simp only [phaseDot_apply,Fintype.sum_option,phaseInfinityInclusion_none,phaseInfinityInclusion_some,
    Prod.fst_zero,Prod.snd_zero,mul_zero,zero_add]
 theorem phaseInfinity_area (z v : PlanePhase ι) :
    phaseArea (phaseInfinityInclusion z) (phaseInfinityInclusion v)=phaseArea z v := by
  simp only [phaseArea_apply,Fintype.sum_option,phaseInfinityInclusion_none,phaseInfinityInclusion_some,
    Prod.fst_zero,Prod.snd_zero,mul_zero,sub_zero,zero_add]
 theorem phaseInfinity_J (z : PlanePhase ι) : phaseInfinityInclusion (phaseJ z)=phaseJ (phaseInfinityInclusion z) := by
  ext j <;> cases j <;> simp only [phaseInfinityInclusion_none,phaseInfinityInclusion_some,phaseJ_apply,
    Prod.fst_zero,Prod.snd_zero,neg_zero]
 theorem phaseInfinity_range (z : PlanePhase (Option ι)) : z∈range (phaseInfinityInclusion (ι := ι)) ↔ z none=0 := by
  constructor
  · rintro ⟨x,rfl⟩; rfl
  · intro hz
    refine ⟨fun i => z (some i),?_⟩
    funext j
    cases j with
    | none => exact hz.symm
    | some i => rfl
 theorem phaseInfinity_complex_range (z : PlanePhase (Option ι)) :
    z∈range (phaseInfinityInclusion (ι := ι)) ↔ complexCartesian.symm z none=0 := by
  rw [phaseInfinity_range]
  change z none=0 ↔ (⟨(z none).1,(z none).2⟩ : ℂ)=0
  constructor
  · intro hz; simp only [hz,Prod.fst_zero,Prod.snd_zero]; rfl
  · intro hz
    have hr := congrArg Complex.re hz
    have hi := congrArg Complex.im hz
    exact Prod.ext hr hi

 theorem phaseUnitDiagonal_eq_rotate {ζ : ℂ} (hζ : Complex.normSq ζ=1) (z : PlanePhase ι) :
    phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z=phaseRotate ζ.arg z := by
  have hn : ‖ζ‖=1 := by
    have hh := Complex.sq_norm ζ
    rw [hζ] at hh
    nlinarith [norm_nonneg ζ]
  have hne : ζ≠0 := by intro hh; simp [hh] at hn
  ext i <;> simp only [phaseUnitDiagonal_apply,phaseDiagonal,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,complexCartesian_apply,complexDiagonal_apply,
    Complex.mul_re,Complex.mul_im,phaseRotate_apply,Pi.add_apply,Pi.smul_apply,
    Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,phaseJ_apply,
    Complex.cos_arg hne,Complex.sin_arg,hn,div_one]
  · change ζ.re*(z i).1-ζ.im*(z i).2=ζ.re*(z i).1+ζ.im*(-(z i).2); ring
  · change ζ.re*(z i).2+ζ.im*(z i).1=ζ.re*(z i).2+ζ.im*(z i).1; rfl

end

section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def complexQuotientGauge (y : Option ι → ℂ) : ℂ :=
  (affineSphereScale (complexAffineQuotient y) : ℂ)*(y none)⁻¹

theorem complexQuotientGauge_smoothAt {y : Option ι → ℂ} (hy : y none≠0) :
    ContDiffAt ℝ ∞ complexQuotientGauge y := by
  apply ContDiffAt.mul
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp y
      (affineSphereScale_smooth.contDiffAt.comp y (complexAffineQuotient_smoothAt hy))
  · exact (contDiff_apply ℝ ℂ none).contDiffAt.inv hy

theorem complexQuotientGauge_ne {y : Option ι → ℂ} (hy : y none≠0) :
    complexQuotientGauge y≠0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr (affineSphereScale_pos _).ne') (inv_ne_zero hy)

theorem complexSphereLift_quotient_gauge {y : Option ι → ℂ} (hy : y none≠0) :
    complexSphereLift (complexAffineQuotient y)=complexQuotientGauge y•y := by
  change (affineSphereScale (complexAffineQuotient y) : ℂ) •
    complexAffineLift (complexAffineQuotient y)=complexQuotientGauge y•y
  rw [complexAffineLift_quotient hy,smul_smul]
  rfl

theorem mixedHopfCurvaturePullback_sphereLift {P : (Option ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) (hPn : ∀ z,z≠0 → P z≠0)
    (hPs : ∀ (ζ : ℂ) z,P (ζ•z)=ζ^2•P z)
    {Z : E → (ι → ℂ)} {x : E} (hZ : DifferentiableAt ℝ Z x)
    (c d : ℝ) (v w : E) :
    mixedHopfCurvaturePullback P c d (fun y => complexSphereLift (Z y)) x v w=
      mixedHopfCurvaturePullback P c d (fun y => complexAffineLift (Z y)) x v w := by
  have hS : DifferentiableAt ℝ (fun y => (affineSphereScale (Z y) : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x
      ((affineSphereScale_smooth.differentiable (by simp) (Z x)).comp x hZ)
  have hG : DifferentiableAt ℝ (fun y => complexAffineLift (Z y)) x :=
    (complexAffineLift_smooth.differentiable (by simp) (Z x)).comp x hZ
  have hGx : complexAffineLift (Z x)≠0 := by
    intro he
    have hh := congrFun he none
    exact one_ne_zero (by simpa only [complexAffineLift_none,Pi.zero_apply] using hh)
  exact mixedHopfCurvaturePullback_gauge hP hPn hPs hS hG
    (Complex.ofReal_ne_zero.mpr (affineSphereScale_pos _).ne') hGx c d v w

theorem mixedHopfCurvaturePullback_chart_normalize {P : (Option ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) (hPn : ∀ z,z≠0 → P z≠0)
    (hPs : ∀ (ζ : ℂ) z,P (ζ•z)=ζ^2•P z)
    {G : E → (Option ι → ℂ)} {x : E}
    (hG : DifferentiableAt ℝ G x) (hGn : ∀ y,G y none≠0)
    (c d : ℝ) (v w : E) :
    mixedHopfCurvaturePullback P c d (fun y => complexSphereLift (complexAffineQuotient (G y))) x v w=
      mixedHopfCurvaturePullback P c d G x v w := by
  have he : (fun y => complexSphereLift (complexAffineQuotient (G y)))=
      (fun y => complexQuotientGauge (G y)•G y) :=
    funext fun y => complexSphereLift_quotient_gauge (hGn y)
  rw [he]
  exact mixedHopfCurvaturePullback_gauge hP hPn hPs
    (((complexQuotientGauge_smoothAt (hGn x)).differentiableAt (by simp)).comp x hG)
    hG (complexQuotientGauge_ne (hGn x))
    (fun he => hGn x (by simpa only [Pi.zero_apply] using congrFun he none)) c d v w

variable {q : ℝ} {ℓ : ℕ}

theorem degreeHopfCurvaturePullback_sphereLift {P : (Option ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) (hPn : ∀ z,z≠0 → P z≠0)
    (hPs : ∀ (ζ : ℂ) z,P (ζ•z)=ζ^ℓ•P z)
    {Z : E → (ι → ℂ)} {x : E} (hZ : DifferentiableAt ℝ Z x)
    (c d : ℝ) (v w : E) :
    degreeHopfCurvaturePullback q P c d (fun y => complexSphereLift (Z y)) x v w=
      degreeHopfCurvaturePullback q P c d (fun y => complexAffineLift (Z y)) x v w := by
  have hS : DifferentiableAt ℝ (fun y => (affineSphereScale (Z y) : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x
      ((affineSphereScale_smooth.differentiable (by simp) (Z x)).comp x hZ)
  have hG : DifferentiableAt ℝ (fun y => complexAffineLift (Z y)) x :=
    (complexAffineLift_smooth.differentiable (by simp) (Z x)).comp x hZ
  have hGx : complexAffineLift (Z x)≠0 := by
    intro he
    have hh := congrFun he none
    exact one_ne_zero (by simpa only [complexAffineLift_none,Pi.zero_apply] using hh)
  exact degreeHopfCurvaturePullback_gauge hP hPn hPs hS hG
    (Complex.ofReal_ne_zero.mpr (affineSphereScale_pos _).ne') hGx c d v w

theorem degreeHopfCurvaturePullback_chart_normalize {P : (Option ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) (hPn : ∀ z,z≠0 → P z≠0)
    (hPs : ∀ (ζ : ℂ) z,P (ζ•z)=ζ^ℓ•P z)
    {G : E → (Option ι → ℂ)} {x : E}
    (hG : DifferentiableAt ℝ G x) (hGn : ∀ y,G y none≠0)
    (c d : ℝ) (v w : E) :
    degreeHopfCurvaturePullback q P c d (fun y => complexSphereLift (complexAffineQuotient (G y))) x v w=
      degreeHopfCurvaturePullback q P c d G x v w := by
  have he : (fun y => complexSphereLift (complexAffineQuotient (G y)))=
      (fun y => complexQuotientGauge (G y)•G y) :=
    funext fun y => complexSphereLift_quotient_gauge (hGn y)
  rw [he]
  exact degreeHopfCurvaturePullback_gauge hP hPn hPs
    (((complexQuotientGauge_smoothAt (hGn x)).differentiableAt (by simp)).comp x hG)
    hG (complexQuotientGauge_ne (hGn x))
    (fun he => hGn x (by simpa only [Pi.zero_apply] using congrFun he none)) c d v w

theorem sphere_map_fderiv_tangent {N : E → PlanePhase ι} {x : E}
    (hN : DifferentiableAt ℝ N x) (hNs : ∀ y,phaseSq (N y)=1) (v : E) :
    phaseDot (N x) (fderiv ℝ N x v)=0 := by
  have he : (fun y => phaseSq (N y))=(fun _ : E => (1:ℝ)) := funext hNs
  have hd := (phaseSq_hasFDerivAt (N x)).comp x hN.hasFDerivAt
  have hD := congrArg (fun L => L v) hd.fderiv
  change fderiv ℝ (fun y => phaseSq (N y)) x v=_ at hD
  rw [he,show fderiv ℝ (fun _ : E => (1:ℝ)) x=0 from (hasFDerivAt_const (1:ℝ) x).fderiv] at hD
  simp only [zero_apply,ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul] at hD
  linarith

theorem homogeneousCone_sphere_tangent {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : phaseSq z=1) (hFz : F z≠0)
    (c d : ℝ) {v w : PlanePhase ι} (hv : phaseDot z v=0) (hw : phaseDot z w=0) :
    euclideanExteriorOneForm (homogeneousConePrimitive F c d) z v w=mixedHopfForm F c d z v w := by
  have hzn : z≠0 := by intro he; simp [he,phaseSq] at hz
  rw [homogeneousConePrimitive_exterior hF hzn hFz,radialSymplectization_apply,hv,hw,hz]
  ring

theorem cone_flow_sphere_pullback {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (hFn : ∀ z,z≠0 → F z≠0)
    {f : PlanePhase ι → PlanePhase ι} (hf : ContDiff ℝ ∞ f)
    (hfr : ∀ z,phaseSq (f z)=phaseSq z) (c d : ℝ)
    (hfω : ∀ z,phaseSq z=1 → ∀ v w,
      euclideanExteriorOneForm (homogeneousConePrimitive F c d) (f z)
        (fderiv ℝ f z v) (fderiv ℝ f z w)=
      euclideanExteriorOneForm (homogeneousConePrimitive F c 0) z v w)
    {N : E → PlanePhase ι} {x : E} (hN : DifferentiableAt ℝ N x)
    (hNs : ∀ y,phaseSq (N y)=1) (v w : E) :
    mixedHopfForm F c d (f (N x))
      (fderiv ℝ (fun y => f (N y)) x v) (fderiv ℝ (fun y => f (N y)) x w)=
    mixedHopfForm F c 0 (N x) (fderiv ℝ N x v) (fderiv ℝ N x w) := by
  have hNz : N x≠0 := by intro he; have hh := hNs x; simp [he,phaseSq] at hh
  have hfNs : ∀ y,phaseSq (f (N y))=1 := fun y => (hfr _).trans (hNs y)
  have hfNz : f (N x)≠0 := by intro he; have hh := hfNs x; simp [he,phaseSq] at hh
  have hfN : DifferentiableAt ℝ (fun y => f (N y)) x :=
    (hf.differentiable (by simp) (N x)).comp x hN
  rw [←homogeneousCone_sphere_tangent hF.contDiffAt (hfNs x) (hFn _ hfNz) c d
    (sphere_map_fderiv_tangent hfN hfNs v) (sphere_map_fderiv_tangent hfN hfNs w),
    ←homogeneousCone_sphere_tangent hF.contDiffAt (hNs x) (hFn _ hNz) c 0
    (sphere_map_fderiv_tangent hN hNs v) (sphere_map_fderiv_tangent hN hNs w)]
  have hD (u : E) : fderiv ℝ (fun y => f (N y)) x u=
      fderiv ℝ f (N x) (fderiv ℝ N x u) :=
    congrArg (fun L => L u) (fderiv_comp x (hf.differentiable (by simp) _) hN)
  rw [hD,hD]
  exact hfω (N x) (hNs x) _ _

theorem degreeCone_sphere_tangent {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : phaseSq z=1) (hFz : F z≠0)
    (c d : ℝ) {v w : PlanePhase ι} (hv : phaseDot z v=0) (hw : phaseDot z w=0) :
    euclideanExteriorOneForm (degreeConePrimitive q F c d) z v w=degreeHopfForm q F c d z v w := by
  have hzn : z≠0 := by intro he; simp [he,phaseSq] at hz
  rw [degreeConePrimitive_exterior hF hzn hFz,radialSymplectization_apply,hv,hw,hz]
  ring

theorem degree_cone_flow_sphere_pullback {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (hFn : ∀ z,z≠0 → F z≠0)
    {f : PlanePhase ι → PlanePhase ι} (hf : ContDiff ℝ ∞ f)
    (hfr : ∀ z,phaseSq (f z)=phaseSq z) (c d : ℝ)
    (hfω : ∀ z,phaseSq z=1 → ∀ v w,
      euclideanExteriorOneForm (degreeConePrimitive q F c d) (f z)
        (fderiv ℝ f z v) (fderiv ℝ f z w)=
      euclideanExteriorOneForm (degreeConePrimitive q F c 0) z v w)
    {N : E → PlanePhase ι} {x : E} (hN : DifferentiableAt ℝ N x)
    (hNs : ∀ y,phaseSq (N y)=1) (v w : E) :
    degreeHopfForm q F c d (f (N x))
      (fderiv ℝ (fun y => f (N y)) x v) (fderiv ℝ (fun y => f (N y)) x w)=
    degreeHopfForm q F c 0 (N x) (fderiv ℝ N x v) (fderiv ℝ N x w) := by
  have hNz : N x≠0 := by intro he; have hh := hNs x; simp [he,phaseSq] at hh
  have hfNs : ∀ y,phaseSq (f (N y))=1 := fun y => (hfr _).trans (hNs y)
  have hfNz : f (N x)≠0 := by intro he; have hh := hfNs x; simp [he,phaseSq] at hh
  have hfN : DifferentiableAt ℝ (fun y => f (N y)) x :=
    (hf.differentiable (by simp) (N x)).comp x hN
  rw [←degreeCone_sphere_tangent hF.contDiffAt (hfNs x) (hFn _ hfNz) c d
    (sphere_map_fderiv_tangent hfN hfNs v) (sphere_map_fderiv_tangent hfN hfNs w),
    ←degreeCone_sphere_tangent hF.contDiffAt (hNs x) (hFn _ hNz) c 0
    (sphere_map_fderiv_tangent hN hNs v) (sphere_map_fderiv_tangent hN hNs w)]
  have hD (u : E) : fderiv ℝ (fun y => f (N y)) x u=
      fderiv ℝ f (N x) (fderiv ℝ N x u) :=
    congrArg (fun L => L u) (fderiv_comp x (hf.differentiable (by simp) _) hN)
  rw [hD,hD]
  exact hfω (N x) (hNs x) _ _

end

section
variable {ι : Type*} [Fintype ι]

def sphereAffineDescend (f : (Option ι → ℂ) → (Option ι → ℂ)) (z : ι → ℂ) : ι → ℂ :=
  complexAffineQuotient (f (complexSphereLift z))

theorem sphereAffineDescend_smooth {f : (Option ι → ℂ) → (Option ι → ℂ)}
    (hf : ContDiff ℝ ∞ f)
    (hfinf : ∀ y,phaseSq (complexCartesian y)=1 → (f y none=0 ↔ y none=0)) :
    ContDiff ℝ ∞ (sphereAffineDescend f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  have hne : f (complexSphereLift z) none≠0 := by
    intro he
    exact complexSphereLift_none_ne z ((hfinf _ (complexSphereLift_sq z)).mp he)
  exact (complexAffineQuotient_smoothAt hne).comp z (hf.comp complexSphereLift_smooth).contDiffAt

theorem sphereAffineDescend_leftInverse {f g : (Option ι → ℂ) → (Option ι → ℂ)}
    (hgf : LeftInverse g f)
    (hfr : ∀ y,phaseSq (complexCartesian (f y))=phaseSq (complexCartesian y))
    (hfinf : ∀ y,phaseSq (complexCartesian y)=1 → (f y none=0 ↔ y none=0))
    (hgζ : ∀ ζ : ℂ,Complex.normSq ζ=1 → ∀ y,phaseSq (complexCartesian y)=1 →
      g (ζ•y)=ζ•g y) : LeftInverse (sphereAffineDescend g) (sphereAffineDescend f) := by
  intro z
  have hyr : phaseSq (complexCartesian (f (complexSphereLift z)))=1 :=
    (hfr _).trans (complexSphereLift_sq z)
  have hy : f (complexSphereLift z) none≠0 := by
    intro he
    exact complexSphereLift_none_ne z ((hfinf _ (complexSphereLift_sq z)).mp he)
  obtain ⟨ζ,hζ,he⟩ := complexSphereLift_quotient_unit hy hyr
  have hζne : ζ≠0 := by intro h; simp [h] at hζ
  change complexAffineQuotient (g (complexSphereLift
    (complexAffineQuotient (f (complexSphereLift z)))))=z
  rw [he,hgζ ζ hζ _ hyr,hgf,complexAffineQuotient_smul ζ hζne,
    complexAffineQuotient_sphereLift]

theorem sphereAffineDescend_equiv {f g : (Option ι → ℂ) → (Option ι → ℂ)}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hgf : LeftInverse g f) (hfg : RightInverse g f)
    (hfr : ∀ y,phaseSq (complexCartesian (f y))=phaseSq (complexCartesian y))
    (hgr : ∀ y,phaseSq (complexCartesian (g y))=phaseSq (complexCartesian y))
    (hfinf : ∀ y,phaseSq (complexCartesian y)=1 → (f y none=0 ↔ y none=0))
    (hginf : ∀ y,phaseSq (complexCartesian y)=1 → (g y none=0 ↔ y none=0))
    (hfζ : ∀ ζ : ℂ,Complex.normSq ζ=1 → ∀ y,phaseSq (complexCartesian y)=1 → f (ζ•y)=ζ•f y)
    (hgζ : ∀ ζ : ℂ,Complex.normSq ζ=1 → ∀ y,phaseSq (complexCartesian y)=1 → g (ζ•y)=ζ•g y) :
    ContDiff ℝ ∞ (sphereAffineDescend f) ∧ ContDiff ℝ ∞ (sphereAffineDescend g) ∧
      LeftInverse (sphereAffineDescend g) (sphereAffineDescend f) ∧
      RightInverse (sphereAffineDescend g) (sphereAffineDescend f) :=
  ⟨sphereAffineDescend_smooth hf hfinf,sphereAffineDescend_smooth hg hginf,
    sphereAffineDescend_leftInverse hgf hfr hfinf hgζ,
    sphereAffineDescend_leftInverse hfg hgr hginf hfζ⟩

end

section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def complexConjugate (f : PlanePhase ι → PlanePhase κ) : (ι → ℂ) → (κ → ℂ) :=
  fun z => complexCartesian.symm (f (complexCartesian z))

theorem complexConjugate_smooth {f : PlanePhase ι → PlanePhase κ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (complexConjugate f) :=
  (complexCartesian (ι := κ)).symm.contDiff.comp (hf.comp (complexCartesian (ι := ι)).contDiff)

theorem sphereAffineDescend_curvature {P : (Option ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) (hPn : ∀ z,z≠0 → P z≠0)
    (hPs : ∀ (ζ : ℂ) z,P (ζ•z)=ζ^2•P z)
    {f : PlanePhase (Option ι) → PlanePhase (Option ι)} (hf : ContDiff ℝ ∞ f)
    (hfr : ∀ z,phaseSq (f z)=phaseSq z)
    (hfinf : ∀ z,phaseSq z=1 →
      (complexCartesian.symm (f z) none=0 ↔ complexCartesian.symm z none=0))
    (c d : ℝ)
    (hfω : ∀ z,phaseSq z=1 → ∀ v w,
      euclideanExteriorOneForm (homogeneousConePrimitive (cartesianConjugate P) c d) (f z)
        (fderiv ℝ f z v) (fderiv ℝ f z w)=
      euclideanExteriorOneForm (homogeneousConePrimitive (cartesianConjugate P) c 0) z v w)
    (x v w : ι → ℂ) :
    mixedHopfCurvaturePullback P c d
        (fun y => complexAffineLift (sphereAffineDescend (complexConjugate f) y)) x v w=
      mixedHopfCurvaturePullback P c 0 complexAffineLift x v w := by
  let G : (ι → ℂ) → (Option ι → ℂ) := fun y =>
    complexCartesian.symm (f (complexCartesian (complexSphereLift y)))
  have hG : ContDiff ℝ ∞ G := (complexConjugate_smooth hf).comp complexSphereLift_smooth
  have hGn (y : ι → ℂ) : G y none≠0 := by
    intro he
    have hh := (hfinf _ (complexSphereLift_sq y)).mp he
    exact complexSphereLift_none_ne y (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using hh)
  have hD : ContDiff ℝ ∞ (sphereAffineDescend (complexConjugate f)) := by
    apply sphereAffineDescend_smooth (complexConjugate_smooth hf)
    intro z hz
    simpa only [complexConjugate,ContinuousLinearEquiv.symm_apply_apply] using hfinf (complexCartesian z) hz
  have hNpc (y : ι → ℂ) : complexSphereLift y≠0 := by
    intro he
    exact complexSphereLift_none_ne y (by simpa only [Pi.zero_apply] using congrFun he none)
  have hGpc (y : ι → ℂ) : G y≠0 := by
    intro he
    exact hGn y (by simpa only [Pi.zero_apply] using congrFun he none)
  have hFn (z : PlanePhase (Option ι)) (hz : z≠0) : cartesianConjugate P z≠0 := by
    intro he
    have hn : complexCartesian.symm z≠0 := by
      intro hh
      exact hz (by simpa only [ContinuousLinearEquiv.apply_symm_apply,map_zero]
        using congrArg complexCartesian hh)
    exact hPn _ hn (complexCartesian.injective (he.trans (map_zero _).symm))
  have hω : mixedHopfCurvaturePullback P c d G x v w=
      mixedHopfCurvaturePullback P c 0 complexSphereLift x v w := by
    rw [mixedHopfCurvaturePullback_eq hP (hG.differentiable (by simp) x) (hGpc x) (hPn _ (hGpc x)),
      mixedHopfCurvaturePullback_eq hP (complexSphereLift_smooth.differentiable (by simp) x)
        (hNpc x) (hPn _ (hNpc x))]
    simpa only [G,ContinuousLinearEquiv.apply_symm_apply,Function.comp_def] using
      cone_flow_sphere_pullback (cartesianConjugate_smooth hP) hFn hf hfr c d hfω
        (((complexCartesian (ι := Option ι)).contDiff.comp complexSphereLift_smooth).differentiable (by simp) x)
        complexSphereLift_sq v w
  calc
    _=mixedHopfCurvaturePullback P c d
        (fun y => complexSphereLift (sphereAffineDescend (complexConjugate f) y)) x v w :=
      (mixedHopfCurvaturePullback_sphereLift hP hPn hPs (hD.differentiable (by simp) x) c d v w).symm
    _=mixedHopfCurvaturePullback P c d G x v w :=
      mixedHopfCurvaturePullback_chart_normalize hP hPn hPs (hG.differentiable (by simp) x) hGn c d v w
    _=mixedHopfCurvaturePullback P c 0 complexSphereLift x v w := hω
    _=_ := mixedHopfCurvaturePullback_sphereLift hP hPn hPs differentiableAt_id c 0 v w

end

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {q : ℝ} {ℓ : ℕ}

theorem sphereAffineDescend_degree_curvature {P : (Option ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) (hPn : ∀ z,z≠0 → P z≠0)
    (hPs : ∀ (ζ : ℂ) z,P (ζ•z)=ζ^ℓ•P z)
    {f : PlanePhase (Option ι) → PlanePhase (Option ι)} (hf : ContDiff ℝ ∞ f)
    (hfr : ∀ z,phaseSq (f z)=phaseSq z)
    (hfinf : ∀ z,phaseSq z=1 →
      (complexCartesian.symm (f z) none=0 ↔ complexCartesian.symm z none=0))
    (c d : ℝ)
    (hfω : ∀ z,phaseSq z=1 → ∀ v w,
      euclideanExteriorOneForm (degreeConePrimitive q (cartesianConjugate P) c d) (f z)
        (fderiv ℝ f z v) (fderiv ℝ f z w)=
      euclideanExteriorOneForm (degreeConePrimitive q (cartesianConjugate P) c 0) z v w)
    (x v w : ι → ℂ) :
    degreeHopfCurvaturePullback q P c d
        (fun y => complexAffineLift (sphereAffineDescend (complexConjugate f) y)) x v w=
      degreeHopfCurvaturePullback q P c 0 complexAffineLift x v w := by
  let G : (ι → ℂ) → (Option ι → ℂ) := fun y =>
    complexCartesian.symm (f (complexCartesian (complexSphereLift y)))
  have hG : ContDiff ℝ ∞ G := (complexConjugate_smooth hf).comp complexSphereLift_smooth
  have hGn (y : ι → ℂ) : G y none≠0 := by
    intro he
    have hh := (hfinf _ (complexSphereLift_sq y)).mp he
    exact complexSphereLift_none_ne y (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using hh)
  have hD : ContDiff ℝ ∞ (sphereAffineDescend (complexConjugate f)) := by
    apply sphereAffineDescend_smooth (complexConjugate_smooth hf)
    intro z hz
    simpa only [complexConjugate,ContinuousLinearEquiv.symm_apply_apply] using hfinf (complexCartesian z) hz
  have hNpc (y : ι → ℂ) : complexSphereLift y≠0 := by
    intro he
    exact complexSphereLift_none_ne y (by simpa only [Pi.zero_apply] using congrFun he none)
  have hGpc (y : ι → ℂ) : G y≠0 := by
    intro he
    exact hGn y (by simpa only [Pi.zero_apply] using congrFun he none)
  have hFn (z : PlanePhase (Option ι)) (hz : z≠0) : cartesianConjugate P z≠0 := by
    intro he
    have hn : complexCartesian.symm z≠0 := by
      intro hh
      exact hz (by simpa only [ContinuousLinearEquiv.apply_symm_apply,map_zero]
        using congrArg complexCartesian hh)
    exact hPn _ hn (complexCartesian.injective (he.trans (map_zero _).symm))
  have hω : degreeHopfCurvaturePullback q P c d G x v w=
      degreeHopfCurvaturePullback q P c 0 complexSphereLift x v w := by
    rw [degreeHopfCurvaturePullback_eq hP (hG.differentiable (by simp) x) (hGpc x) (hPn _ (hGpc x)),
      degreeHopfCurvaturePullback_eq hP (complexSphereLift_smooth.differentiable (by simp) x)
        (hNpc x) (hPn _ (hNpc x))]
    simpa only [G,ContinuousLinearEquiv.apply_symm_apply,Function.comp_def] using
      degree_cone_flow_sphere_pullback (cartesianConjugate_smooth hP) hFn hf hfr c d hfω
        (((complexCartesian (ι := Option ι)).contDiff.comp complexSphereLift_smooth).differentiable (by simp) x)
        complexSphereLift_sq v w
  calc
    _=degreeHopfCurvaturePullback q P c d
        (fun y => complexSphereLift (sphereAffineDescend (complexConjugate f) y)) x v w :=
      (degreeHopfCurvaturePullback_sphereLift hP hPn hPs (hD.differentiable (by simp) x) c d v w).symm
    _=degreeHopfCurvaturePullback q P c d G x v w :=
      degreeHopfCurvaturePullback_chart_normalize hP hPn hPs (hG.differentiable (by simp) x) hGn c d v w
    _=degreeHopfCurvaturePullback q P c 0 complexSphereLift x v w := hω
    _=_ := degreeHopfCurvaturePullback_sphereLift hP hPn hPs differentiableAt_id c 0 v w

end PackingSufficiencySupport.Hamiltonian
end

end OAI
