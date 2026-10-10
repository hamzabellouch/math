import Mathlib
import OAI.Geometry.BallPacking.BallMaps.QuadricLargeAmbientPacking

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Topology
open Set Function
open Hamiltonian
section
variable {m : ℕ}

theorem exists_quadric_relative_shell_map (a : Fin m → ℂ) (t : ℝ)
    {c d : ℝ} (hc : 0<c) (hd : 0≤d) (hdhalf : d<1/2) :
    ∃ f g : PlanePhase (Option (Option (Fin m))) → PlanePhase (Option (Option (Fin m))),
      ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ g ∧
      LeftInverse g f ∧ RightInverse g f ∧
      (∀ z,phaseSq (f z)=phaseSq z) ∧ (∀ z,phaseSq (g z)=phaseSq z) ∧
      (∀ ζ : ℂ,∀ hζ : Complex.normSq ζ=1,∀ z,phaseSq z=1 →
        f (phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z)=
          phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) (f z)) ∧
      (∀ ζ : ℂ,∀ hζ : Complex.normSq ζ=1,∀ z,phaseSq z=1 →
        g (phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z)=
          phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) (g z)) ∧
      (∀ z,phaseSq z=1 → (complexCartesian.symm (f z) none=0 ↔ complexCartesian.symm z none=0)) ∧
      (∀ z,phaseSq z=1 → (complexCartesian.symm (g z) none=0 ↔ complexCartesian.symm z none=0)) ∧
      ∀ z∈phaseShell (1/2:ℝ) 2,∀ v w,
        euclideanExteriorOneForm (homogeneousConePrimitive (homogeneousCartesian a t) c d) (f z)
            (fderiv ℝ f z v) (fderiv ℝ f z w)=
          euclideanExteriorOneForm (homogeneousConePrimitive (homogeneousCartesian a t) c 0) z v w := by
  obtain ⟨Φ,Ψ,hΦ,hΨ,hΦ0,hΦi,hΦr,hΦω,V,hV,hODE,hVe⟩ :=
    exists_homogeneousCone_shell_flow (homogeneousCartesian_smooth a t)
      (fun _ hz => homogeneousCartesian_nonzero a t hz) (homogeneousCartesian_euler a t)
      (homogeneousCartesian_J a t) (b := 2) hc hd hdhalf (by norm_num : 0<(1/2:ℝ))
  have h1 : (1:ℝ)∈Icc (0:ℝ) 1 := by simp
  let f := fun z => Φ (1,z)
  let g := fun z => Ψ (1,z)
  have hfg : LeftInverse g f := fun z => (hΦi 1 h1 z).1
  have hgf : RightInverse g f := fun z => (hΦi 1 h1 z).2
  have hfr : ∀ z,phaseSq (f z)=phaseSq z := hΦr 1 h1
  have hgr (z) : phaseSq (g z)=phaseSq z := by
    have h := hfr (g z)
    rw [hgf z] at h
    exact h.symm
  have hK (z : PlanePhase (Option (Option (Fin m)))) (hz : phaseSq z=1) :
      z∈phaseShell (1/2:ℝ) 2 := by
    change (1/2:ℝ)≤phaseSq z ∧ phaseSq z≤2
    rw [hz]
    norm_num
  have heq (U : PlanePhase (Option (Option (Fin m))) ≃L[ℝ] PlanePhase (Option (Option (Fin m))))
      (T : PlanePhase (Option (NormalPolynomialIndex m)) →L[ℝ] PlanePhase (Option (NormalPolynomialIndex m)))
      (he : ∀ z,homogeneousCartesian a t (U z)=T (homogeneousCartesian a t z))
      (hU₁ : ∀ z v,phaseDot (U z) (U v)=phaseDot z v)
      (hU₂ : ∀ z v,phaseArea (U z) (U v)=phaseArea z v)
      (hT₁ : ∀ z v,phaseDot (T z) (T v)=phaseDot z v)
      (hT₂ : ∀ z v,phaseArea (T z) (T v)=phaseArea z v)
      (z) (hz : phaseSq z=1) : f (U z)=U (f z) :=
    homogeneousCone_shell_flow_linear_equivariant (homogeneousCartesian_smooth a t)
      (fun _ hz => homogeneousCartesian_nonzero a t hz) (homogeneousCartesian_euler a t)
      (homogeneousCartesian_J a t) hc hd hdhalf (by norm_num : 0<(1/2:ℝ))
      hΦ0 hΦr hV hODE hVe U T he hU₁ hU₂ hT₁ hT₂ 1 h1 z (hK z hz)
  have hfζ (ζ : ℂ) (hζ : Complex.normSq ζ=1) (z) (hz : phaseSq z=1) :
      f (phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z)=
        phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) (f z) := by
    have hζ₂ : Complex.normSq (ζ^2)=1 := by rw [map_pow,hζ,one_pow]
    exact heq _ (phaseDiagonal (fun _ => ζ^2)) (homogeneousCartesian_circle a t ζ hζ)
      (phaseDiagonal_dot _ (fun _ => hζ)) (phaseDiagonal_area _ (fun _ => hζ))
      (phaseDiagonal_dot _ (fun _ => hζ₂)) (phaseDiagonal_area _ (fun _ => hζ₂)) z hz
  have hgζ (ζ : ℂ) (hζ : Complex.normSq ζ=1) (z) (hz : phaseSq z=1) :
      g (phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z)=
        phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) (g z) := by
    apply hfg.injective
    rw [hgf,hfζ ζ hζ (g z) ((hgr z).trans hz),hgf]
  have hfinf (z) (hz : phaseSq z=1) :
      complexCartesian.symm (f z) none=0 ↔ complexCartesian.symm z none=0 := by
    have he := heq (phaseUnitDiagonal infinitySign infinitySign_unit)
      (phaseDiagonal homogeneousInfinityOutputSign) (homogeneousCartesian_infinity a t)
      (phaseDiagonal_dot _ infinitySign_unit) (phaseDiagonal_area _ infinitySign_unit)
      (phaseDiagonal_dot _ homogeneousInfinityOutputSign_unit)
      (phaseDiagonal_area _ homogeneousInfinityOutputSign_unit) z hz
    rw [←phaseUnitDiagonal_infinity_fixed,←phaseUnitDiagonal_infinity_fixed]
    constructor
    · intro h
      apply hfg.injective
      exact he.trans h
    · intro h
      exact (he.symm.trans (congrArg f h))
  have hginf (z) (hz : phaseSq z=1) :
      complexCartesian.symm (g z) none=0 ↔ complexCartesian.symm z none=0 := by
    have h := hfinf (g z) ((hgr z).trans hz)
    rw [hgf z] at h
    exact h.symm
  refine ⟨f,g,hΦ.comp (contDiff_const.prodMk contDiff_id),hΨ.comp (contDiff_const.prodMk contDiff_id),
    hfg,hgf,hfr,hgr,hfζ,hgζ,hfinf,hginf,?_⟩
  intro z hz v w
  simpa only [one_mul] using hΦω 1 h1 z hz v w

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mixedHopf_affine_pullback (a : Fin m → ℂ) (c d t : ℝ)
    {Z : E → Affine m} {x : E} (hZ : DifferentiableAt ℝ Z x) (v w : E) :
    mixedHopfCurvaturePullback (homogeneousPolynomial a t) c d
      (fun y => complexAffineLift (affineComplex m (Z y))) x v w=
      normalAmbientForm a c d t (Z x) (fderiv ℝ Z x v) (fderiv ℝ Z x w) := by
  have hAc : DifferentiableAt ℝ (fun y => affineComplex m (Z y)) x :=
    ((affineComplex m).restrictScalars ℝ).differentiableAt.comp x hZ
  have hPc : DifferentiableAt ℝ (fun y => normalPolynomial a t (Z y)) x :=
    (((normalPolynomial_smooth a t).restrict_scalars ℝ).differentiable (by simp) _).comp x hZ
  have he : (fun y => homogeneousPolynomial a t (complexAffineLift (affineComplex m (Z y))))=
      (fun y => complexAffineLift (normalPolynomial a t (Z y))) := by
    funext y
    have h₁ : complexAffineLift (affineComplex m (Z y))=
        (fun i => match i with | none => 1 | some j => affineComplex m (Z y) j) := by
      funext i; cases i <;> rfl
    have h₂ : complexAffineLift (normalPolynomial a t (Z y))=
        (fun i => match i with | none => 1 | some j => normalPolynomial a t (Z y) j) := by
      funext i; cases i <;> rfl
    rw [h₁,h₂]
    exact homogeneousPolynomial_affine a t (Z y)
  unfold mixedHopfCurvaturePullback hopfCurvaturePullback
  change (1-2*d)*hopfForm c (complexCartesian (complexAffineLift (affineComplex m (Z x))))
    (fderiv ℝ (fun y => complexCartesian (complexAffineLift (affineComplex m (Z y)))) x v)
    (fderiv ℝ (fun y => complexCartesian (complexAffineLift (affineComplex m (Z y)))) x w)+
    d*hopfCurvaturePullback c (fun y => homogeneousPolynomial a t
      (complexAffineLift (affineComplex m (Z y)))) x v w=_
  rw [he]
  unfold hopfCurvaturePullback
  rw [hopfForm_affine_pullback hAc,hopfForm_affine_pullback hPc,normalAmbientForm_apply]
  simp only [affineComplex_cartesian]
  have hD (u : E) : fderiv ℝ (fun y => affinePhase m (Z y)) x u=
      affinePhase m (fderiv ℝ Z x u) := by
    exact congrArg (fun L => L u) ((affinePhase m).hasFDerivAt.comp x hZ.hasFDerivAt).fderiv
  have hP (u : E) : fderiv ℝ (fun y => complexCartesian (normalPolynomial a t (Z y))) x u=
      fderiv ℝ (fun y => complexCartesian (normalPolynomial a t y)) (Z x) (fderiv ℝ Z x u) :=
    congrArg (fun L => L u) (fderiv_comp x
      ((normalPolynomialCartesian_smooth a t).differentiable (by simp) _) hZ)
  rw [hD,hD,hP,hP]

theorem mixedHopf_affine (a : Fin m → ℂ) (c d t : ℝ) (x v w : Affine m) :
    mixedHopfCurvaturePullback (homogeneousPolynomial a t) c d
      (fun y => complexAffineLift (affineComplex m y)) x v w=
      normalAmbientForm a c d t x v w := by
  simpa only [fderiv_id,ContinuousLinearMap.id_apply,id_eq] using
    mixedHopf_affine_pullback a c d t (Z := id) differentiableAt_id v w

theorem exists_quadric_global_affine_moser (a : Fin m → ℂ) (t : ℝ)
    {c d : ℝ} (hc : 0<c) (hd : 0≤d) (hdhalf : d<1/2) :
    ∃ f g : Affine m → Affine m,
      ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ g ∧ LeftInverse g f ∧ RightInverse g f ∧
      (∀ x v w, normalAmbientForm a c d t (f x)
        (fderiv ℝ f x v) (fderiv ℝ f x w)=normalAmbientForm a c 0 t x v w) ∧
      (∀ x v w, normalAmbientForm a c 0 t (g x)
        (fderiv ℝ g x v) (fderiv ℝ g x w)=normalAmbientForm a c d t x v w) := by
  obtain ⟨f,g,hf,hg,hgf,hfg,hfr,hgr,hfζ,hgζ,hfinf,hginf,hω⟩ :=
    exists_quadric_relative_shell_map a t hc hd hdhalf
  obtain ⟨hfC,hgC,hgfC,hfgC⟩ :=
    sphereCartesianDescend_equiv hf hg hgf hfg hfr hgr hfinf hginf hfζ hgζ
  let fC := sphereAffineDescend (complexConjugate f)
  let gC := sphereAffineDescend (complexConjugate g)
  let A := affineComplexEquiv m
  let fA : Affine m → Affine m := fun z => A.symm (fC (A z))
  let gA : Affine m → Affine m := fun z => A.symm (gC (A z))
  have hfA : ContDiff ℝ ∞ fA := A.symm.contDiff.comp (hfC.comp A.contDiff)
  have hgA : ContDiff ℝ ∞ gA := A.symm.contDiff.comp (hgC.comp A.contDiff)
  have hgfA : LeftInverse gA fA := by
    intro z
    simp only [fA,gA,ContinuousLinearEquiv.apply_symm_apply]
    have he : gC (fC (A z))=A z := hgfC (A z)
    rw [he,ContinuousLinearEquiv.symm_apply_apply]
  have hfgA : RightInverse gA fA := by
    intro z
    simp only [fA,gA,ContinuousLinearEquiv.apply_symm_apply]
    have he : fC (gC (A z))=A z := hfgC (A z)
    rw [he,ContinuousLinearEquiv.symm_apply_apply]
  have hP : ContDiff ℝ ∞ (homogeneousPolynomial a t) :=
    (homogeneousPolynomial_smooth a t).restrict_scalars ℝ
  have hωsphere (z) (hz : phaseSq z=1) (v w) :
      euclideanExteriorOneForm (homogeneousConePrimitive
        (cartesianConjugate (homogeneousPolynomial a t)) c d) (f z)
          (fderiv ℝ f z v) (fderiv ℝ f z w)=
        euclideanExteriorOneForm (homogeneousConePrimitive
          (cartesianConjugate (homogeneousPolynomial a t)) c 0) z v w := by
    apply hω z
    change (1/2:ℝ)≤phaseSq z ∧ phaseSq z≤2
    rw [hz]
    norm_num
  have hωC (x v w : Option (Fin m) → ℂ) :
      mixedHopfCurvaturePullback (homogeneousPolynomial a t) c d
        (fun y => complexAffineLift (fC y)) x v w=
      mixedHopfCurvaturePullback (homogeneousPolynomial a t) c 0 complexAffineLift x v w :=
    sphereAffineDescend_curvature hP (fun _ hz => homogeneousPolynomial_nonzero a t hz)
      (homogeneousPolynomial_homogeneous a t) hf hfr hfinf c d hωsphere x v w
  have hωA (x v w : Affine m) : normalAmbientForm a c d t (fA x)
      (fderiv ℝ fA x v) (fderiv ℝ fA x w)=normalAmbientForm a c 0 t x v w := by
    rw [←mixedHopf_affine_pullback a c d t (hfA.differentiable (by simp) x),
      ←mixedHopf_affine a c 0 t]
    have he : (fun y => complexAffineLift (affineComplex m (fA y)))=
        (fun y => complexAffineLift (fC (A y))) := by
      funext y
      rw [←affineComplexEquiv_apply]
      change complexAffineLift (A (A.symm (fC (A y))))=_
      rw [ContinuousLinearEquiv.apply_symm_apply]
    rw [he]
    have hA : (fun y : Affine m => complexAffineLift (affineComplex m y))=
        (fun y => complexAffineLift (A y)) := by
      simp only [A,affineComplexEquiv_apply]
    rw [hA]
    change mixedHopfCurvaturePullback (homogeneousPolynomial a t) c d
      (fun y => complexAffineLift (fC (A y))) x v w=
      mixedHopfCurvaturePullback (homogeneousPolynomial a t) c 0
        (fun y => complexAffineLift (A y)) x v w
    have h₁ := mixedHopfCurvaturePullback_comp hP
      (G := fun y => complexAffineLift (fC y))
      ((complexAffineLift_smooth.comp hfC).differentiable (by simp) (A x))
      A.differentiableAt (c := c) (d := d) v w
    have h₂ := mixedHopfCurvaturePullback_comp hP
      (G := complexAffineLift)
      (complexAffineLift_smooth.differentiable (by simp) (A x))
      A.differentiableAt (c := c) (d := 0) v w
    rw [h₁,h₂]
    exact hωC (A x) (fderiv ℝ A x v) (fderiv ℝ A x w)

  exact ⟨fA,gA,hfA,hgA,hgfA,hfgA,hωA,
    diffeomorphicFormPullback_inverse hfA hgA hfgA
      (normalAmbientForm a c 0 t) (normalAmbientForm a c d t) hωA⟩

end

 def affinePhaseEquiv (m : ℕ) : Affine m ≃L[ℝ] PlanePhase (Option (Fin m)) :=
  (affineComplexEquiv m).trans complexCartesian

@[simp] theorem affinePhaseEquiv_apply (m : ℕ) (z : Affine m) :
    affinePhaseEquiv m z=affinePhase m z := by
  simp only [affinePhaseEquiv,ContinuousLinearEquiv.trans_apply,
    affineComplexEquiv_apply,affineComplex_cartesian]

 def affineRadialTarget (m : ℕ) (c : ℝ) (z : Affine m) : Ambient (m+1) :=
  optionPhaseAmbient m (fsBallMap c (affinePhaseEquiv m z))

 theorem affineRadialTarget_smooth (m : ℕ) (c : ℝ) :
    ContDiff ℝ ∞ (affineRadialTarget m c) :=
  (optionPhaseAmbient m).contDiff.comp ((fsBallMap_smooth c).comp (affinePhaseEquiv m).contDiff)

 theorem affineRadialTarget_isEmbedding (m : ℕ) {c : ℝ} (hc : 0<c) :
    Topology.IsEmbedding (affineRadialTarget m c) :=
  (optionPhaseAmbient m).toHomeomorph.isEmbedding.comp
    ((fsBallMap_isEmbedding hc).comp (affinePhaseEquiv m).toHomeomorph.isEmbedding)

 theorem affineRadialTarget_mem (m : ℕ) {c : ℝ} (hc : 0<c) (z : Affine m) :
    affineRadialTarget m c z ∈ openBall (m+1) (Real.pi*c) := by
  change capacity (optionPhaseAmbient m (fsBallMap c (affinePhaseEquiv m z)))<Real.pi*c
  rw [optionPhaseAmbient_capacity]
  exact mul_lt_mul_of_pos_left (fsBallMap_mem hc _) Real.pi_pos

 theorem affineRadialTarget_pullback {m : ℕ} (a : Fin m → ℂ) (t : ℝ)
    {c : ℝ} (hc : 0≤c) (z v w : Affine m) :
    standardForm (fderiv ℝ (affineRadialTarget m c) z v)
      (fderiv ℝ (affineRadialTarget m c) z w)=normalAmbientForm a c 0 t z v w := by
  have hs := (fsBallMap_smooth (ι := Option (Fin m)) c).differentiable (by simp)
  have hD (u : Affine m) : fderiv ℝ (affineRadialTarget m c) z u=
      optionPhaseAmbient m (fderiv ℝ (fsBallMap c) (affinePhaseEquiv m z)
        (affinePhaseEquiv m u)) := by
    exact congrArg (fun L => L u) (((optionPhaseAmbient m).hasFDerivAt.comp z
      ((hs _).hasFDerivAt.comp z (affinePhaseEquiv m).hasFDerivAt)).fderiv)
  rw [hD,hD,optionPhaseAmbient_form,fsBallMap_pullback hc,normalAmbientForm_apply]
  simp only [affinePhaseEquiv_apply,mul_zero,sub_zero,one_mul,zero_mul,add_zero]

 theorem exists_polynomial_target_embedding {m : ℕ} (a : Fin m → ℂ) (t : ℝ)
    {c d : ℝ} (hc : 0<c) (hd : 0≤d) (hdhalf : d<1/2) :
    ∃ g : Affine m → Ambient (m+1),ContDiff ℝ ∞ g ∧ Topology.IsEmbedding g ∧
      (∀ x,g x∈openBall (m+1) (Real.pi*c)) ∧
      ∀ x v w,standardForm (fderiv ℝ g x v) (fderiv ℝ g x w)=
        normalAmbientForm a c d t x v w := by
  obtain ⟨f,g,hf,hg,hgf,hfg,_hωf,hωg⟩ := exists_quadric_global_affine_moser a t hc hd hdhalf
  let e : Affine m ≃ₜ Affine m :=
    { toEquiv := ⟨g,f,hfg,hgf⟩
      continuous_toFun := hg.continuous
      continuous_invFun := hf.continuous }
  refine ⟨affineRadialTarget m c ∘ g,(affineRadialTarget_smooth m c).comp hg,
    (affineRadialTarget_isEmbedding m hc).comp e.isEmbedding,
    fun x => affineRadialTarget_mem m hc (g x),?_⟩
  intro x v w
  rw [fderiv_comp x ((affineRadialTarget_smooth m c).differentiable (by simp) (g x))
    (hg.differentiable (by simp) x)]
  change standardForm (fderiv ℝ (affineRadialTarget m c) (g x) (fderiv ℝ g x v))
    (fderiv ℝ (affineRadialTarget m c) (g x) (fderiv ℝ g x w))=_
  rw [affineRadialTarget_pullback a t hc.le,hωg]

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators Manifold
open Set Function

 def headComplexAmbient (n : ℕ) : (Ambient n × Plane) ≃L[ℝ] Ambient (n+1) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => Fin.cons (⟨x.2.1,x.2.2⟩ : ℂ) x.1
      invFun := fun z => (fun j => z j.succ,((z 0).re,(z 0).im))
      left_inv := by intro x; rfl
      right_inv := by intro z; funext j; exact Fin.cases rfl (fun _ => rfl) j
      map_add' := by intros; funext j; exact Fin.cases rfl (fun _ => rfl) j
      map_smul' := by
        intro r x
        funext j
        refine Fin.cases ?_ (fun _ => rfl) j
        apply Complex.ext <;> simp }

@[simp] theorem headComplexAmbient_apply (n : ℕ) (x : Ambient n × Plane) :
    headComplexAmbient n x=Fin.cons (⟨x.2.1,x.2.2⟩ : ℂ) x.1 := rfl

 theorem headComplexAmbient_capacity (n : ℕ) (x : Ambient n × Plane) :
    capacity (headComplexAmbient n x)=capacity x.1+radialArea x.2 := by
  simp only [capacity,Fin.sum_univ_succ,headComplexAmbient_apply,
    Fin.cons_zero,Fin.cons_succ,Complex.normSq_apply,radialArea,radiusSq]
  ring

 theorem headComplexAmbient_form (n : ℕ) (v w : Ambient n × Plane) :
    standardForm (headComplexAmbient n v) (headComplexAmbient n w)=
      standardForm v.1 w.1+planarArea v.2 w.2 := by
  simp only [standardForm,Fin.sum_univ_succ,headComplexAmbient_apply,
    Fin.cons_zero,Fin.cons_succ,planarArea_apply]
  ring

 def phasePlusPlaneAmbient (m : ℕ) : (PlanePhase (Option (Fin m)) × Plane) ≃L[ℝ] Ambient (m+2) :=
  ((optionPhaseAmbient m).prodCongr (ContinuousLinearEquiv.refl ℝ Plane)).trans (headComplexAmbient (m+1))

 theorem phasePlusPlaneAmbient_capacity (m : ℕ) (x : PlanePhase (Option (Fin m)) × Plane) :
    capacity (phasePlusPlaneAmbient m x)=Real.pi*phaseSq x.1+radialArea x.2 := by
  rw [phasePlusPlaneAmbient,ContinuousLinearEquiv.trans_apply,headComplexAmbient_capacity]
  exact congrArg (fun t => t+radialArea x.2) (optionPhaseAmbient_capacity m x.1)

 theorem phasePlusPlaneAmbient_form (m : ℕ) (v w : PlanePhase (Option (Fin m)) × Plane) :
    standardForm (phasePlusPlaneAmbient m v) (phasePlusPlaneAmbient m w)=
      phaseArea v.1 w.1+planarArea v.2 w.2 := by
  rw [phasePlusPlaneAmbient,ContinuousLinearEquiv.trans_apply,ContinuousLinearEquiv.trans_apply,
    headComplexAmbient_form]
  exact congrArg (fun t => t+planarArea v.2 w.2) (optionPhaseAmbient_form m v.1 w.1)

 theorem phasePlusPlaneAmbient_first (m : ℕ) (x : PlanePhase (Option (Fin m)) × Plane) :
    Real.pi*Complex.normSq (phasePlusPlaneAmbient m x 0)=radialArea x.2 := by
  change Real.pi*Complex.normSq (⟨x.2.1,x.2.2⟩ : ℂ)=_
  simp only [Complex.normSq_apply,radialArea,radiusSq,pow_two]

 variable {ι : Type} [Fintype ι]
 theorem phasePlusPlanePrimitive_exterior (x v w : PlanePhase ι × Plane) :
    euclideanExteriorOneForm phasePlusPlanePrimitive x v w=phaseArea v.1 w.1+planarArea v.2 w.2 := by
  let Ω : (PlanePhase ι × Plane) →L[ℝ] (PlanePhase ι × Plane) →L[ℝ] ℝ :=
    phaseArea.bilinearComp (ContinuousLinearMap.fst ℝ _ _) (ContinuousLinearMap.fst ℝ _ _)+
      planarArea.bilinearComp (ContinuousLinearMap.snd ℝ _ _) (ContinuousLinearMap.snd ℝ _ _)
  have hΩ : ∀ v w,Ω v w= -Ω w v := by
    intro v w
    change phaseArea v.1 w.1+planarArea v.2 w.2= -(phaseArea w.1 v.1+planarArea w.2 v.2)
    rw [phaseArea_skew v.1 w.1]
    simp only [planarArea_apply]
    ring
  have he : (phasePlusPlanePrimitive (ι := ι))=linearLiouville Ω := by
    funext y
    apply ContinuousLinearMap.ext
    intro u
    change (1/2:ℝ)*phaseArea y.1 u.1+(1/2:ℝ)*planarArea y.2 u.2=
      (1/2:ℝ)*(phaseArea y.1 u.1+planarArea y.2 u.2)
    ring
  rw [he,← manifoldExteriorOneForm_model,linearLiouville_exterior Ω hΩ]
  rfl

 theorem firstDiskRadial_mem_unit {x : PlanePhase ι × Plane} (hx : x∈firstDiskDomain) :
    Real.pi*phaseSq (firstDiskRadial (1/Real.pi) x).1+
      radialArea (firstDiskRadial (1/Real.pi) x).2<1 := by
  have hu : 0<1-radialArea x.2 := sub_pos.mpr hx
  have hc : 0<(1:ℝ)/Real.pi := one_div_pos.mpr Real.pi_pos
  have hfs := fsBallMap_mem (ι := ι) hc x.1
  change phaseSq (fsBallMap (1/Real.pi) x.1)<1/Real.pi at hfs
  have hb : Real.pi*phaseSq (fsBallMap (1/Real.pi) x.1)<1 := by
    simpa only [mul_comm] using (lt_div_iff₀ Real.pi_pos).mp hfs
  change Real.pi*phaseSq (Real.sqrt (1-radialArea x.2) • fsBallMap (1/Real.pi) x.1)+radialArea x.2<1
  rw [phaseSq_smul,Real.sq_sqrt hu.le]
  nlinarith [mul_lt_mul_of_pos_left hb hu]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
open Function
open Hamiltonian
open scoped Manifold Topology
open Set

 theorem exists_quadric_exact_affine_moser {m : ℕ} (a : Fin m → ℂ) (t : ℝ)
    {c d : ℝ} (hc : 0<c) (hd : 0≤d) (hdhalf : d<1/2) :
    ∃ g h : Affine m → Affine m,∃ f : Affine m → ℝ,
      ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ h ∧ ContDiff ℝ ∞ f ∧
      LeftInverse h g ∧ RightInverse h g ∧
      ∀ x,primitivePullback (ambientFSPrimitive c) g x=
        normalAmbientPrimitive a c d t x+fderiv ℝ f x := by
  obtain ⟨h,g,hh,hg,hgh,hhg,_hωh,hωg⟩ := exists_quadric_global_affine_moser a t hc hd hdhalf
  obtain ⟨f,hf,hfD⟩ := exists_exact_primitive_comparison
    (ambientFSPrimitive_smooth c) (normalAmbientPrimitive_smooth a c d t) hg (by
      intro x
      have he : normalAmbientPrimitive a c 0 t=ambientFSPrimitive c := by
        simp [normalAmbientPrimitive]
      apply ContinuousLinearMap.ext
      intro v
      apply ContinuousLinearMap.ext
      intro w
      change euclideanExteriorOneForm (ambientFSPrimitive c) (g x)
        (fderiv ℝ g x v) (fderiv ℝ g x w)=_
      rw [← he]
      exact hωg x v w)
  exact ⟨g,h,f,hg,hh,hf,hhg,hgh,hfD⟩

 def affineLinePhase (m : ℕ) : (Affine m × Plane) ≃L[ℝ] PlanePhase (Option (Fin m)) × Plane :=
  (affinePhaseEquiv m).prodCongr (ContinuousLinearEquiv.refl ℝ Plane)

 theorem affineLinePhase_primitive (m : ℕ) (c : ℝ) (x : Affine m × Plane) :
    primitivePullback (firstLinePrimitive (affineFSPrimitive c)) (affineLinePhase m) x=
      firstLinePrimitive (ambientFSPrimitive c) x := by
  apply ContinuousLinearMap.ext
  intro u
  change firstLinePrimitive (affineFSPrimitive c) (affineLinePhase m x)
    (fderiv ℝ (affineLinePhase m) x u)=_
  rw [(affineLinePhase m).fderiv,firstLinePrimitive_apply,firstLinePrimitive_apply]
  change linearLiouville planarArea x.2 u.2 + (1-radialArea x.2)*
    affineFSPrimitive c (affinePhaseEquiv m x.1) (affinePhaseEquiv m u.1)=_
  rw [affinePhaseEquiv_apply,affinePhaseEquiv_apply]
  rfl

 def affineLineRadial (m : ℕ) (x : Affine m × Plane) : PlanePhase (Option (Fin m)) × Plane :=
  firstDiskRadial (1/Real.pi) (affineLinePhase m x)

 theorem affineLineRadial_smoothOn (m : ℕ) :
    ContDiffOn ℝ ∞ (affineLineRadial m) firstDiskDomain :=
  (firstDiskRadial_smoothOn _).comp (affineLinePhase m).contDiff.contDiffOn (fun _ hx => hx)

 theorem affineLineRadial_primitive (m : ℕ) {x : Affine m × Plane} (hx : x∈firstDiskDomain) :
    primitivePullback phasePlusPlanePrimitive (affineLineRadial m) x=
      firstLinePrimitive (ambientFSPrimitive (1/Real.pi)) x := by
  have hg := (firstDiskRadial_smoothOn (ι := Option (Fin m)) (1/Real.pi)).contDiffAt
    (firstDiskDomain_open.mem_nhds (show affineLinePhase m x∈firstDiskDomain from hx))
  apply ContinuousLinearMap.ext
  intro v
  change phasePlusPlanePrimitive (affineLineRadial m x) (fderiv ℝ (affineLineRadial m) x v)=_
  rw [show affineLineRadial m=firstDiskRadial (1/Real.pi) ∘ affineLinePhase m from rfl,
    fderiv_comp x (hg.differentiableAt (by simp)) ((affineLinePhase m).differentiableAt)]
  have he := congrArg (fun L => L (affineLinePhase m v))
    (firstDiskRadial_primitive (one_div_pos.mpr Real.pi_pos).le
      (show affineLinePhase m x∈firstDiskDomain from hx))
  change phasePlusPlanePrimitive (firstDiskRadial (1/Real.pi) (affineLinePhase m x))
    (fderiv ℝ (firstDiskRadial (1/Real.pi)) (affineLinePhase m x) (affineLinePhase m v))=_ at he
  have he' := congrArg (fun L => L v) (affineLinePhase_primitive m (1/Real.pi) x)
  simp only [primitivePullback,ContinuousLinearMap.comp_apply,(affineLinePhase m).fderiv] at he'
  simp only [ContinuousLinearMap.comp_apply,(affineLinePhase m).fderiv]
  convert! he.trans he' using 1

 def affineLineTarget (m : ℕ) : Affine m × Plane → Ambient (m+2) :=
  phasePlusPlaneAmbient m ∘ affineLineRadial m

 theorem affineLineTarget_smoothOn (m : ℕ) :
    ContDiffOn ℝ ∞ (affineLineTarget m) firstDiskDomain :=
  (phasePlusPlaneAmbient m).contDiff.comp_contDiffOn (affineLineRadial_smoothOn m)

 theorem affineLineTarget_isEmbedding (m : ℕ) :
    Topology.IsEmbedding (fun x : firstDiskDomain (V := Affine m) => affineLineTarget m x.val) := by
  let j : firstDiskDomain (V := Affine m) → firstDiskDomain (V := PlanePhase (Option (Fin m))) :=
    fun x => ⟨affineLinePhase m x.val,x.property⟩
  have hj : Topology.IsEmbedding j :=
    ((affineLinePhase m).toHomeomorph.isEmbedding.comp
      (Topology.IsEmbedding.subtypeVal (p := fun x => x∈firstDiskDomain (V := Affine m)))).codRestrict
      firstDiskDomain (fun x : firstDiskDomain (V := Affine m) => x.property)
  have hr : Topology.IsEmbedding (fun x : firstDiskDomain (V := PlanePhase (Option (Fin m))) =>
      firstDiskRadial (1/Real.pi) x.val) := firstDiskRadial_isEmbedding (one_div_pos.mpr Real.pi_pos)
  have hh := (phasePlusPlaneAmbient m).toHomeomorph.isEmbedding.comp (hr.comp hj)
  convert! hh using 1

 theorem affineLineTarget_mem (m : ℕ) {x : Affine m × Plane} (hx : x∈firstDiskDomain) :
    affineLineTarget m x∈openBall (m+2) 1 := by
  change capacity (phasePlusPlaneAmbient m (affineLineRadial m x))<1
  rw [phasePlusPlaneAmbient_capacity]
  exact firstDiskRadial_mem_unit (show affineLinePhase m x∈firstDiskDomain from hx)

 theorem affineLineTarget_first (m : ℕ) (x : Affine m × Plane) :
    Real.pi*Complex.normSq (affineLineTarget m x 0)=radialArea x.2 :=
  phasePlusPlaneAmbient_first m (affineLineRadial m x)

 theorem affineLineTarget_pullback (m : ℕ) {x : Affine m × Plane} (hx : x∈firstDiskDomain)
    (v w : Affine m × Plane) :
    standardForm (fderiv ℝ (affineLineTarget m) x v) (fderiv ℝ (affineLineTarget m) x w)=
      euclideanExteriorOneForm (firstLinePrimitive (ambientFSPrimitive (1/Real.pi))) x v w := by
  have hg := (affineLineRadial_smoothOn m).contDiffAt (firstDiskDomain_open.mem_nhds hx)
  have hD := ((phasePlusPlaneAmbient m).hasFDerivAt.comp x (hg.differentiableAt (by simp)).hasFDerivAt).fderiv
  change fderiv ℝ (affineLineTarget m) x=_ at hD
  rw [hD]
  change standardForm (phasePlusPlaneAmbient m (fderiv ℝ (affineLineRadial m) x v))
    (phasePlusPlaneAmbient m (fderiv ℝ (affineLineRadial m) x w))=_
  rw [phasePlusPlaneAmbient_form,← phasePlusPlanePrimitive_exterior (affineLineRadial m x)]
  have he := primitivePullback_exterior_at
    (phasePlusPlanePrimitive_smooth (ι := Option (Fin m))).contDiffAt hg
  have he' := euclideanExteriorOneForm_congr_nhds
    (Filter.eventually_of_mem (firstDiskDomain_open.mem_nhds hx)
      (fun _ hy => affineLineRadial_primitive m hy))
  exact congrArg (fun B => B v w) (he.symm.trans he')

 theorem exists_polynomial_first_line_target {m : ℕ} (a : Fin m → ℂ) (t : ℝ)
    {d : ℝ} (hd : 0≤d) (hdhalf : d<1/2) :
    ∃ g : Affine m × Plane → Ambient (m+2),ContDiffOn ℝ ∞ g firstDiskDomain ∧
      Topology.IsEmbedding (fun x : firstDiskDomain (V := Affine m) => g x.val) ∧
      (∀ x∈firstDiskDomain,g x∈openBall (m+2) 1) ∧
      (∀ x,Real.pi*Complex.normSq (g x 0)=radialArea x.2) ∧
      ∀ x∈firstDiskDomain,∀ v w,standardForm (fderiv ℝ g x v) (fderiv ℝ g x w)=
        euclideanExteriorOneForm (firstLinePrimitive (normalAmbientPrimitive a (1/Real.pi) d t)) x v w := by
  obtain ⟨f,h,θ,hf,hh,hθ,hfh,hhf,he⟩ :=
    exists_quadric_exact_affine_moser a t (one_div_pos.mpr Real.pi_pos) hd hdhalf
  let F := firstLineLift f θ
  have hF := firstLineLift_smooth hf hθ
  have hFe := firstLineLift_isEmbedding hf hh hθ hfh hhf
  have hFm (x : Affine m × Plane) : radialArea (F x).2=radialArea x.2 := radialArea_planeRotate _ _
  have hFd : MapsTo F firstDiskDomain firstDiskDomain := fun x hx => by
    change radialArea (F x).2<1
    rw [hFm]
    exact hx
  let j : firstDiskDomain (V := Affine m) → firstDiskDomain (V := Affine m) :=
    fun x => ⟨F x.val,hFd x.property⟩
  have hj : Topology.IsEmbedding j :=
    (hFe.comp Topology.IsEmbedding.subtypeVal).codRestrict _ _
  have hge : Topology.IsEmbedding (fun x : firstDiskDomain (V := Affine m) =>
      (affineLineTarget m ∘ F) x.val) := by
    convert! (affineLineTarget_isEmbedding m).comp hj using 1
  refine ⟨affineLineTarget m ∘ F,(affineLineTarget_smoothOn m).comp hF.contDiffOn hFd,
    hge,fun x hx => affineLineTarget_mem m (hFd hx),
    fun x => (affineLineTarget_first m (F x)).trans (hFm x),?_⟩
  intro x hx v w
  have hG := (affineLineTarget_smoothOn m).contDiffAt (firstDiskDomain_open.mem_nhds (hFd hx))
  rw [fderiv_comp x (hG.differentiableAt (by simp)) (hF.differentiable (by simp) x)]
  change standardForm (fderiv ℝ (affineLineTarget m) (F x) (fderiv ℝ F x v))
    (fderiv ℝ (affineLineTarget m) (F x) (fderiv ℝ F x w))=_
  rw [affineLineTarget_pullback m (hFd hx)]
  exact congrArg (fun B => B v w) (firstLineLift_exterior (ambientFSPrimitive_smooth _)
    (normalAmbientPrimitive_smooth a _ d t) hf hθ he x)

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
