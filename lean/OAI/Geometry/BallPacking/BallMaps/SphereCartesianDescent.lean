import Mathlib
import OAI.Geometry.BallPacking.Hopf.DegreeRelativeShell

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Function
open scoped Manifold Topology
open Set Manifold
section
variable {ι : Type*} [Fintype ι]

theorem complexConjugate_leftInverse {f g : PlanePhase ι → PlanePhase ι}
    (h : LeftInverse g f) : LeftInverse (complexConjugate g) (complexConjugate f) := by
  intro z
  simp only [complexConjugate,ContinuousLinearEquiv.apply_symm_apply]
  rw [h,ContinuousLinearEquiv.symm_apply_apply]

theorem complexConjugate_radius {f : PlanePhase ι → PlanePhase ι}
    (h : ∀ z,phaseSq (f z)=phaseSq z) (z : ι → ℂ) :
    phaseSq (complexCartesian (complexConjugate f z))=phaseSq (complexCartesian z) := by
  simp only [complexConjugate,ContinuousLinearEquiv.apply_symm_apply,h]

theorem complexConjugate_circle {f : PlanePhase ι → PlanePhase ι}
    (h : ∀ ζ : ℂ,∀ hζ : Complex.normSq ζ=1,∀ z,phaseSq z=1 →
      f (phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z)=
        phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) (f z))
    (ζ : ℂ) (hζ : Complex.normSq ζ=1) (z : ι → ℂ) (hz : phaseSq (complexCartesian z)=1) :
    complexConjugate f (ζ•z)=ζ•complexConjugate f z := by
  have he (y : ι → ℂ) : complexDiagonal (fun _ => ζ) y=ζ•y := rfl
  have hh := h ζ hζ (complexCartesian z) hz
  simp only [phaseUnitDiagonal_apply,phaseDiagonal_cartesian,he] at hh
  apply complexCartesian.injective
  change f (complexCartesian (ζ•z))=complexCartesian (ζ•complexCartesian.symm (f (complexCartesian z)))
  rw [hh]
  rw [←he,←phaseDiagonal_cartesian,ContinuousLinearEquiv.apply_symm_apply]

theorem sphereCartesianDescend_equiv
    {f g : PlanePhase (Option ι) → PlanePhase (Option ι)}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hgf : LeftInverse g f) (hfg : RightInverse g f)
    (hfr : ∀ y,phaseSq (f y)=phaseSq y) (hgr : ∀ y,phaseSq (g y)=phaseSq y)
    (hfinf : ∀ y,phaseSq y=1 → (complexCartesian.symm (f y) none=0 ↔ complexCartesian.symm y none=0))
    (hginf : ∀ y,phaseSq y=1 → (complexCartesian.symm (g y) none=0 ↔ complexCartesian.symm y none=0))
    (hfζ : ∀ ζ : ℂ,∀ hζ : Complex.normSq ζ=1,∀ z,phaseSq z=1 →
      f (phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z)=phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) (f z))
    (hgζ : ∀ ζ : ℂ,∀ hζ : Complex.normSq ζ=1,∀ z,phaseSq z=1 →
      g (phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z)=phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) (g z)) :
    ContDiff ℝ ∞ (sphereAffineDescend (complexConjugate f)) ∧
      ContDiff ℝ ∞ (sphereAffineDescend (complexConjugate g)) ∧
      LeftInverse (sphereAffineDescend (complexConjugate g)) (sphereAffineDescend (complexConjugate f)) ∧
      RightInverse (sphereAffineDescend (complexConjugate g)) (sphereAffineDescend (complexConjugate f)) := by
  apply sphereAffineDescend_equiv (complexConjugate_smooth hf) (complexConjugate_smooth hg)
    (complexConjugate_leftInverse hgf) (complexConjugate_leftInverse hfg)
    (complexConjugate_radius hfr) (complexConjugate_radius hgr)
  · intro y hy
    simpa only [complexConjugate,ContinuousLinearEquiv.symm_apply_apply] using hfinf (complexCartesian y) hy
  · intro y hy
    simpa only [complexConjugate,ContinuousLinearEquiv.symm_apply_apply] using hginf (complexCartesian y) hy
  · exact complexConjugate_circle hfζ
  · exact complexConjugate_circle hgζ

end

variable {ι κ : Type} [Fintype ι] [Fintype κ]

 theorem exists_degree_global_affine_moser {P : (Option ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℂ ∞ P) (hPn : ∀ z,z≠0 → P z≠0)
    {ℓ : ℕ} (hPs : ∀ (ζ : ℂ) z,P (ζ•z)=ζ^ℓ•P z)
    {c d : ℝ} (hc : 0<c) (hd : 0≤d) (hdℓ : (ℓ:ℝ)*d<1) :
    ∃ f g : (ι → ℂ) → (ι → ℂ),
      ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ g ∧ LeftInverse g f ∧ RightInverse g f ∧
      (∀ x v w,degreeAffineForm (ℓ:ℝ) P c d (f x) (fderiv ℝ f x v) (fderiv ℝ f x w)=
        degreeAffineForm (ℓ:ℝ) P c 0 x v w) ∧
      (∀ x v w,degreeAffineForm (ℓ:ℝ) P c 0 (g x) (fderiv ℝ g x v) (fderiv ℝ g x w)=
        degreeAffineForm (ℓ:ℝ) P c d x v w) := by
  have hPr := hP.restrict_scalars ℝ
  have hF := cartesianConjugate_smooth hPr
  obtain ⟨f,g,hf,hg,hgf,hfg,hfr,hgr,hfe,hge,hfc,hgc,hω⟩ := exists_degree_relative_shell_maps
    hF (fun z hz => cartesianConjugate_nonzero hPn hz)
    (cartesianConjugate_euler hP hPs) (cartesianConjugate_J hP)
    phaseInfinityInclusion phaseInfinityProjection phaseInfinity_left phaseInfinity_embedding
    phaseInfinity_dot phaseInfinity_area phaseInfinity_J (b := 2) (by norm_num : 0<(1/2:ℝ))
    hc hd (Nat.cast_nonneg ℓ) hdℓ
  have hK (z : PlanePhase (Option ι)) (hz : phaseSq z=1) : z∈phaseShell (1/2:ℝ) 2 := by
    change (1/2:ℝ)≤phaseSq z ∧ phaseSq z≤2
    rw [hz]; norm_num
  have hfinf (z : PlanePhase (Option ι)) (_hz : phaseSq z=1) :
      complexCartesian.symm (f z) none=0 ↔ complexCartesian.symm z none=0 := by
    simpa only [phaseInfinity_complex_range] using hfe z
  have hginf (z : PlanePhase (Option ι)) (_hz : phaseSq z=1) :
      complexCartesian.symm (g z) none=0 ↔ complexCartesian.symm z none=0 := by
    simpa only [phaseInfinity_complex_range] using hge z
  have hfζ (ζ : ℂ) (hζ : Complex.normSq ζ=1) (z : PlanePhase (Option ι)) (hz : phaseSq z=1) :
      f (phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z)=phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) (f z) := by
    simp only [phaseUnitDiagonal_eq_rotate]
    exact hfc ζ.arg z (hK z hz)
  have hgζ (ζ : ℂ) (hζ : Complex.normSq ζ=1) (z : PlanePhase (Option ι)) (hz : phaseSq z=1) :
      g (phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z)=phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) (g z) := by
    simp only [phaseUnitDiagonal_eq_rotate]
    exact hgc ζ.arg z (hK z hz)
  obtain ⟨hfC,hgC,hgfC,hfgC⟩ := sphereCartesianDescend_equiv hf hg hgf hfg hfr hgr hfinf hginf hfζ hgζ
  let fC := sphereAffineDescend (complexConjugate f)
  let gC := sphereAffineDescend (complexConjugate g)
  have hzero : degreeConePrimitive (ℓ:ℝ) (cartesianConjugate P) c 0=c•standardLiouville :=
    funext (degreeConePrimitive_zero (ℓ:ℝ) (cartesianConjugate P) c)
  have hωs (z) (hz : phaseSq z=1) (v w) :
      euclideanExteriorOneForm (degreeConePrimitive (ℓ:ℝ) (cartesianConjugate P) c d) (f z)
        (fderiv ℝ f z v) (fderiv ℝ f z w)=
      euclideanExteriorOneForm (degreeConePrimitive (ℓ:ℝ) (cartesianConjugate P) c 0) z v w := by
    rw [hzero,euclideanExteriorOneForm_smul c
      ((standardLiouville_smooth (ι := Option ι)).contDiffAt.differentiableAt (by simp)),standardLiouville_exterior]
    exact hω z (hK z hz) v w
  have hωC (x v w : ι → ℂ) :
      degreeAffineForm (ℓ:ℝ) P c d (fC x) (fderiv ℝ fC x v) (fderiv ℝ fC x w)=
      degreeAffineForm (ℓ:ℝ) P c 0 x v w := by
    rw [degreeAffineForm_pullback hPr (hfC.differentiable (by simp) x),degreeAffineForm_apply]
    exact sphereAffineDescend_degree_curvature hPr hPn hPs hf hfr hfinf c d hωs x v w
  exact ⟨fC,gC,hfC,hgC,hgfC,hfgC,hωC,
    diffeomorphicFormPullback_inverse hfC hgC hfgC (degreeAffineForm (ℓ:ℝ) P c 0)
      (degreeAffineForm (ℓ:ℝ) P c d) hωC⟩

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
open Hamiltonian

def affineComplexEquiv (m : ℕ) : Affine m ≃L[ℝ] (Option (Fin m) → ℂ) :=
  ((LinearEquiv.piOptionEquivProd ℝ (M := fun _ : Option (Fin m) => ℂ)).symm).toContinuousLinearEquiv

@[simp] theorem affineComplexEquiv_apply (m : ℕ) (z : Affine m) :
    affineComplexEquiv m z=affineComplex m z := by
  funext j
  cases j <;> rfl

@[simp] theorem affineComplexEquiv_symm_apply (m : ℕ) (z : Option (Fin m) → ℂ) :
    (affineComplexEquiv m).symm z=(z none,fun j => z (some j)) := rfl

@[simp] theorem affineComplex_cartesian (m : ℕ) (z : Affine m) :
    complexCartesian (affineComplex m z)=affinePhase m z := by
  funext j
  cases j <;> rfl

@[simp] theorem affineComplexEquiv_toCLM (m : ℕ) :
    (affineComplexEquiv m).toContinuousLinearMap=(affineComplex m).restrictScalars ℝ := by
  apply ContinuousLinearMap.ext
  intro z
  exact affineComplexEquiv_apply m z

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators
open Set Function
open scoped Manifold Topology
section

def optionComplexAmbient (m : ℕ) : (Option (Fin m) → ℂ) ≃L[ℝ] Ambient (m+1) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun z => Fin.cons (z none) (fun j => z (some j))
      invFun := fun z j => match j with | none => z 0 | some j => z j.succ
      left_inv := by intro z; funext j; cases j <;> rfl
      right_inv := by intro z; funext j; exact Fin.cases rfl (fun _ => rfl) j
      map_add' := by intros; funext j; exact Fin.cases rfl (fun _ => rfl) j
      map_smul' := by intros; funext j; exact Fin.cases rfl (fun _ => rfl) j }

def optionPhaseAmbient (m : ℕ) : PlanePhase (Option (Fin m)) ≃L[ℝ] Ambient (m+1) :=
  complexCartesian.symm.trans (optionComplexAmbient m)

theorem optionPhaseAmbient_capacity (m : ℕ) (z : PlanePhase (Option (Fin m))) :
    capacity (optionPhaseAmbient m z)=Real.pi*phaseSq z := by
  obtain ⟨z,rfl⟩ := complexCartesian.surjective z
  simp only [optionPhaseAmbient,ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.symm_apply_apply,capacity,complexCartesian_sq]
  congr 1
  simp only [Fin.sum_univ_succ,Fintype.sum_option]
  rfl

theorem optionPhaseAmbient_form (m : ℕ) (v w : PlanePhase (Option (Fin m))) :
    standardForm (optionPhaseAmbient m v) (optionPhaseAmbient m w)=phaseArea v w := by
  obtain ⟨v,rfl⟩ := complexCartesian.surjective v
  obtain ⟨w,rfl⟩ := complexCartesian.surjective w
  simp only [optionPhaseAmbient,ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.symm_apply_apply,standardForm,phaseArea_apply]
  simp only [Fin.sum_univ_succ,Fintype.sum_option]
  rfl

variable {ι : Type*} [Fintype ι]

def fsBallHomeomorph {a : ℝ} (ha : 0<a) : PlanePhase ι ≃ₜ phaseOpenBall (ι := ι) a where
  toEquiv :=
    { toFun := fun z => ⟨fsBallMap a z,fsBallMap_mem ha z⟩
      invFun := fun z => fsAffineMap a z.val
      left_inv := fsAffineMap_fsBallMap ha
      right_inv := by intro z; apply Subtype.ext; exact fsBallMap_fsAffineMap ha z.property }
  continuous_toFun := (fsBallMap_smooth a).continuous.subtype_mk _
  continuous_invFun := (fsAffineMap_smoothOn a).continuousOn.comp_continuous
    continuous_subtype_val (fun z => z.property)

theorem fsBallMap_isEmbedding {a : ℝ} (ha : 0<a) :
    Topology.IsEmbedding (fsBallMap (ι := ι) a) :=
  Topology.IsEmbedding.subtypeVal.comp (fsBallHomeomorph (ι := ι) ha).isEmbedding

end

 theorem complexCartesian_standardForm {n : ℕ} (v w : Ambient n) :
    standardForm v w=phaseArea (complexCartesian v) (complexCartesian w) := by
  simp only [standardForm,phaseArea_apply,complexCartesian]
  rfl

 theorem complexRadialTarget_mem {n : ℕ} {c : ℝ} (hc : 0<c) (x : Ambient n) :
    complexCartesian.symm (fsBallMap c (complexCartesian x)) ∈ openBall n (Real.pi*c) := by
  change Real.pi*(∑ i,Complex.normSq (complexCartesian.symm (fsBallMap c (complexCartesian x)) i))<Real.pi*c
  rw [←complexCartesian_sq,ContinuousLinearEquiv.apply_symm_apply]
  exact mul_lt_mul_of_pos_left (fsBallMap_mem hc _) Real.pi_pos

 theorem exists_degree_polynomial_target_embedding {n : ℕ} {κ : Type} [Fintype κ]
    {P : (Option (Fin n) → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℂ ∞ P) (hPn : ∀ z,z≠0 → P z≠0)
    {ℓ : ℕ} (hPs : ∀ (ζ : ℂ) z,P (ζ•z)=ζ^ℓ•P z)
    {c d : ℝ} (hc : 0<c) (hd : 0≤d) (hdℓ : (ℓ:ℝ)*d<1) :
    ∃ g : Ambient n → Ambient n,ContDiff ℝ ∞ g ∧ Topology.IsEmbedding g ∧
      (∀ x,g x∈openBall n (Real.pi*c)) ∧
      ∀ x v w,standardForm (fderiv ℝ g x v) (fderiv ℝ g x w)=
        degreeAffineForm (ℓ:ℝ) P c d x v w := by
  obtain ⟨f,g,hf,hg,hgf,hfg,_hfω,hgω⟩ := exists_degree_global_affine_moser hP hPn hPs hc hd hdℓ
  let e : Ambient n ≃ₜ Ambient n :=
    { toEquiv := ⟨g,f,hfg,hgf⟩
      continuous_toFun := hg.continuous
      continuous_invFun := hf.continuous }
  let h : Ambient n → Ambient n := fun x => complexCartesian.symm (fsBallMap c (complexCartesian (g x)))
  have hh : ContDiff ℝ ∞ h := (complexCartesian (ι := Fin n)).symm.contDiff.comp
    ((fsBallMap_smooth c).comp ((complexCartesian (ι := Fin n)).contDiff.comp hg))
  refine ⟨h,hh,complexCartesian.symm.toHomeomorph.isEmbedding.comp
    ((fsBallMap_isEmbedding hc).comp (complexCartesian.toHomeomorph.isEmbedding.comp e.isEmbedding)),
    fun x => complexRadialTarget_mem hc (g x),?_⟩
  intro x v w
  have hD (u : Ambient n) : fderiv ℝ h x u=complexCartesian.symm
      (fderiv ℝ (fsBallMap c) (complexCartesian (g x)) (complexCartesian (fderiv ℝ g x u))) := by
    exact congrArg (fun L => L u) ((complexCartesian.symm.hasFDerivAt.comp x
      (((fsBallMap_smooth c).differentiable (by simp) _).hasFDerivAt.comp x
        (complexCartesian.hasFDerivAt.comp x (hg.differentiable (by simp) x).hasFDerivAt))).fderiv)
  rw [hD,hD,complexCartesian_standardForm]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  rw [fsBallMap_pullback hc.le,←degreeAffineForm_zero (ℓ:ℝ) P c,hgω]

 theorem affineFSForm_mul {ι : Type*} [Fintype ι] (a b : ℝ) (x v w : PlanePhase ι) :
     affineFSForm (a*b) x v w=a*affineFSForm b x v w := by
   rw [affineFSForm_apply,affineFSForm_apply]
   ring

 def complexFSAffine {n : ℕ} (a : ℝ) (x : Ambient n) : Ambient n :=
   complexCartesian.symm (fsAffineMap a (complexCartesian x))

 theorem complexFSAffine_smoothOn {n : ℕ} (a : ℝ) :
     ContDiffOn ℝ ∞ (complexFSAffine (n := n) a) (openBall n (Real.pi*a)) := by
   have hinto : MapsTo (complexCartesian (ι := Fin n)) (openBall n (Real.pi*a)) (phaseOpenBall a) := by
     intro x hx
     change phaseSq (complexCartesian x)<a
     rw [complexCartesian_sq]
     exact (mul_lt_mul_iff_right₀ Real.pi_pos).mp hx
   exact (complexCartesian (ι := Fin n)).symm.contDiff.comp_contDiffOn
     ((fsAffineMap_smoothOn a).comp (complexCartesian (ι := Fin n)).contDiff.contDiffOn hinto)

 theorem complexCartesian_ball_into {n : ℕ} {a : ℝ}
     (x : openBall n (Real.pi*a)) : complexCartesian x.val∈phaseOpenBall a := by
   change phaseSq (complexCartesian x.val)<a
   rw [complexCartesian_sq]
   exact (mul_lt_mul_iff_right₀ Real.pi_pos).mp x.property

 theorem complexCartesian_ball_isEmbedding {n : ℕ} (a : ℝ) :
     Topology.IsEmbedding (fun x : openBall n (Real.pi*a) => complexCartesian x.val) :=
   (complexCartesian (ι := Fin n)).toHomeomorph.isEmbedding.comp
     (Topology.IsEmbedding.subtypeVal (p := fun x => x∈openBall n (Real.pi*a)))

 theorem complexCartesian_ball_codRestrict {n : ℕ} (a : ℝ) :
     Topology.IsEmbedding (fun x : openBall n (Real.pi*a) =>
       (⟨complexCartesian x.val,complexCartesian_ball_into x⟩ : phaseOpenBall a)) :=
   (complexCartesian_ball_isEmbedding (n := n) a).codRestrict (phaseOpenBall a) complexCartesian_ball_into

 theorem complexFSAffine_isEmbedding {n : ℕ} {a : ℝ} (ha : 0<a) :
     Topology.IsEmbedding (fun x : openBall n (Real.pi*a) => complexFSAffine a x.val) := by
   have hf : Topology.IsEmbedding (fun x : openBall n (Real.pi*a) => fsAffineMap a (complexCartesian x.val)) :=
     (fsAffineMap_isEmbedding (ι := Fin n) ha).comp (complexCartesian_ball_codRestrict (n := n) a)
   exact (complexCartesian (ι := Fin n)).symm.toHomeomorph.isEmbedding.comp hf

 theorem complexFSAffine_pullback {n : ℕ} {a : ℝ} (ha : 0<a) {x : Ambient n}
     (hx : x∈openBall n (Real.pi*a)) (v w : Ambient n) :
     affineFSForm a (complexCartesian (complexFSAffine a x))
       (complexCartesian (fderiv ℝ (complexFSAffine a) x v))
       (complexCartesian (fderiv ℝ (complexFSAffine a) x w))=standardForm v w := by
   have hxc : complexCartesian x∈phaseOpenBall a := by
     change phaseSq (complexCartesian x)<a
     rw [complexCartesian_sq]
     exact (mul_lt_mul_iff_right₀ Real.pi_pos).mp hx
   have hs := ((fsAffineMap_smoothOn a).contDiffAt ((phaseOpenBall_open a).mem_nhds hxc)).differentiableAt (by simp)
   have hd (u : Ambient n) : fderiv ℝ (complexFSAffine a) x u=
       complexCartesian.symm (fderiv ℝ (fsAffineMap a) (complexCartesian x) (complexCartesian u)) := by
     exact congrArg (fun L => L u) ((complexCartesian.symm.hasFDerivAt.comp x
       (hs.hasFDerivAt.comp x (complexCartesian (ι := Fin n)).hasFDerivAt)).fderiv)
   rw [complexFSAffine,hd,hd]
   simp only [ContinuousLinearEquiv.apply_symm_apply]
   rw [fsAffineMap_pullback ha hxc,complexCartesian_standardForm]

 theorem complexFSAffine_ball_embedding {m : ℕ} {r a : ℝ} (ha : 0<a) (hr : r<Real.pi*a) :
     FormNeighborhoodEmbedding (closedBall (m+1) r) (fun _ => successorStandardForm m)
       (fun x => (affineFSForm a (complexCartesian x)).bilinearComp
         complexCartesian.toContinuousLinearMap complexCartesian.toContinuousLinearMap) (complexFSAffine a) := by
   refine ⟨openBall (m+1) (Real.pi*a),openBall_isOpen _ _,?_,
     (complexFSAffine_smoothOn a).contMDiffOn,complexFSAffine_isEmbedding ha,?_⟩
   · intro x hx
     exact (show capacity x≤r from hx).trans_lt hr
   · intro x hx v w
     simp only [mfderiv_eq_fderiv]
     exact (complexFSAffine_pullback ha hx v w).trans
       (successorStandardForm_apply m v w).symm

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 theorem exists_uniform_cubic_bubble_ball {L S A B p N : ℕ} (m : ℕ)
     (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hp : p<L-S) (hN : p<N)
     (hm : m+1≤p) (t δ : ℝ) {c : ℝ} (hc : 0<c)
     {D : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) (hD0 : 0<D 0)
     {r : ℝ} (hr : r<Real.pi*(D 0*((m+1:ℕ)*c)))
     {T : Set (Fin 3 → ℂ)} (hT : IsOpen T) (h0T : (0 : Fin 3 → ℂ)∈T)
     {η : ℝ} (hη : 0<η) :
     ∃ τ>0,τ≤η ∧ ∀ ε∈Ioc (0:ℝ) τ,∃ g : Ambient 3 → Ambient 3,
       FormNeighborhoodEmbedding (closedBall 3 r) (fun _ => successorStandardForm 2)
         (degreeAffineForm (L:ℝ) (cubicBubblePolynomial (A := A) (B := B) L S (m+1) p N t δ ε) c (D ε)) g ∧
       MapsTo g (closedBall 3 r) T := by
   let a : ℝ := D 0*((m+1:ℕ)*c)
   have ha : 0<a := mul_pos hD0 (mul_pos (by positivity) hc)
   let f : Ambient 3 → Ambient 3 := complexFSAffine a
   have hf := complexFSAffine_ball_embedding (m := 2) ha hr
   let K : Set (Fin 3 → ℂ) := f '' closedBall 3 r
   have hK : IsCompact K := by
     obtain ⟨U,_hU,hKU,hs,_he,_hf⟩ := hf
     exact (closedBall_isCompact 3 r).image_of_continuousOn (hs.continuousOn.mono hKU)
   obtain ⟨τ,hτ,hτη,hall⟩ := exists_uniform_cubic_bubble_transfer m hAS hS hB hp hN hm t δ hc hD hD0 hK hT h0T hη
   refine ⟨τ,hτ,hτη,?_⟩
   intro ε hε
   obtain ⟨g,W,hW,hKW,hg,he,hgT,hgf⟩ := hall ε hε
   have him : MapsTo f (closedBall 3 r) W := fun x hx => hKW ⟨x,hx,rfl⟩
   refine ⟨g ∘ f,hf.postcompose hW hg.contMDiff.contMDiffOn he ?_ him,?_⟩
   · intro x hx v w
     simp only [mfderiv_eq_fderiv]
     exact (hgf x hx v w).trans
       (affineFSForm_mul (D 0) ((m+1:ℕ)*c) (complexCartesian x)
         (complexCartesian v) (complexCartesian w)).symm
   · exact hgT.comp him

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators

variable {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]
 def complexLeftBlock (z : κ → ℂ) : (κ ⊕ (ι ⊕ ν)) → ℂ :=
   Sum.elim z (0 : (ι ⊕ ν) → ℂ)

 def complexLeftBlockCLM : (κ → ℂ) →L[ℝ] ((κ ⊕ (ι ⊕ ν)) → ℂ) :=
   ContinuousLinearMap.pi fun i => match i with
     | Sum.inl k => ContinuousLinearMap.proj k
     | Sum.inr (Sum.inl _) => 0
     | Sum.inr (Sum.inr _) => 0

omit [Fintype ι] [Fintype κ] [Fintype ν] in
 theorem complexLeftBlockCLM_apply (z : κ → ℂ) :
     complexLeftBlockCLM (ι := ι) (ν := ν) z=complexLeftBlock z := by
   ext i
   rcases i with (i|(k|j)) <;> rfl

 theorem complexLeftBlock_sq (z : κ → ℂ) :
     phaseSq (complexCartesian (complexLeftBlock (ι := ι) (ν := ν) z))=
       phaseSq (complexCartesian z) := by
   simp [complexCartesian_sq,complexLeftBlock,Fintype.sum_sum_type]

 theorem complexLeftBlock_pairing (z v : κ → ℂ) :
     complexPairing (complexLeftBlock (ι := ι) (ν := ν) z) (complexLeftBlock v)=
       complexPairing z v := by
   simp [complexPairing,complexLeftBlock,Fintype.sum_sum_type]

 theorem complexLeftBlock_hopf (c : ℝ) (z v : κ → ℂ) :
     hopfPrimitive c (complexCartesian (complexLeftBlock (ι := ι) (ν := ν) z))
       (complexCartesian (complexLeftBlock v))=
     hopfPrimitive c (complexCartesian z) (complexCartesian v) := by
   simp only [hopfPrimitive,smul_apply,smul_eq_mul,complexLeftBlock_sq,
     ←complexPairing_im,complexLeftBlock_pairing]

 theorem complexLeftBlock_primitive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
     {F : E → (κ → ℂ)} (hF : ContDiff ℝ ∞ F) (c : ℝ) :
     primitivePullback (hopfPrimitive c)
       (fun z => complexCartesian (complexLeftBlock (ι := ι) (ν := ν) (F z)))=
     primitivePullback (hopfPrimitive c) (fun z => complexCartesian (F z)) := by
   ext z v
   have hD := complexCartesian.hasFDerivAt.comp z
     ((complexLeftBlockCLM (ι := ι) (ν := ν)).hasFDerivAt.comp z
       (hF.differentiable (by simp) z).hasFDerivAt)
   have hD' := complexCartesian.hasFDerivAt.comp z (hF.differentiable (by simp) z).hasFDerivAt
   change hopfPrimitive c _ (fderiv ℝ _ z v)=hopfPrimitive c _ (fderiv ℝ _ z v)
   rw [show fderiv ℝ (fun z => complexCartesian (complexLeftBlock (ι := ι) (ν := ν) (F z))) z=_ from by simpa only [Function.comp_def,complexLeftBlockCLM_apply] using hD.fderiv,
     show fderiv ℝ (fun z => complexCartesian (F z)) z=_ from hD'.fderiv]
   simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
     complexLeftBlockCLM_apply] using complexLeftBlock_hopf (ι := ι) (ν := ν) c (F z) (fderiv ℝ F z v)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 def firstBubbleLift (z : CubicAmbient) : Option (Fin 3) → ℂ
   | none => z.2
   | some i => ![1,z.1.1,z.1.2] i

 theorem firstBubbleLift_smooth : ContDiff ℂ ∞ firstBubbleLift := by
   apply contDiff_pi.mpr
   rintro (_|i)
   · exact contDiff_snd
   · fin_cases i
     · exact contDiff_const
     · exact contDiff_fst.fst
     · exact contDiff_fst.snd

 theorem firstBubbleLift_coordinates (z : CubicAmbient) :
     distinguishedHomogeneousCoordinates (firstBubbleLift z)=firstQuadricChart z := by
   ext i
   fin_cases i <;> rfl

 theorem firstBubbleLift_nonzero (z : CubicAmbient) : firstBubbleLift z≠0 := by
   intro h
   exact one_ne_zero (congrFun h (some 0))

 theorem cubicOuterBubble_nonzero {A B : ℕ} (L S m p N : ℕ) (t δ : ℝ)
     (ε : ℂ) (z : CubicAmbient) :
     complexCartesian (cubicBubblePolynomial (A := A) (B := B) L S m p N t δ ε (firstBubbleLift z))≠0 := by
   intro h
   have he := complexCartesian.injective (h.trans (map_zero _).symm)
   have ho : outerPolynomial (A := A) (B := B) L S t δ (firstQuadricChart z)=0 := by
     ext i
     have hh := congrFun he (Sum.inl i)
     simpa only [cubicBubblePolynomial,bubblePolynomial,Sum.elim_inl,Function.comp_def,
       firstBubbleLift_coordinates,Pi.zero_apply] using hh
   apply outerPolynomial_nonzero (A := A) (B := B) L S t δ z
   rw [ho,map_zero]

 def cubicOuterBubblePrimitive {A B : ℕ} (L S m p N : ℕ) (t δ c : ℝ)
     (D : ℝ → ℝ) (ε : ℝ) : CubicAmbient → CubicAmbient →L[ℝ] ℝ :=
   (1-(L:ℝ)*D ε)•primitivePullback (hopfPrimitive c) (complexCartesian ∘ firstBubbleLift)+
     D ε•primitivePullback (hopfPrimitive c)
       (complexCartesian ∘ cubicBubblePolynomial (A := A) (B := B) L S m p N t δ ε ∘ firstBubbleLift)

 theorem cubicOuterBubble_joint_real_smooth {A B : ℕ} (L S m p N : ℕ) (t δ : ℝ) :
     ContDiff ℝ ∞ (fun a : ℝ×CubicAmbient =>
       cubicBubblePolynomial (A := A) (B := B) L S m p N t δ a.1 (firstBubbleLift a.2)) := by
   have hε : ContDiff ℝ ∞ (fun a : ℝ×CubicAmbient => (a.1:ℂ)) :=
     Complex.ofRealCLM.contDiff.comp contDiff_fst
   have hF : ContDiff ℝ ∞ (fun a : ℝ×CubicAmbient => firstBubbleLift a.2) :=
     (firstBubbleLift_smooth.restrict_scalars ℝ).comp contDiff_snd
   have hG : ContDiff ℝ ∞ (fun a : ℝ×CubicAmbient => bubbleCoordinates (a.1:ℂ) (firstBubbleLift a.2)) := by
     apply contDiff_pi.mpr
     rintro (_|i)
     · exact hε.mul ((contDiff_apply ℝ ℂ none).comp hF)
     · exact (contDiff_apply ℝ ℂ (some i)).comp hF
   apply contDiff_pi.mpr
   rintro (i|(j|k))
   · change ContDiff ℝ ∞ (fun a : ℝ×CubicAmbient =>
       outerPolynomial (A := A) (B := B) L S t δ (distinguishedHomogeneousCoordinates (firstBubbleLift a.2)) i)
     simp only [firstBubbleLift_coordinates]
     exact (contDiff_apply ℝ ℂ i).comp (((outerPolynomial_smooth (A := A) (B := B) L S t δ).restrict_scalars ℝ).comp
       ((firstQuadricChart_smooth.restrict_scalars ℝ).comp contDiff_snd))
   · change ContDiff ℝ ∞ (fun a : ℝ×CubicAmbient => (a.1:ℂ)^(p-m)*(firstBubbleLift a.2 none)^(L-m)*
       homogeneousVeronese m (bubbleCoordinates (a.1:ℂ) (firstBubbleLift a.2)) j)
     exact ((hε.pow _).mul (((contDiff_apply ℝ ℂ none).comp hF).pow _)).mul
       ((contDiff_apply ℝ ℂ j).comp (((homogeneousVeronese_smooth m).restrict_scalars ℝ).comp hG))
   · change ContDiff ℝ ∞ (fun a : ℝ×CubicAmbient => (a.1:ℂ)^N*homogeneousVeronese L (firstBubbleLift a.2) k)
     exact (hε.pow N).mul ((contDiff_apply ℝ ℂ k).comp
       (((homogeneousVeronese_smooth L).restrict_scalars ℝ).comp hF))

 theorem cubicOuterBubblePrimitive_joint_smooth {A B : ℕ} (L S m p N : ℕ) (t δ c : ℝ)
     {D : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) :
     ContDiff ℝ ∞ (fun a : ℝ×CubicAmbient =>
       cubicOuterBubblePrimitive (A := A) (B := B) L S m p N t δ c D a.1 a.2) := by
   have hF : ContDiff ℝ ∞ (fun a : ℝ×CubicAmbient => complexCartesian (firstBubbleLift a.2)) :=
     complexCartesian.contDiff.comp ((firstBubbleLift_smooth.restrict_scalars ℝ).comp contDiff_snd)
   have hQ := complexCartesian.contDiff.comp
     (cubicOuterBubble_joint_real_smooth (A := A) (B := B) L S m p N t δ)
   have hFn (a : ℝ×CubicAmbient) : complexCartesian (firstBubbleLift a.2)≠0 := by
     intro h
     exact firstBubbleLift_nonzero a.2 (complexCartesian.injective (h.trans (map_zero _).symm))
   exact (contDiff_const.sub (contDiff_const.mul (hD.comp contDiff_fst))).smul
     (fibrePrimitivePullback_smooth hF (fun a => hopfPrimitive_smoothAt c (hFn a))) |>.add
       ((hD.comp contDiff_fst).smul (fibrePrimitivePullback_smooth hQ
         (fun a => hopfPrimitive_smoothAt c (cubicOuterBubble_nonzero L S m p N t δ a.1 a.2))))

 theorem cubicOuterBubblePrimitive_smooth_family {A B : ℕ} (L S m p N : ℕ) (t δ c : ℝ)
     {D : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) :
     SmoothOneFormFamily (cubicOuterBubblePrimitive (A := A) (B := B) L S m p N t δ c D) := by
   intro x
   simpa only [vector_chartOneForm] using
     (cubicOuterBubblePrimitive_joint_smooth (A := A) (B := B) L S m p N t δ c hD).contDiffOn

 theorem cubicOuterBubblePrimitive_zero {A B L S m p N : ℕ} (hmp : m<p) (hN : 0<N)
     (t δ c : ℝ) {D : ℝ → ℝ} (hD : (L:ℝ)*D 0=1) :
     cubicOuterBubblePrimitive (A := A) (B := B) L S m p N t δ c D 0=
       outerAmbientPrimitive (A := A) (B := B) L S (D 0*c) t δ := by
   have he : (fun z => cubicBubblePolynomial (A := A) (B := B) L S m p N t δ (0:ℝ) (firstBubbleLift z))=
       (fun z => complexLeftBlock (ι := Fin m → Option (Fin 3)) (ν := Fin L → Option (Fin 3))
         (outerPolynomial (A := A) (B := B) L S t δ (firstQuadricChart z))) := by
     funext z
     ext i
     rcases i with (i|(j|k))
     · simp only [cubicBubblePolynomial,bubblePolynomial,Sum.elim_inl,Function.comp_def,
         firstBubbleLift_coordinates,complexLeftBlock]
     · simp only [cubicBubblePolynomial,bubblePolynomial,Sum.elim_inr,Sum.elim_inl,
         Complex.ofReal_zero,homogeneousBubble_zero hmp,Pi.zero_apply,complexLeftBlock]
     · simp [cubicBubblePolynomial,bubblePolynomial,complexLeftBlock,zero_pow hN.ne']
   unfold cubicOuterBubblePrimitive
   rw [hD,sub_self,zero_smul,zero_add]
   change D 0•primitivePullback (hopfPrimitive c) (fun z => complexCartesian
     (cubicBubblePolynomial (A := A) (B := B) L S m p N t δ (0:ℝ) (firstBubbleLift z)))=_
   simp_rw [congrFun he]
   erw [complexLeftBlock_primitive (((outerPolynomial_smooth (A := A) (B := B) L S t δ).restrict_scalars ℝ).comp
     (firstQuadricChart_smooth.restrict_scalars ℝ))]
   funext z
   apply ContinuousLinearMap.ext
   intro v
   simp only [Function.comp_def,Pi.smul_apply,smul_apply,smul_eq_mul,primitivePullback,outerAmbientPrimitive,
     ContinuousLinearMap.comp_apply,hopfPrimitive]
   ring

end PackingSufficiencySupport.CubicModel
end

end OAI
