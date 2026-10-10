import Mathlib
import OAI.Geometry.BallPacking.Hopf.AffineHopfRestriction

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function
section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

 def degreeHopfPrimitive (q : ℝ) (F : PlanePhase ι → PlanePhase κ) (c d : ℝ)
    : PlanePhase ι → PlanePhase ι →L[ℝ] ℝ :=
  (1-q*d)•hopfPrimitive c+d•primitivePullback (hopfPrimitive c) F

 def degreeHopfForm (q : ℝ) (F : PlanePhase ι → PlanePhase κ) (c d : ℝ) :=
  euclideanExteriorOneForm (degreeHopfPrimitive q F c d)

 def degreeConePrimitive (q : ℝ) (F : PlanePhase ι → PlanePhase κ) (c d : ℝ)
    (z : PlanePhase ι) : PlanePhase ι →L[ℝ] ℝ :=
  phaseSq z•degreeHopfPrimitive q F c d z

 theorem degreeHopfPrimitive_smoothAt {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0) (q c d : ℝ) :
    ContDiffAt ℝ ∞ (degreeHopfPrimitive q F c d) z :=
  ((hopfPrimitive_smoothAt c hz).const_smul (1-q*d)).add
    ((primitivePullback_smoothAt (hopfPrimitive_smoothAt c hFz) hF).const_smul d)

 theorem degreeHopfForm_eq {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0) (q c d : ℝ) :
    degreeHopfForm q F c d z=(1-q*d)•hopfForm c z+
      d•(hopfForm c (F z)).bilinearComp (fderiv ℝ F z) (fderiv ℝ F z) := by
  have h₀ := (hopfPrimitive_smoothAt c hz).differentiableAt (by simp)
  have h₁ := (primitivePullback_smoothAt (hopfPrimitive_smoothAt c hFz) hF).differentiableAt (by simp)
  rw [degreeHopfForm,degreeHopfPrimitive,euclideanExteriorOneForm_add (h₀.const_smul _) (h₁.const_smul _),
    euclideanExteriorOneForm_smul _ h₀,euclideanExteriorOneForm_smul _ h₁,
    primitivePullback_exteriorAt (hopfPrimitive_smoothAt c hFz) hF]
  rfl

 theorem degreeHopfPrimitive_circle {F : PlanePhase ι → PlanePhase κ} {z : PlanePhase ι}
    {q : ℝ} (hz : z≠0) (hFz : F z≠0)
    (hD : fderiv ℝ F z (phaseJ z)=q•phaseJ (F z)) (c d : ℝ) :
    degreeHopfPrimitive q F c d z (phaseJ z)=c/2 := by
  simp only [degreeHopfPrimitive,Pi.add_apply,Pi.smul_apply,add_apply,smul_apply,
    smul_eq_mul,primitivePullback,ContinuousLinearMap.comp_apply,hD,map_smul,
    hopfPrimitive_circle c hz,hopfPrimitive_circle c hFz]
  ring

 theorem degreeHopfForm_radial {F : PlanePhase ι → PlanePhase κ} {z : PlanePhase ι}
    {q : ℝ} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0)
    (hD : fderiv ℝ F z z=q•F z) (c d : ℝ) (v : PlanePhase ι) :
    degreeHopfForm q F c d z z v=0 := by
  rw [degreeHopfForm_eq hF hz hFz]
  simp only [add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.bilinearComp_apply,hD,
    map_smul,hopfForm_radial c hz,hopfForm_radial c hFz,mul_zero,add_zero]

 theorem degreeHopfForm_circle {F : PlanePhase ι → PlanePhase κ} {z : PlanePhase ι}
    {q : ℝ} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0)
    (hD : fderiv ℝ F z (phaseJ z)=q•phaseJ (F z)) (c d : ℝ) (v : PlanePhase ι) :
    degreeHopfForm q F c d z (phaseJ z) v=0 := by
  rw [degreeHopfForm_eq hF hz hFz]
  simp only [add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.bilinearComp_apply,hD,
    map_smul,hopfForm_circle c hz,hopfForm_circle c hFz,mul_zero,add_zero]

 theorem degreeHopfForm_skew (q : ℝ) (F : PlanePhase ι → PlanePhase κ) (c d : ℝ)
    (z v w : PlanePhase ι) : degreeHopfForm q F c d z v w= -degreeHopfForm q F c d z w v := by
  simp only [degreeHopfForm,euclideanExteriorOneForm,sub_apply,ContinuousLinearMap.flip_apply]
  ring

 theorem degreeHopfForm_horizontal_positive {F : PlanePhase ι → PlanePhase κ} {z : PlanePhase ι}
    (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0)
    (hJ : ∀ v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v))
    {q c d : ℝ} (hc : 0<c) (hd : 0≤d) (hdq : q*d<1)
    {v : PlanePhase ι} (hdv : phaseDot z v=0) (hav : phaseArea z v=0) (hv : v≠0) :
    0 < degreeHopfForm q F c d z v (phaseJ v) := by
  rw [degreeHopfForm_eq hF hz hFz]
  simp only [add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.bilinearComp_apply,hJ]
  have hp : 0<hopfForm c z v (phaseJ v) := by
    rw [hopfForm_complex_diagonal c hz,hdv,hav]
    simp only [zero_pow (by norm_num : 2≠0),zero_add,sub_zero]
    exact mul_pos (div_pos hc (sq_pos_of_pos (phaseSq_pos hz)))
      (mul_pos (phaseSq_pos hz) (phaseSq_pos hv))
  exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) hp)
    (mul_nonneg hd (hopfForm_semipositive hc.le hFz _))

 theorem degreeConePrimitive_exterior {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0) (q c d : ℝ) :
    euclideanExteriorOneForm (degreeConePrimitive q F c d) z=
      radialSymplectization z (degreeHopfPrimitive q F c d z) (degreeHopfForm q F c d z) := by
  have ha := (degreeHopfPrimitive_smoothAt hF hz hFz q c d).differentiableAt (by simp)
  have he := (phaseSq_hasFDerivAt z).smul ha.hasFDerivAt
  rw [euclideanExteriorOneForm,show fderiv ℝ (degreeConePrimitive q F c d) z=_ from he.fderiv]
  ext v w
  simp only [sub_apply,ContinuousLinearMap.flip_apply,add_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul,radialSymplectization_apply,
    degreeHopfForm,euclideanExteriorOneForm]
  ring

 theorem degreeConePrimitive_nondegenerate {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} {q : ℝ} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0)
    (hD : fderiv ℝ F z z=q•F z)
    (hJ : ∀ v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v))
    {c d : ℝ} (hc : 0<c) (hd : 0≤d) (hdq : q*d<1) :
    (euclideanExteriorOneForm (degreeConePrimitive q F c d) z).IsInvertible := by
  have hDJ : fderiv ℝ F z (phaseJ z)=q•phaseJ (F z) := by rw [hJ,hD,map_smul]
  rw [degreeConePrimitive_exterior hF hz hFz]
  apply radialSymplectization_nondegenerate hz _ _ (half_pos hc)
    (degreeHopfPrimitive_circle hz hFz hDJ c d)
  · intro v
    rw [degreeHopfForm_skew,degreeHopfForm_radial hF hz hFz hD,neg_zero]
  · intro v
    rw [degreeHopfForm_skew,degreeHopfForm_circle hF hz hFz hDJ,neg_zero]
  · exact degreeHopfForm_circle hF hz hFz hDJ c d
  · intro v hdv hav hv
    exact degreeHopfForm_horizontal_positive hF hz hFz hJ hc hd hdq hdv hav hv

 theorem degreeConePrimitive_circle_contraction {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} {q : ℝ} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0)
    (hDJ : fderiv ℝ F z (phaseJ z)=q•phaseJ (F z)) (c d : ℝ) (v : PlanePhase ι) :
    euclideanExteriorOneForm (degreeConePrimitive q F c d) z v (phaseJ z)=c*phaseDot z v := by
  rw [degreeConePrimitive_exterior hF hz hFz,
    radialSymplectization_circle z _ _ (degreeHopfPrimitive_circle hz hFz hDJ c d)
      (fun v => by rw [degreeHopfForm_skew,degreeHopfForm_circle hF hz hFz hDJ,neg_zero])]
  ring

 theorem degreeConePrimitive_smoothAt {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0) (q c d : ℝ) :
    ContDiffAt ℝ ∞ (degreeConePrimitive q F c d) z :=
  phaseSq_smooth.contDiffAt.smul (degreeHopfPrimitive_smoothAt hF hz hFz q c d)

 theorem degreeConePrimitive_affine (q : ℝ) (F : PlanePhase ι → PlanePhase κ)
    (c d s : ℝ) (z : PlanePhase ι) :
    (1-s)•degreeConePrimitive q F c 0 z+s•degreeConePrimitive q F c d z=
      degreeConePrimitive q F c (s*d) z := by
  ext v
  simp only [degreeConePrimitive,degreeHopfPrimitive,Pi.add_apply,Pi.smul_apply,
    add_apply,smul_apply,smul_eq_mul]
  ring

 theorem degreeConePrimitive_circle {F : PlanePhase ι → PlanePhase κ} {z : PlanePhase ι}
    {q : ℝ} (hz : z≠0) (hFz : F z≠0)
    (hD : fderiv ℝ F z (phaseJ z)=q•phaseJ (F z)) (c d : ℝ) :
    degreeConePrimitive q F c d z (phaseJ z)=phaseSq z*(c/2) := by
  simp only [degreeConePrimitive,smul_apply,smul_eq_mul,degreeHopfPrimitive_circle hz hFz hD c d]

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {q : ℝ} {ℓ : ℕ}

def degreeHopfCurvaturePullback (q : ℝ) (P : (ι → ℂ) → (κ → ℂ)) (c d : ℝ)
    (G : E → (ι → ℂ)) (x : E) (v w : E) : ℝ :=
  (1-q*d)*hopfCurvaturePullback c G x v w+
    d*hopfCurvaturePullback c (fun y => P (G y)) x v w

theorem degreeHopfCurvaturePullback_gauge {P : (ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) (hPn : ∀ z,z≠0 → P z≠0)
    (hPs : ∀ (ζ : ℂ) z,P (ζ•z)=ζ^ℓ•P z)
    {S : E → ℂ} {G : E → (ι → ℂ)} {x : E}
    (hS : DifferentiableAt ℝ S x) (hG : DifferentiableAt ℝ G x)
    (hSx : S x≠0) (hGx : G x≠0) (c d : ℝ) (v w : E) :
    degreeHopfCurvaturePullback q P c d (fun y => S y•G y) x v w=
      degreeHopfCurvaturePullback q P c d G x v w := by
  have hGxc : complexCartesian (G x)≠0 := by
    intro h; exact hGx (complexCartesian.injective (h.trans (map_zero _).symm))
  have hPGxc : complexCartesian (P (G x))≠0 := by
    intro h; exact hPn (G x) hGx (complexCartesian.injective (h.trans (map_zero _).symm))
  have he : (fun y => P (S y•G y))=(fun y => (S y)^ℓ•P (G y)) := funext fun y => hPs _ _
  unfold degreeHopfCurvaturePullback
  change (1-q*d)*hopfCurvaturePullback c (fun y => S y•G y) x v w+
    d*hopfCurvaturePullback c (fun y => P (S y•G y)) x v w=_
  rw [he]
  unfold hopfCurvaturePullback
  rw [hopfForm_variable_gauge hS hG hSx hGxc]
  have h₂ := hopfForm_variable_gauge (S := fun y => S y^ℓ) (G := fun y => P (G y))
    (hS.pow ℓ) ((hP.differentiable (by simp) (G x)).comp x hG)
      (pow_ne_zero ℓ hSx) hPGxc c v w
  exact congrArg (fun u : ℝ => (1-q*d)*hopfCurvaturePullback c G x v w+d*u) h₂

theorem degreeHopfCurvaturePullback_eq {P : (ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) {G : E → (ι → ℂ)} {x : E}
    (hG : DifferentiableAt ℝ G x) (hGx : G x≠0) (hPGx : P (G x)≠0)
    (c d : ℝ) (v w : E) :
    degreeHopfCurvaturePullback q P c d G x v w=
      degreeHopfForm q (cartesianConjugate P) c d (complexCartesian (G x))
        (fderiv ℝ (fun y => complexCartesian (G y)) x v)
        (fderiv ℝ (fun y => complexCartesian (G y)) x w) := by
  have hz : complexCartesian (G x)≠0 := by
    intro h; exact hGx (complexCartesian.injective (h.trans (map_zero _).symm))
  have hPz : cartesianConjugate P (complexCartesian (G x))≠0 := by
    rw [cartesianConjugate_cartesian]
    intro h; exact hPGx (complexCartesian.injective (h.trans (map_zero _).symm))
  have hGc := complexCartesian.differentiableAt.comp x hG
  have hPc := (cartesianConjugate_smooth hP).differentiable (by simp) (complexCartesian (G x))
  have he : (fun y => cartesianConjugate P (complexCartesian (G y)))=
      (fun y => complexCartesian (P (G y))) := funext fun y => cartesianConjugate_cartesian P (G y)
  have hD (u : E) : fderiv ℝ (fun y => complexCartesian (P (G y))) x u=
      fderiv ℝ (cartesianConjugate P) (complexCartesian (G x))
        (fderiv ℝ (fun y => complexCartesian (G y)) x u) := by
    rw [←he]
    exact congrArg (fun L => L u) (fderiv_comp x hPc hGc)
  rw [degreeHopfForm_eq (cartesianConjugate_smooth hP).contDiffAt hz hPz]
  simp only [add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.bilinearComp_apply,
    cartesianConjugate_cartesian,degreeHopfCurvaturePullback,hopfCurvaturePullback,hD]

theorem hopfCurvaturePullback_comp {G : E' → (ι → ℂ)} {H : E → E'} {x : E}
    (hG : DifferentiableAt ℝ G (H x)) (hH : DifferentiableAt ℝ H x)
    (c : ℝ) (v w : E) :
    hopfCurvaturePullback c (fun y => G (H y)) x v w=
      hopfCurvaturePullback c G (H x) (fderiv ℝ H x v) (fderiv ℝ H x w) := by
  unfold hopfCurvaturePullback
  have hD (u : E) : fderiv ℝ (fun y => complexCartesian (G (H y))) x u=
      fderiv ℝ (fun y => complexCartesian (G y)) (H x) (fderiv ℝ H x u) :=
    congrArg (fun L => L u) (fderiv_comp x (complexCartesian.differentiableAt.comp (H x) hG) hH)
  rw [hD,hD]

theorem mixedHopfCurvaturePullback_comp {P : (ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) {G : E' → (ι → ℂ)} {H : E → E'} {x : E}
    (hG : DifferentiableAt ℝ G (H x)) (hH : DifferentiableAt ℝ H x)
    (c d : ℝ) (v w : E) :
    mixedHopfCurvaturePullback P c d (fun y => G (H y)) x v w=
      mixedHopfCurvaturePullback P c d G (H x) (fderiv ℝ H x v) (fderiv ℝ H x w) := by
  unfold mixedHopfCurvaturePullback
  rw [hopfCurvaturePullback_comp hG hH]
  have h₂ := hopfCurvaturePullback_comp (G := fun y => P (G y))
    ((hP.differentiable (by simp) _).comp (H x) hG) hH c v w
  exact congrArg (fun q : ℝ => (1-2*d)*hopfCurvaturePullback c G (H x)
    (fderiv ℝ H x v) (fderiv ℝ H x w)+d*q) h₂

end

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']

 def degreeAffineForm (q : ℝ) (P : (Option ι → ℂ) → (κ → ℂ)) (c d : ℝ) (x : ι → ℂ) :
    (ι → ℂ) →L[ℝ] (ι → ℂ) →L[ℝ] ℝ :=
  (1-q*d)•(hopfForm c (complexCartesian (complexAffineLift x))).bilinearComp
    (fderiv ℝ (fun y => complexCartesian (complexAffineLift y)) x)
    (fderiv ℝ (fun y => complexCartesian (complexAffineLift y)) x)+
  d•(hopfForm c (complexCartesian (P (complexAffineLift x)))).bilinearComp
    (fderiv ℝ (fun y => complexCartesian (P (complexAffineLift y))) x)
    (fderiv ℝ (fun y => complexCartesian (P (complexAffineLift y))) x)

 theorem degreeAffineForm_apply (q : ℝ) (P : (Option ι → ℂ) → (κ → ℂ)) (c d : ℝ)
    (x v w : ι → ℂ) : degreeAffineForm q P c d x v w=
      degreeHopfCurvaturePullback q P c d complexAffineLift x v w := rfl

 theorem degreeHopfCurvaturePullback_comp {P : (ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) {G : E' → (ι → ℂ)} {H : E → E'} {x : E}
    (hG : DifferentiableAt ℝ G (H x)) (hH : DifferentiableAt ℝ H x)
    (q c d : ℝ) (v w : E) :
    degreeHopfCurvaturePullback q P c d (fun y => G (H y)) x v w=
      degreeHopfCurvaturePullback q P c d G (H x) (fderiv ℝ H x v) (fderiv ℝ H x w) := by
  unfold degreeHopfCurvaturePullback
  rw [hopfCurvaturePullback_comp hG hH]
  have h₂ := hopfCurvaturePullback_comp (G := fun y => P (G y))
    ((hP.differentiable (by simp) _).comp (H x) hG) hH c v w
  exact congrArg (fun u : ℝ => (1-q*d)*hopfCurvaturePullback c G (H x)
    (fderiv ℝ H x v) (fderiv ℝ H x w)+d*u) h₂

 theorem degreeAffineForm_pullback {P : (Option ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) {f : E → (ι → ℂ)} {x : E} (hf : DifferentiableAt ℝ f x)
    (q c d : ℝ) (v w : E) :
    degreeAffineForm q P c d (f x) (fderiv ℝ f x v) (fderiv ℝ f x w)=
      degreeHopfCurvaturePullback q P c d (fun y => complexAffineLift (f y)) x v w := by
  rw [degreeAffineForm_apply]
  exact (degreeHopfCurvaturePullback_comp hP (complexAffineLift_smooth.differentiable (by simp) _) hf q c d v w).symm

 theorem degreeAffineForm_zero (q : ℝ) (P : (Option ι → ℂ) → (κ → ℂ)) (c : ℝ)
    (x v w : ι → ℂ) : degreeAffineForm q P c 0 x v w=
      affineFSForm c (complexCartesian x) (complexCartesian v) (complexCartesian w) := by
  rw [degreeAffineForm_apply]
  simp only [degreeHopfCurvaturePullback,mul_zero,sub_zero,one_mul,zero_mul,add_zero]
  simpa only [hopfCurvaturePullback,fderiv_id,ContinuousLinearMap.id_apply,Function.id_def,ContinuousLinearEquiv.fderiv,
    ContinuousLinearEquiv.coe_coe] using hopfForm_affine_pullback (ι := ι) (Z := id)
      (x := x) differentiableAt_id c v w

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 def cubicBubblePrimitive {A B : ℕ} (L S m p N : ℕ) (t δ c d ε : ℝ) :
     (Fin 3 → ℂ) → (Fin 3 → ℂ) →L[ℝ] ℝ :=
   (1-(L:ℝ)*d)•primitivePullback (affineFSPrimitive c)
     (fun z => complexCartesian ((ε:ℂ)•z))+
   d•primitivePullback (hopfPrimitive c)
     (fun z => complexCartesian (cubicBubbleResidual (A := A) (B := B) L S m p N t δ ε z))

 theorem distinguishedResidualTerm_real_smooth (p n k J K : ℕ) :
     ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) => distinguishedResidualTerm p n k J K a.1 a.2) := by
   have hε : ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) => (a.1:ℂ)) :=
     Complex.ofRealCLM.contDiff.comp contDiff_fst
   have hz (i : Fin 3) : ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) => a.2 i) :=
     (contDiff_apply ℝ ℂ i).comp contDiff_snd
   unfold distinguishedResidualTerm
   exact (((hε.pow _).mul (((hz 0).sub ((hε.mul (hz 1)).mul (hz 2))).pow _)).mul
     ((hz 0).pow _ ) |>.mul ((hz 1).pow _)).mul ((hz 2).pow _)

 theorem distinguishedResidualPolynomial_real_smooth {A B : ℕ} (p L S : ℕ) (t δ : ℝ) :
     ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) => distinguishedResidualPolynomial (A := A) (B := B) p L S t δ a.1 a.2) := by
   apply contDiff_pi.mpr
   intro ki
   exact contDiff_const.mul (ContDiff.sum (fun _ _ => contDiff_const.mul
     (distinguishedResidualTerm_real_smooth _ _ _ _ _)))

 theorem cubicBubbleResidual_real_smooth {A B : ℕ} (L S m p N : ℕ) (t δ : ℝ) :
     ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) =>
       cubicBubbleResidual (A := A) (B := B) L S m p N t δ a.1 a.2) := by
   apply contDiff_pi.mpr
   rintro (i|(j|k))
   · change ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) => distinguishedResidualPolynomial p L S t δ a.1 a.2 i)
     exact (contDiff_apply ℝ ℂ i).comp (distinguishedResidualPolynomial_real_smooth (A := A) (B := B) p L S t δ)
   · change ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) => homogeneousVeronese m (complexAffineLift a.2) j)
     exact (contDiff_apply ℝ ℂ j).comp (((homogeneousVeronese_smooth m).restrict_scalars ℝ).comp
       (complexAffineLift_smooth.comp contDiff_snd))
   · change ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) => (a.1:ℂ)^(N-p)*homogeneousVeronese L (complexAffineLift ((a.1:ℂ)•a.2)) k)
     have hs : ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) => (a.1:ℂ)•a.2) :=
       (Complex.ofRealCLM.contDiff.comp contDiff_fst).smul contDiff_snd
     exact ((Complex.ofRealCLM.contDiff.comp contDiff_fst).pow (N-p)).mul
       ((contDiff_apply ℝ ℂ k).comp (((homogeneousVeronese_smooth L).restrict_scalars ℝ).comp
         (complexAffineLift_smooth.comp hs)))

 theorem cubicBubblePrimitive_joint_smooth {A B : ℕ} (L S m p N : ℕ) (t δ c d : ℝ) :
     ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) => cubicBubblePrimitive (A := A) (B := B) L S m p N t δ c d a.1 a.2) := by
   have hF : ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) => complexCartesian ((a.1:ℂ)•a.2)) :=
     (complexCartesian (ι := Fin 3)).contDiff.comp
       (show ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) => (a.1:ℂ)•a.2) from
         (Complex.ofRealCLM.contDiff.comp contDiff_fst).smul contDiff_snd)
   have hQ := complexCartesian.contDiff.comp (cubicBubbleResidual_real_smooth (A := A) (B := B) L S m p N t δ)
   have hn (a : ℝ×(Fin 3 → ℂ)) :
       complexCartesian (cubicBubbleResidual (A := A) (B := B) L S m p N t δ a.1 a.2)≠0 := by
     intro h
     exact cubicBubbleResidual_nonzero L S m p N t δ _ _
       (complexCartesian.injective (h.trans (map_zero _).symm))
   exact ((fibrePrimitivePullback_smooth hF (fun _ => (affineFSPrimitive_smooth c).contDiffAt)).const_smul (1-(L:ℝ)*d)).add
     ((fibrePrimitivePullback_smooth hQ (fun a => hopfPrimitive_smoothAt c (hn a))).const_smul d)

 theorem cubicBubblePrimitive_smooth_family {A B : ℕ} (L S m p N : ℕ) (t δ c d : ℝ) :
     SmoothOneFormFamily (cubicBubblePrimitive (A := A) (B := B) L S m p N t δ c d) := by
   intro x
   simpa only [vector_chartOneForm] using
     (cubicBubblePrimitive_joint_smooth (A := A) (B := B) L S m p N t δ c d).contDiffOn

 theorem cubicBubblePrimitive_zero {L S A B p N : ℕ} (m : ℕ)
     (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hp : p<L-S) (hN : p<N)
     (t δ c d : ℝ) :
     cubicBubblePrimitive (A := A) (B := B) L S (m+1) p N t δ c d 0=
       d•primitivePullback (affineFSPrimitive ((m+1:ℕ)*c)) complexCartesian := by
   have he : (fun z => complexCartesian (cubicBubbleResidual (A := A) (B := B) L S (m+1) p N t δ (0:ℝ) z))=
       (fun z => complexCartesian (complexMiddleBlock
         (homogeneousVeronese (m+1) (complexAffineLift z)))) := by
     funext z
     rw [Complex.ofReal_zero,cubicBubbleResidual_zero hAS hS hB hp hN]
     rfl
   have hF : ContDiff ℝ ∞ (fun z : Fin 3 → ℂ => homogeneousVeronese (m+1) (complexAffineLift z)) :=
     ((homogeneousVeronese_smooth (m+1)).restrict_scalars ℝ).comp complexAffineLift_smooth
   unfold cubicBubblePrimitive
   rw [he,complexMiddleBlock_primitive hF,homogeneousVeronese_affinePrimitive]
   have hz : primitivePullback (affineFSPrimitive (ι := Fin 3) c)
       (fun _ : Fin 3 → ℂ => (0 : PlanePhase (Fin 3)))=0 := by
     ext x v
     simp [primitivePullback]
   simp only [Complex.ofReal_zero,zero_smul,map_zero,hz,smul_zero,zero_add]

 theorem cubicBubblePrimitive_zero_exterior {L S A B p N : ℕ} (m : ℕ)
     (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hp : p<L-S) (hN : p<N)
     (t δ c d : ℝ) (z v w : Fin 3 → ℂ) :
     manifoldExteriorOneForm (cubicBubblePrimitive (A := A) (B := B) L S (m+1) p N t δ c d 0) z v w=
       d*affineFSForm ((m+1:ℕ)*c) (complexCartesian z) (complexCartesian v) (complexCartesian w) := by
   rw [cubicBubblePrimitive_zero m hAS hS hB hp hN,vector_exteriorOneForm,
     euclideanExteriorOneForm_smul d ((primitivePullback_smooth (affineFSPrimitive_smooth ((m+1:ℕ)*c))
       (complexCartesian (ι := Fin 3)).contDiff).differentiable (by simp) z),
     primitivePullback_exterior (affineFSPrimitive_smooth ((m+1:ℕ)*c)) (complexCartesian (ι := Fin 3)).contDiff,←affineFSForm_eq_exterior]
   simp only [smul_apply,smul_eq_mul,ContinuousLinearMap.bilinearComp_apply,
     ContinuousLinearEquiv.fderiv,ContinuousLinearEquiv.coe_coe]

 theorem cubicBubblePrimitive_zero_invertible {L S A B p N : ℕ} (m : ℕ)
     (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hp : p<L-S) (hN : p<N)
     (t δ : ℝ) {c d : ℝ} (hc : 0<c) (hd : 0<d) (z : Fin 3 → ℂ) :
     (manifoldExteriorOneForm (cubicBubblePrimitive (A := A) (B := B) L S (m+1) p N t δ c d 0) z).IsInvertible := by
   apply bilinear_isInvertible_of_taming (J := fun v => complexCartesian.symm (phaseJ (complexCartesian v)))
   intro v hv
   rw [cubicBubblePrimitive_zero_exterior m hAS hS hB hp hN,
     ContinuousLinearEquiv.apply_symm_apply]
   apply mul_pos hd
   apply affineFSForm_positive (mul_pos (by positivity) hc)
   intro he
   apply hv
   exact complexCartesian.injective (he.trans (map_zero _).symm)

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem residualPrimitive_exterior {F : E → (ι → ℂ)} {Q : E → (κ → ℂ)}
    (hF : ContDiff ℝ ∞ F) (hQ : ContDiff ℝ ∞ Q) {z : E}
    (hn : complexCartesian (Q z)≠0) (a c d : ℝ) (v w : E) :
    euclideanExteriorOneForm (a•primitivePullback (affineFSPrimitive c) (fun y => complexCartesian (F y))+
      d•primitivePullback (hopfPrimitive c) (fun y => complexCartesian (Q y))) z v w=
      a*affineFSForm c (complexCartesian (F z))
        (fderiv ℝ (fun y => complexCartesian (F y)) z v)
        (fderiv ℝ (fun y => complexCartesian (F y)) z w)+
      d*hopfCurvaturePullback c Q z v w := by
   have hFC := complexCartesian.contDiff.comp hF
   have hQC := complexCartesian.contDiff.comp hQ
   have hα := primitivePullback_smooth (affineFSPrimitive_smooth c) hFC
   have hβ := primitivePullback_smoothAt (g := fun y => complexCartesian (Q y)) (hopfPrimitive_smoothAt c hn) hQC.contDiffAt
   change euclideanExteriorOneForm (a•primitivePullback (affineFSPrimitive (ι := ι) c)
     (complexCartesian ∘ F)+d•primitivePullback (hopfPrimitive (ι := κ) c) (complexCartesian ∘ Q)) z v w=_
   erw [euclideanExteriorOneForm_add ((hα.differentiable (by simp) z).const_smul a)
       ((hβ.differentiableAt (by simp)).const_smul d),
     euclideanExteriorOneForm_smul a (hα.differentiable (by simp) z),
     euclideanExteriorOneForm_smul d (hβ.differentiableAt (by simp)),
     primitivePullback_exterior (affineFSPrimitive_smooth c) hFC,
     primitivePullback_exteriorAt (g := fun y => complexCartesian (Q y)) (hopfPrimitive_smoothAt c hn) hQC.contDiffAt,
     ←affineFSForm_eq_exterior]
   rfl

 theorem residual_degreeAffineForm {P : (Option ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) {F : E → (ι → ℂ)} {Q : E → (κ → ℂ)}
    (hF : ContDiff ℝ ∞ F) (hQ : ContDiff ℝ ∞ Q) {ζ : ℂ} (hζ : ζ≠0)
    (he : (fun y => P (complexAffineLift (F y)))=(fun y => ζ•Q y))
    {z : E} (hn : complexCartesian (Q z)≠0) (q c d : ℝ) (v w : E) :
    degreeAffineForm q P c d (F z) (fderiv ℝ F z v) (fderiv ℝ F z w)=
      (1-q*d)*affineFSForm c (complexCartesian (F z))
        (fderiv ℝ (fun y => complexCartesian (F y)) z v)
        (fderiv ℝ (fun y => complexCartesian (F y)) z w)+
      d*hopfCurvaturePullback c Q z v w := by
   rw [degreeAffineForm_pullback hP (hF.differentiable (by simp) z)]
   unfold degreeHopfCurvaturePullback
   have ha := hopfForm_affine_pullback (hF.differentiable (by simp) z) c v w
   change hopfCurvaturePullback c (fun y => complexAffineLift (F y)) z v w=_ at ha
   rw [ha,he]
   exact congrArg (fun r : ℝ => (1-q*d)*affineFSForm c (complexCartesian (F z))
     (fderiv ℝ (fun y => complexCartesian (F y)) z v)
     (fderiv ℝ (fun y => complexCartesian (F y)) z w)+d*r)
       (hopfForm_variable_gauge (S := fun _ : E => ζ) (differentiableAt_const ζ)
         (hQ.differentiable (by simp) z) hζ hn c v w)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 theorem cubicBubblePolynomial_real_smooth {L S A B m p N : ℕ} (t δ ε : ℝ) :
     ContDiff ℝ ∞ (cubicBubblePolynomial (A := A) (B := B) L S m p N t δ ε) := by
   exact ((cubicBubblePolynomial_joint_smooth L S m p N t δ).comp
       (contDiff_const.prodMk contDiff_id)).restrict_scalars ℝ

 theorem cubicBubbleResidual_fixed_real_smooth {L S A B m p N : ℕ} (t δ ε : ℝ) :
     ContDiff ℝ ∞ (cubicBubbleResidual (A := A) (B := B) L S m p N t δ ε) := by
   exact (cubicBubbleResidual_real_smooth (A := A) (B := B) L S m p N t δ).comp
     (f := fun y : Fin 3 → ℂ => (ε,y)) (contDiff_const.prodMk contDiff_id)

 theorem cubicBubblePrimitive_curvature {L S A B m p N : ℕ}
     (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hp : p≤L-S)
     (hm : m≤p) (hN : p≤N) (t δ c d : ℝ) {ε : ℝ} (hε : ε≠0)
     (z v w : Fin 3 → ℂ) :
     manifoldExteriorOneForm (cubicBubblePrimitive (A := A) (B := B) L S m p N t δ c d ε) z v w=
       degreeAffineForm (L:ℝ) (cubicBubblePolynomial (A := A) (B := B) L S m p N t δ ε) c d
         ((ε:ℂ)•z) (fderiv ℝ (fun y : Fin 3 → ℂ => (ε:ℂ)•y) z v)
           (fderiv ℝ (fun y : Fin 3 → ℂ => (ε:ℂ)•y) z w) := by
   have hscale : ContDiff ℝ ∞ (fun y : Fin 3 → ℂ => (ε:ℂ)•y) := (contDiff_const (c := (ε:ℂ))).smul (contDiff_id (𝕜 := ℝ) (E := Fin 3 → ℂ))
   have hP : ContDiff ℝ ∞ (cubicBubblePolynomial (A := A) (B := B) L S m p N t δ ε) :=
     cubicBubblePolynomial_real_smooth t δ ε
   have hQ : ContDiff ℝ ∞ (cubicBubbleResidual (A := A) (B := B) L S m p N t δ ε) :=
     cubicBubbleResidual_fixed_real_smooth t δ ε
   have hn : complexCartesian (cubicBubbleResidual (A := A) (B := B) L S m p N t δ ε z)≠0 := by
     intro he
     exact cubicBubbleResidual_nonzero L S m p N t δ _ _
       (complexCartesian.injective (he.trans (map_zero _).symm))
   have he : (fun y => cubicBubblePolynomial (A := A) (B := B) L S m p N t δ ε
       (complexAffineLift ((ε:ℂ)•y)))=
       (fun y => (ε:ℂ)^p•cubicBubbleResidual L S m p N t δ ε y) := by
     funext y
     exact cubicBubblePolynomial_scaled hAS hS hB hp hm hN t δ ε y
   rw [vector_exteriorOneForm,cubicBubblePrimitive]
   exact (residualPrimitive_exterior hscale hQ hn (1-(L:ℝ)*d) c d v w).trans
     (residual_degreeAffineForm hP hscale hQ
       (pow_ne_zero p (Complex.ofReal_ne_zero.mpr hε)) he hn (L:ℝ) c d v w).symm

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N]

 theorem exists_uniform_compact_exact_fibre_embedding_into {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) {K : Set M} (hK : IsCompact K)
    (hinv : ∀ x∈K,(manifoldExteriorOneForm (Γ 0) x).IsInvertible)
    {U : Set M} (hU : IsOpen U) (hKU : K⊆U)
    {δ : ℝ} (hδ : 0<δ) {A : ℝ × M → N}
    (hA : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,F) ∞ A)
    (hemb : ∀ t∈Ioc (0:ℝ) δ,Topology.IsEmbedding (fun x : U => A (t,x.val)))
    {T : Set N} (hinto : ∀ t∈Ioc (0:ℝ) δ,MapsTo (fun x => A (t,x)) U T)
    (Ω : ℝ → ManifoldTwoForm F N)
    (hform : ∀ t∈Ioc (0:ℝ) δ,∀ x∈U,
      manifoldExteriorOneForm (Γ t) x=(Ω t (A (t,x))).bilinearComp
        (manifoldMapDifferential (E := F) (F := E) (fun y => A (t,y)) x)
        (manifoldMapDifferential (E := F) (F := E) (fun y => A (t,y)) x)) :
    ∃ η>0,η≤δ ∧ ∀ t∈Ioc (0:ℝ) η,∃ g : M → N,∃ W : Set M,IsOpen W ∧ K⊆W ∧
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ g ∧ Topology.IsEmbedding (fun x : W => g x.val) ∧
      MapsTo g W T ∧ ∀ x∈W,∀ v w,Ω t (g x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) g x v)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) g x w)=manifoldExteriorOneForm (Γ 0) x v w := by
  obtain ⟨ε,hε,_hε1,V,hV,hKV,Φ,Ψ,hΦ,hΨ,hΦ0,hΦinv,hΦform⟩ :=
    exists_compact_short_exact_moser hΓ hK hinv
  have hS : IsOpen {p : ℝ × M | p.2∈V ∧ Φ p∈U} :=
    (hV.preimage continuous_snd).inter (hU.preimage hΦ.continuous)
  have hKS : ({0}:Set ℝ)×ˢK⊆{p : ℝ × M | p.2∈V ∧ Φ p∈U} := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    rcases ht with rfl
    exact ⟨hKV hx,by simpa only [hΦ0] using hKU hx⟩
  obtain ⟨T,W,hT,hW,h0T,hKW,hTW⟩ := generalized_tube_lemma isCompact_singleton hK hS hKS
  obtain ⟨η,hη,hηT⟩ := Metric.isOpen_iff.mp hT 0 (h0T (mem_singleton 0))
  let τ : ℝ := min (η/2) (min ε δ)
  have hτ : 0<τ := lt_min (by positivity) (lt_min hε hδ)
  have hτδ : τ≤δ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨τ,hτ,hτδ,?_⟩
  intro t ht'
  have ht : 0<t := ht'.1
  have htη : t≤η/2 := ht'.2.trans (min_le_left _ _)
  have htε : t≤ε := ht'.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have htδ : t≤δ := ht'.2.trans hτδ
  have htT : t∈T := hηT (by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht]
    linarith)
  have hstay (x : M) (hx : x∈W) : x∈V ∧ Φ (t,x)∈U :=
    hTW (show (t,x)∈T×ˢW from ⟨htT,hx⟩)
  have hφ := hΦ.comp (contMDiff_const.prodMk contMDiff_id) (f := fun x : M => (t,x))
  have hψ := hΨ.comp (contMDiff_const.prodMk contMDiff_id) (f := fun x : M => (t,x))
  have hφemb : Topology.IsEmbedding (fun x : M => Φ (t,x)) := by
    apply Topology.IsEmbedding.of_comp hφ.continuous hψ.continuous
    have he : (fun x : M => Ψ (t,Φ (t,x)))=id := funext fun x => (hΦinv t ⟨ht.le,htε⟩ x).1
    change Topology.IsEmbedding (fun x : M => Ψ (t,Φ (t,x)))
    rw [he]
    exact Topology.IsEmbedding.id
  have ha := hA.comp (contMDiff_const.prodMk contMDiff_id) (f := fun x : M => (t,x))
  let g : M → N := (fun x => A (t,x)) ∘ (fun x => Φ (t,x))
  refine ⟨g,W,hW,hKW,ha.comp hφ,?_,?_,?_⟩
  · exact (hemb t ⟨ht,htδ⟩).comp
      ((hφemb.comp Topology.IsEmbedding.subtypeVal).codRestrict U (fun x : W => (hstay x.val x.property).2))
  · intro x hx
    exact hinto t ⟨ht,htδ⟩ (hstay x hx).2
  · intro x hx v w
    have hd := mfderiv_comp x (ha.mdifferentiable (by simp) (Φ (t,x)))
      (hφ.mdifferentiable (by simp) x)
    change Ω t (A (t,Φ (t,x))) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) g x v)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) g x w)=_
    change Ω t (A (t,Φ (t,x)))
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) ((A ∘ fun y => (t,y)) ∘ (Φ ∘ fun y => (t,y))) x v)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) ((A ∘ fun y => (t,y)) ∘ (Φ ∘ fun y => (t,y))) x w)=_
    rw [hd]
    have hf := congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ =>
      B (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun y => Φ (t,y)) x v)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun y => Φ (t,y)) x w))
      (hform t ⟨ht,htδ⟩ (Φ (t,x)) (hstay x hx).2)
    exact hf.symm.trans (hΦform t ⟨ht.le,htε⟩ x (hstay x hx).1 v w)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
