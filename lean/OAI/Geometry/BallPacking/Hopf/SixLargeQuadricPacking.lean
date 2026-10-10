import Mathlib
import OAI.Geometry.BallPacking.Projective.SixLargeCubicPacking

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment MomentPolytope

 theorem actual_six_quadric_polynomial_packing_large (Q : ℕ) {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0<r i) (hr' : ∀ i,0≤r' i)
    (hrr : ∀ i,r' i<r i) {a : ℚ} (ha : (1:ℚ)/2<a) (ha1 : a<1)
    (hrs : ∀ i,r i<1-(a:ℝ)) (hvol : ∑ i,r i^3<1-(a:ℝ)^3) :
    ∃ L A B S : ℕ,Q<L ∧ 0<L ∧ 0<A ∧ 0<S ∧ A<S ∧ A≤B ∧ S≤B ∧ 3*B<L+S ∧ 2*S<L ∧
      (S:ℝ)=(L:ℝ)*(1-(a:ℝ)) ∧
      ∃ t δ : ℝ,0<t ∧ 0<δ ∧ ∃ f : Fin N → Ambient 3 → CubicAmbient,
        (∀ i,FormNeighborhoodEmbedding (closedBall 3 (r' i)) (fun _ => successorStandardForm 2)
          (outerAmbientForm (A := A) (B := B) L S (1/((L:ℝ)*Real.pi)) t δ) (f i)) ∧
        (∀ i,∀ x∈closedBall 3 (r' i),(f i x).2≠0) ∧
        Pairwise (fun i j => Disjoint (f i '' closedBall 3 (r' i)) (f j '' closedBall 3 (r' j))) := by
  classical
  obtain ⟨L,A,B,D,S,hQL,hL,hA,hS0,hAS,hAB,hSB,hB,_hS,heD,heS,t,ht,f,hf,hinto,hd⟩ :=
    actual_six_cubic_inner_polynomial_packing_avoid_axes_large Q r r' hr hr' hrr ha ha1 hrs hvol
  have hLr : 0<(L:ℝ) := Nat.cast_pos.mpr hL
  have hDL : D=L+S := by
    apply Nat.cast_injective (R := ℝ)
    push_cast
    rw [heD,heS]
    ring
  subst D
  have hSL : 2*S<L := by
    have har : (1:ℝ)/2<(a:ℝ) := by
      have hh : (((1:ℚ)/2:ℚ):ℝ)<(a:ℝ) := Rat.cast_lt.mpr ha
      norm_num at hh ⊢
      exact hh
    have hrS : 2*(S:ℝ)<(L:ℝ) := by rw [heS]; nlinarith
    exact_mod_cast hrS
  let K : Set CubicAmbient := ⋃ i,f i '' closedBall 3 (r' i)
  have hK : IsCompact K := by
    apply isCompact_iUnion
    intro i
    obtain ⟨U,_hU,hKU,hs,_he,_hf⟩ := hf i
    exact (closedBall_isCompact 3 (r' i)).image_of_continuousOn (hs.continuousOn.mono hKU)
  have hKd : K⊆cubicAffineDomain := by
    intro p hp
    obtain ⟨i,x,hx,rfl⟩ := mem_iUnion.mp hp
    exact hinto i hx
  have hdim : Module.finrank ℝ (Ambient 3)=Module.finrank ℝ CubicAmbient := by
    simp [Ambient,CubicAmbient,PlaneBase,Module.finrank_pi_fintype,Complex.finrank_real_complex]
  have hinv (p : CubicAmbient) (hp : p∈K) :
      (cubicAmbientForm (A := A) (B := B) (L+S) S (1/((L:ℝ)*Real.pi)) t p).IsInvertible := by
    obtain ⟨i,x,hx,rfl⟩ := mem_iUnion.mp hp
    exact (hf i).target_invertible hdim hx (successorStandardForm_isInvertible 2)
  obtain ⟨δ,hδ,g,W,hW,hKW,hg,he,hgT,hgform⟩ :=
    exists_actual_outer_normal_transfer hAS hSL hB (1/((L:ℝ)*Real.pi)) t hK hKd hinv
  obtain ⟨hgφ,hdj⟩ := postcompose_form_packing (fun i => closedBall 3 (r' i))
    (fun _ => successorStandardForm 2)
    (cubicAmbientForm (A := A) (B := B) (L+S) S (1/((L:ℝ)*Real.pi)) t)
    (outerAmbientForm (A := A) (B := B) L S (1/((L:ℝ)*Real.pi)) t δ)
    hW g hg.contMDiff.contMDiffOn he (by
      intro x hx v w
      have hh := hgform x hx v w
      simp only [mfderiv_eq_fderiv]
      convert! hh using 1) f hf
    (fun i x hx => hKW (mem_iUnion.mpr ⟨i,x,hx,rfl⟩)) hd
  exact ⟨L,A,B,S,hQL,hL,hA,hS0,hAS,hAB,hSB,hB,hSL,heS,t,δ,ht,hδ,fun i => g ∘ f i,
    hgφ,fun i x hx => hgT (f i x) (hKW (mem_iUnion.mpr ⟨i,x,hx,rfl⟩)),hdj⟩

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function
open scoped BigOperators
section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

 def radialSymplectization (z : PlanePhase ι) (α : PlanePhase ι →L[ℝ] ℝ)
    (C : PlanePhase ι →L[ℝ] PlanePhase ι →L[ℝ] ℝ) :=
  (2:ℝ) • ((phaseDot z).smulRight α-α.smulRight (phaseDot z))+(phaseSq z) • C

 theorem radialSymplectization_apply (z : PlanePhase ι) (α : PlanePhase ι →L[ℝ] ℝ)
    (C : PlanePhase ι →L[ℝ] PlanePhase ι →L[ℝ] ℝ) (v w : PlanePhase ι) :
    radialSymplectization z α C v w=
      2*(phaseDot z v*α w-α v*phaseDot z w)+phaseSq z*C v w := by
  simp only [radialSymplectization,add_apply,smul_apply,sub_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul]

 theorem radialSymplectization_nondegenerate {z : PlanePhase ι} (hz : z≠0)
    (α : PlanePhase ι →L[ℝ] ℝ) (C : PlanePhase ι →L[ℝ] PlanePhase ι →L[ℝ] ℝ)
    {c : ℝ} (hc : 0<c) (hαJ : α (phaseJ z)=c)
    (hCr : ∀ v,C v z=0) (hCJr : ∀ v,C v (phaseJ z)=0)
    (hCJl : ∀ v,C (phaseJ z) v=0)
    (hpos : ∀ v,phaseDot z v=0 → phaseArea z v=0 → v≠0 → 0<C v (phaseJ v)) :
    (radialSymplectization z α C).IsInvertible := by
  let Ω := radialSymplectization z α C
  have hq := phaseSq_pos hz
  have hinj : Injective Ω := by
    apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    intro v hv
    change Ω v=0 at hv
    have hval (w : PlanePhase ι) : Ω v w=0 := by rw [hv]; rfl
    have hdz : phaseDot z v=0 := by
      have h := hval (phaseJ z)
      change radialSymplectization z α C v (phaseJ z)=0 at h
      rw [radialSymplectization_apply,hαJ,hCJr,phaseDot_J_right,phaseArea_self] at h
      nlinarith
    have hαv : α v=0 := by
      have h := hval z
      change radialSymplectization z α C v z=0 at h
      rw [radialSymplectization_apply,hdz,hCr] at h
      change 2*(0*α z-α v*phaseSq z)+phaseSq z*0=0 at h
      nlinarith
    let b := phaseArea z v/phaseSq z
    let w := v-b•phaseJ z
    have hwd : phaseDot z w=0 := by
      simp only [w,map_sub,map_smul,phaseDot_J_right,phaseArea_self,neg_zero,smul_eq_mul,
        mul_zero,sub_zero,hdz]
    have hwa : phaseArea z w=0 := by
      simp only [w,map_sub,map_smul,smul_eq_mul,phaseArea_J_right]
      change phaseArea z v-(phaseArea z v/phaseSq z)*phaseSq z=0
      field_simp [hq.ne']
      ring
    have hCw : C w (phaseJ w)=0 := by
      have h := hval (phaseJ w)
      change radialSymplectization z α C v (phaseJ w)=0 at h
      rw [radialSymplectization_apply,hdz,hαv] at h
      have he : C w (phaseJ w)=C v (phaseJ w) := by
        simp only [w,map_sub,map_smul,sub_apply,smul_apply,smul_eq_mul,hCJl,mul_zero,sub_zero]
      rw [he]
      nlinarith
    have hw : w=0 := by
      by_contra hn
      have hh := hpos w hwd hwa hn
      linarith
    have hvw : v=b•phaseJ z := sub_eq_zero.mp hw
    have hb : b=0 := by
      rw [hvw,map_smul,hαJ,smul_eq_mul] at hαv
      exact (mul_eq_zero.mp hαv).resolve_right hc.ne'
    rw [hvw,hb,zero_smul]
  have hsurj : Surjective Ω :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (finrank_continuous_dual (E := PlanePhase ι)).symm).mp hinj
  exact ⟨(LinearEquiv.ofBijective Ω.toLinearMap ⟨hinj,hsurj⟩).toContinuousLinearEquiv,rfl⟩

 theorem radialSymplectization_circle (z : PlanePhase ι) (α : PlanePhase ι →L[ℝ] ℝ)
    (C : PlanePhase ι →L[ℝ] PlanePhase ι →L[ℝ] ℝ) {c : ℝ}
    (hα : α (phaseJ z)=c) (hC : ∀ v,C v (phaseJ z)=0) (v : PlanePhase ι) :
    radialSymplectization z α C v (phaseJ z)=2*c*phaseDot z v := by
  rw [radialSymplectization_apply,hα,hC,phaseDot_J_right,phaseArea_self]
  ring

 theorem radialSymplectization_moser_tangent (z : PlanePhase ι)
    (α β : PlanePhase ι →L[ℝ] ℝ) (C : PlanePhase ι →L[ℝ] PlanePhase ι →L[ℝ] ℝ)
    {c : ℝ} (hc : c≠0) (hα : α (phaseJ z)=c) (hC : ∀ v,C v (phaseJ z)=0)
    (hβ : β (phaseJ z)=0) (v : PlanePhase ι)
    (hv : radialSymplectization z α C v=β) : phaseDot z v=0 := by
  have h := congrArg (fun L : PlanePhase ι →L[ℝ] ℝ => L (phaseJ z)) hv
  rw [radialSymplectization_circle z α C hα hC,hβ] at h
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (by norm_num) hc)

def mixedHopfPrimitive (F : PlanePhase ι → PlanePhase κ) (c d : ℝ) :
    PlanePhase ι → PlanePhase ι →L[ℝ] ℝ :=
  (1-2*d)•hopfPrimitive c+d•primitivePullback (hopfPrimitive c) F

def mixedHopfForm (F : PlanePhase ι → PlanePhase κ) (c d : ℝ) :=
  euclideanExteriorOneForm (mixedHopfPrimitive F c d)

def homogeneousConePrimitive (F : PlanePhase ι → PlanePhase κ) (c d : ℝ)
    (z : PlanePhase ι) : PlanePhase ι →L[ℝ] ℝ :=
  phaseSq z•mixedHopfPrimitive F c d z

theorem mixedHopfPrimitive_smoothAt {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0) (c d : ℝ) :
    ContDiffAt ℝ ∞ (mixedHopfPrimitive F c d) z :=
  ((hopfPrimitive_smoothAt c hz).const_smul (1-2*d)).add
    ((primitivePullback_smoothAt (hopfPrimitive_smoothAt c hFz) hF).const_smul d)

theorem mixedHopfForm_eq {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0) (c d : ℝ) :
    mixedHopfForm F c d z=(1-2*d)•hopfForm c z+
      d•(hopfForm c (F z)).bilinearComp (fderiv ℝ F z) (fderiv ℝ F z) := by
  have h₀ := (hopfPrimitive_smoothAt c hz).differentiableAt (by simp)
  have h₁ := (primitivePullback_smoothAt (hopfPrimitive_smoothAt c hFz) hF).differentiableAt (by simp)
  rw [mixedHopfForm,mixedHopfPrimitive,euclideanExteriorOneForm_add (h₀.const_smul _) (h₁.const_smul _),
    euclideanExteriorOneForm_smul _ h₀,euclideanExteriorOneForm_smul _ h₁,
    primitivePullback_exteriorAt (hopfPrimitive_smoothAt c hFz) hF]
  rfl

theorem mixedHopfPrimitive_circle {F : PlanePhase ι → PlanePhase κ} {z : PlanePhase ι}
    (hz : z≠0) (hFz : F z≠0)
    (hD : fderiv ℝ F z (phaseJ z)=(2:ℝ)•phaseJ (F z)) (c d : ℝ) :
    mixedHopfPrimitive F c d z (phaseJ z)=c/2 := by
  simp only [mixedHopfPrimitive,Pi.add_apply,Pi.smul_apply,add_apply,smul_apply,
    smul_eq_mul,primitivePullback,ContinuousLinearMap.comp_apply,hD,map_smul,
    hopfPrimitive_circle c hz,hopfPrimitive_circle c hFz]
  ring

theorem mixedHopfForm_radial {F : PlanePhase ι → PlanePhase κ} {z : PlanePhase ι}
    (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0)
    (hD : fderiv ℝ F z z=(2:ℝ)•F z) (c d : ℝ) (v : PlanePhase ι) :
    mixedHopfForm F c d z z v=0 := by
  rw [mixedHopfForm_eq hF hz hFz]
  simp only [add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.bilinearComp_apply,hD,
    map_smul,hopfForm_radial c hz,hopfForm_radial c hFz,mul_zero,add_zero]

theorem mixedHopfForm_circle {F : PlanePhase ι → PlanePhase κ} {z : PlanePhase ι}
    (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0)
    (hD : fderiv ℝ F z (phaseJ z)=(2:ℝ)•phaseJ (F z)) (c d : ℝ) (v : PlanePhase ι) :
    mixedHopfForm F c d z (phaseJ z) v=0 := by
  rw [mixedHopfForm_eq hF hz hFz]
  simp only [add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.bilinearComp_apply,hD,
    map_smul,hopfForm_circle c hz,hopfForm_circle c hFz,mul_zero,add_zero]

theorem mixedHopfForm_skew (F : PlanePhase ι → PlanePhase κ) (c d : ℝ)
    (z v w : PlanePhase ι) : mixedHopfForm F c d z v w= -mixedHopfForm F c d z w v := by
  simp only [mixedHopfForm,euclideanExteriorOneForm,sub_apply,ContinuousLinearMap.flip_apply]
  ring

theorem mixedHopfForm_horizontal_positive {F : PlanePhase ι → PlanePhase κ} {z : PlanePhase ι}
    (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0)
    (hJ : ∀ v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v))
    {c d : ℝ} (hc : 0<c) (hd : 0≤d) (hdhalf : d<1/2)
    {v : PlanePhase ι} (hdv : phaseDot z v=0) (hav : phaseArea z v=0) (hv : v≠0) :
    0 < mixedHopfForm F c d z v (phaseJ v) := by
  rw [mixedHopfForm_eq hF hz hFz]
  simp only [add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.bilinearComp_apply,hJ]
  have hp : 0<hopfForm c z v (phaseJ v) := by
    rw [hopfForm_complex_diagonal c hz,hdv,hav]
    simp only [zero_pow (by norm_num : 2≠0),zero_add,sub_zero]
    exact mul_pos (div_pos hc (sq_pos_of_pos (phaseSq_pos hz)))
      (mul_pos (phaseSq_pos hz) (phaseSq_pos hv))
  exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) hp)
    (mul_nonneg hd (hopfForm_semipositive hc.le hFz _))

theorem homogeneousConePrimitive_exterior {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0) (c d : ℝ) :
    euclideanExteriorOneForm (homogeneousConePrimitive F c d) z=
      radialSymplectization z (mixedHopfPrimitive F c d z) (mixedHopfForm F c d z) := by
  have ha := (mixedHopfPrimitive_smoothAt hF hz hFz c d).differentiableAt (by simp)
  have he := (phaseSq_hasFDerivAt z).smul ha.hasFDerivAt
  rw [euclideanExteriorOneForm,show fderiv ℝ (homogeneousConePrimitive F c d) z=_ from he.fderiv]
  ext v w
  simp only [sub_apply,ContinuousLinearMap.flip_apply,add_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul,radialSymplectization_apply,
    mixedHopfForm,euclideanExteriorOneForm]
  ring

theorem homogeneousConePrimitive_nondegenerate {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0)
    (hD : fderiv ℝ F z z=(2:ℝ)•F z)
    (hJ : ∀ v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v))
    {c d : ℝ} (hc : 0<c) (hd : 0≤d) (hdhalf : d<1/2) :
    (euclideanExteriorOneForm (homogeneousConePrimitive F c d) z).IsInvertible := by
  have hDJ : fderiv ℝ F z (phaseJ z)=(2:ℝ)•phaseJ (F z) := by rw [hJ,hD,map_smul]
  rw [homogeneousConePrimitive_exterior hF hz hFz]
  apply radialSymplectization_nondegenerate hz _ _ (half_pos hc)
    (mixedHopfPrimitive_circle hz hFz hDJ c d)
  · intro v
    rw [mixedHopfForm_skew,mixedHopfForm_radial hF hz hFz hD,neg_zero]
  · intro v
    rw [mixedHopfForm_skew,mixedHopfForm_circle hF hz hFz hDJ,neg_zero]
  · exact mixedHopfForm_circle hF hz hFz hDJ c d
  · intro v hdv hav hv
    exact mixedHopfForm_horizontal_positive hF hz hFz hJ hc hd hdhalf hdv hav hv

theorem homogeneousConePrimitive_circle_contraction {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0)
    (hDJ : fderiv ℝ F z (phaseJ z)=(2:ℝ)•phaseJ (F z)) (c d : ℝ) (v : PlanePhase ι) :
    euclideanExteriorOneForm (homogeneousConePrimitive F c d) z v (phaseJ z)=c*phaseDot z v := by
  rw [homogeneousConePrimitive_exterior hF hz hFz,
    radialSymplectization_circle z _ _ (mixedHopfPrimitive_circle hz hFz hDJ c d)
      (fun v => by rw [mixedHopfForm_skew,mixedHopfForm_circle hF hz hFz hDJ,neg_zero])]
  ring

theorem homogeneousConePrimitive_smoothAt {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0) (c d : ℝ) :
    ContDiffAt ℝ ∞ (homogeneousConePrimitive F c d) z :=
  phaseSq_smooth.contDiffAt.smul (mixedHopfPrimitive_smoothAt hF hz hFz c d)

theorem homogeneousConePrimitive_affine (F : PlanePhase ι → PlanePhase κ)
    (c d s : ℝ) (z : PlanePhase ι) :
    (1-s)•homogeneousConePrimitive F c 0 z+s•homogeneousConePrimitive F c d z=
      homogeneousConePrimitive F c (s*d) z := by
  ext v
  simp only [homogeneousConePrimitive,mixedHopfPrimitive,Pi.add_apply,Pi.smul_apply,
    add_apply,smul_apply,smul_eq_mul]
  ring

theorem homogeneousConePrimitive_circle {F : PlanePhase ι → PlanePhase κ} {z : PlanePhase ι}
    (hz : z≠0) (hFz : F z≠0)
    (hD : fderiv ℝ F z (phaseJ z)=(2:ℝ)•phaseJ (F z)) (c d : ℝ) :
    homogeneousConePrimitive F c d z (phaseJ z)=phaseSq z*(c/2) := by
  simp only [homogeneousConePrimitive,smul_apply,smul_eq_mul,mixedHopfPrimitive_circle hz hFz hD c d]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def hopfCurvaturePullback (c : ℝ) (G : E → (ι → ℂ)) (x : E) (v w : E) : ℝ :=
  hopfForm c (complexCartesian (G x))
    (fderiv ℝ (fun y => complexCartesian (G y)) x v)
    (fderiv ℝ (fun y => complexCartesian (G y)) x w)

def mixedHopfCurvaturePullback (P : (ι → ℂ) → (κ → ℂ)) (c d : ℝ)
    (G : E → (ι → ℂ)) (x : E) (v w : E) : ℝ :=
  (1-2*d)*hopfCurvaturePullback c G x v w+
    d*hopfCurvaturePullback c (fun y => P (G y)) x v w

theorem mixedHopfCurvaturePullback_gauge {P : (ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) (hPn : ∀ z,z≠0 → P z≠0)
    (hPs : ∀ (ζ : ℂ) z,P (ζ•z)=ζ^2•P z)
    {S : E → ℂ} {G : E → (ι → ℂ)} {x : E}
    (hS : DifferentiableAt ℝ S x) (hG : DifferentiableAt ℝ G x)
    (hSx : S x≠0) (hGx : G x≠0) (c d : ℝ) (v w : E) :
    mixedHopfCurvaturePullback P c d (fun y => S y•G y) x v w=
      mixedHopfCurvaturePullback P c d G x v w := by
  have hGxc : complexCartesian (G x)≠0 := by
    intro h; exact hGx (complexCartesian.injective (h.trans (map_zero _).symm))
  have hPGxc : complexCartesian (P (G x))≠0 := by
    intro h; exact hPn (G x) hGx (complexCartesian.injective (h.trans (map_zero _).symm))
  have he : (fun y => P (S y•G y))=(fun y => (S y)^2•P (G y)) := funext fun y => hPs _ _
  unfold mixedHopfCurvaturePullback
  change (1-2*d)*hopfCurvaturePullback c (fun y => S y•G y) x v w+
    d*hopfCurvaturePullback c (fun y => P (S y•G y)) x v w=_
  rw [he]
  unfold hopfCurvaturePullback
  rw [hopfForm_variable_gauge hS hG hSx hGxc]
  have h₂ := hopfForm_variable_gauge (S := fun y => S y^2) (G := fun y => P (G y))
    (hS.pow 2) ((hP.differentiable (by simp) (G x)).comp x hG)
      (pow_ne_zero 2 hSx) hPGxc c v w
  exact congrArg (fun q : ℝ => (1-2*d)*hopfCurvaturePullback c G x v w+d*q) h₂

def cartesianConjugate (P : (ι → ℂ) → (κ → ℂ)) : PlanePhase ι → PlanePhase κ :=
  fun z => complexCartesian (P (complexCartesian.symm z))

theorem cartesianConjugate_smooth {P : (ι → ℂ) → (κ → ℂ)} (hP : ContDiff ℝ ∞ P) :
    ContDiff ℝ ∞ (cartesianConjugate P) :=
  (complexCartesian (ι := κ)).contDiff.comp (hP.comp (complexCartesian (ι := ι)).symm.contDiff)

@[simp] theorem cartesianConjugate_cartesian (P : (ι → ℂ) → (κ → ℂ)) (z : ι → ℂ) :
    cartesianConjugate P (complexCartesian z)=complexCartesian (P z) := by
  simp only [cartesianConjugate,ContinuousLinearEquiv.symm_apply_apply]

theorem mixedHopfCurvaturePullback_eq {P : (ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) {G : E → (ι → ℂ)} {x : E}
    (hG : DifferentiableAt ℝ G x) (hGx : G x≠0) (hPGx : P (G x)≠0)
    (c d : ℝ) (v w : E) :
    mixedHopfCurvaturePullback P c d G x v w=
      mixedHopfForm (cartesianConjugate P) c d (complexCartesian (G x))
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
  rw [mixedHopfForm_eq (cartesianConjugate_smooth hP).contDiffAt hz hPz]
  simp only [add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.bilinearComp_apply,
    cartesianConjugate_cartesian,mixedHopfCurvaturePullback,hopfCurvaturePullback,hD]

end
section

variable {ι κ : Type} [Fintype ι] [Fintype κ]

 theorem homogeneousDegree_euler {P : (ι → ℂ) → (κ → ℂ)} (hP : ContDiff ℂ ∞ P)
    {ℓ : ℕ} (hPs : ∀ (ζ : ℂ) z,P (ζ•z)=ζ^ℓ•P z) (z : ι → ℂ) :
    fderiv ℂ P z z=(ℓ:ℂ)•P z := by
  have hf := (hP.differentiable (by simp) z)
  have hf' : HasFDerivAt P (fderiv ℂ P z) ((1:ℂ)•z) := by simpa only [one_smul] using hf.hasFDerivAt
  have hd := hf'.comp_hasDerivAt (1:ℂ) ((hasDerivAt_id (1:ℂ)).smul_const z)
  have he : (fun b : ℂ => P (b•z))=(fun b : ℂ => b^ℓ•P z) := funext fun b => hPs b z
  have hd' : HasDerivAt (fun b : ℂ => b^ℓ•P z) ((ℓ:ℂ)•P z) 1 := by
    convert! (((hasDerivAt_id (1:ℂ)).pow ℓ).smul_const (P z)) using 1; simp
  simp only [Function.comp_def,id_eq] at hd
  rw [he] at hd
  simpa only [one_smul] using hd.unique hd'

 theorem cartesianConjugate_fderiv {P : (ι → ℂ) → (κ → ℂ)} (hP : ContDiff ℂ ∞ P)
    (z v : PlanePhase ι) : fderiv ℝ (cartesianConjugate P) z v=
      complexCartesian (fderiv ℂ P (complexCartesian.symm z) (complexCartesian.symm v)) := by
  have hh := (hP.differentiable (by simp) (complexCartesian.symm z)).hasFDerivAt.restrictScalars ℝ
  have hd := complexCartesian.toContinuousLinearMap.hasFDerivAt.comp z
    (hh.comp z (complexCartesian (ι := ι)).symm.hasFDerivAt)
  exact congrArg (fun L => L v) hd.fderiv

 theorem cartesianConjugate_euler {P : (ι → ℂ) → (κ → ℂ)} (hP : ContDiff ℂ ∞ P)
    {ℓ : ℕ} (hPs : ∀ (ζ : ℂ) z,P (ζ•z)=ζ^ℓ•P z) (z : PlanePhase ι) :
    fderiv ℝ (cartesianConjugate P) z z=(ℓ:ℝ)•cartesianConjugate P z := by
  rw [cartesianConjugate_fderiv hP,homogeneousDegree_euler hP hPs]
  rw [show (ℓ:ℂ)•P (complexCartesian.symm z)=(ℓ:ℝ)•P (complexCartesian.symm z) by
    ext i; simp [Pi.smul_apply,Complex.real_smul]]
  exact map_smul _ _ _

 theorem cartesianConjugate_J {P : (ι → ℂ) → (κ → ℂ)} (hP : ContDiff ℂ ∞ P)
    (z v : PlanePhase ι) : fderiv ℝ (cartesianConjugate P) z (phaseJ v)=
      phaseJ (fderiv ℝ (cartesianConjugate P) z v) := by
  have hJ : complexCartesian.symm (phaseJ v)=Complex.I•complexCartesian.symm v := by
    apply complexCartesian.injective
    simp only [ContinuousLinearEquiv.apply_symm_apply,complexCartesian_I]
  rw [cartesianConjugate_fderiv hP,cartesianConjugate_fderiv hP,hJ,map_smul,complexCartesian_I]

 theorem cartesianConjugate_nonzero {P : (ι → ℂ) → (κ → ℂ)}
    (hPn : ∀ z,z≠0 → P z≠0) {z : PlanePhase ι} (hz : z≠0) : cartesianConjugate P z≠0 := by
  intro he
  have hn : complexCartesian.symm z≠0 := by
    intro hh
    exact hz (by simpa only [ContinuousLinearEquiv.apply_symm_apply,map_zero] using congrArg complexCartesian hh)
  exact hPn _ hn (complexCartesian.injective (he.trans (map_zero _).symm))

end

variable {ι : Type} [Fintype ι]

 def homogeneousVeronese (m : ℕ) (z : ι → ℂ) : (Fin m → ι) → ℂ :=
  fun j => ∏ i,z (j i)

 theorem homogeneousVeronese_smooth (m : ℕ) :
    ContDiff ℂ ∞ (homogeneousVeronese (ι := ι) m) := by
  apply contDiff_pi.mpr
  intro j
  exact contDiff_prod (fun i _ => contDiff_apply ℂ ℂ (j i))

omit [Fintype ι] in
 theorem homogeneousVeronese_homogeneous (m : ℕ) (ζ : ℂ) (z : ι → ℂ) :
    homogeneousVeronese m (ζ•z)=ζ^m•homogeneousVeronese m z := by
  ext j
  simp [homogeneousVeronese,Finset.prod_mul_distrib]

omit [Fintype ι] in
 theorem homogeneousVeronese_nonzero (m : ℕ) {z : ι → ℂ} (hz : z≠0) :
    homogeneousVeronese m z≠0 := by
  classical
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hz
  intro h
  have hh := congrFun h (fun _ => i)
  simp only [homogeneousVeronese,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    Pi.zero_apply] at hh
  exact pow_ne_zero m hi hh

 theorem homogeneousVeronese_sq (m : ℕ) (z : ι → ℂ) :
    phaseSq (complexCartesian (homogeneousVeronese m z))=(phaseSq (complexCartesian z))^m := by
  classical
  simp only [complexCartesian_sq,homogeneousVeronese,map_prod]
  simpa using (Finset.sum_pow' (R := ℝ) Finset.univ (fun i => Complex.normSq (z i)) m).symm

variable {κ : Type} [Fintype κ]
 def veroneseRegularization (m : ℕ) (P : (ι → ℂ) → (κ → ℂ)) (ε : ℝ)
    (z : ι → ℂ) : (κ ⊕ (Fin m → ι)) → ℂ :=
  Sum.elim (P z) (fun j => (ε:ℂ)*homogeneousVeronese m z j)

 theorem veroneseRegularization_smooth (m : ℕ) {P : (ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℂ ∞ P) (ε : ℝ) :
    ContDiff ℂ ∞ (veroneseRegularization m P ε) := by
  apply contDiff_pi.mpr
  rintro (i|j)
  · exact (contDiff_apply ℂ ℂ i).comp hP
  · exact contDiff_const.mul ((contDiff_apply ℂ ℂ j).comp (homogeneousVeronese_smooth m))

 theorem veroneseRegularization_joint_smooth (m : ℕ) {P : (ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℝ ∞ P) :
    ContDiff ℝ ∞ (fun p : ℝ×(ι → ℂ) => veroneseRegularization m P p.1 p.2) := by
  apply contDiff_pi.mpr
  rintro (i|j)
  · exact (contDiff_apply ℝ ℂ i).comp (hP.comp contDiff_snd)
  · exact (Complex.ofRealCLM.contDiff.comp contDiff_fst).mul
      ((contDiff_apply ℝ ℂ j).comp ((homogeneousVeronese_smooth m).restrict_scalars ℝ |>.comp contDiff_snd))

omit [Fintype ι] [Fintype κ] in
 theorem veroneseRegularization_homogeneous {m : ℕ} {P : (ι → ℂ) → (κ → ℂ)}
    (hP : ∀ (ζ : ℂ) z,P (ζ•z)=ζ^m•P z) (ε : ℝ) (ζ : ℂ) (z : ι → ℂ) :
    veroneseRegularization m P ε (ζ•z)=ζ^m•veroneseRegularization m P ε z := by
  ext i
  cases i with
  | inl i => exact congrFun (hP ζ z) i
  | inr j =>
    simp only [veroneseRegularization,Sum.elim_inr,homogeneousVeronese_homogeneous,Pi.smul_apply,smul_eq_mul]
    ring

omit [Fintype ι] [Fintype κ] in
 theorem veroneseRegularization_nonzero (m : ℕ) (P : (ι → ℂ) → (κ → ℂ))
    {ε : ℝ} (hε : ε≠0) {z : ι → ℂ} (hz : z≠0) :
    veroneseRegularization m P ε z≠0 := by
  intro h
  apply homogeneousVeronese_nonzero m hz
  funext j
  have hh := congrFun h (Sum.inr j)
  change (ε:ℂ)*homogeneousVeronese m z j=0 at hh
  exact (mul_eq_zero.mp hh).resolve_left (Complex.ofReal_ne_zero.mpr hε)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
