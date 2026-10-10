import Mathlib
import OAI.Geometry.BallPacking.Moments.RearrangementBounds

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem smooth_fderiv_apply_const {D G : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup G] [NormedSpace ℝ G] {f : D → G}
    (hf : ContDiff ℝ ∞ f) (p v w : D) :
    fderiv ℝ (fun q => fderiv ℝ f q v) p w = fderiv ℝ (fderiv ℝ f) p w v := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hh := (hfd.differentiable (by simp) p).hasFDerivAt.clm_apply
    (hasFDerivAt_const v p)
  rw [hh.fderiv]
  simp

theorem joint_spatial_fderiv {F : ℝ × E → E} (hF : ContDiff ℝ ∞ F) (t : ℝ) (x v : E) :
    fderiv ℝ (fun y => F (t,y)) x v = fderiv ℝ F (t,x) (0,v) := by
  have hd := (hF.differentiable (by simp) (t,x)).hasFDerivAt.comp x
    ((hasFDerivAt_const (c := t) x).prodMk (hasFDerivAt_id (𝕜 := ℝ) x))
  exact congrArg (fun A : E →L[ℝ] E => A v) hd.fderiv

theorem joint_time_fderiv {F X : ℝ × E → E} (hF : ContDiff ℝ ∞ F)
    (hflow : ∀ t x, HasDerivAt (fun s => F (s,x)) (X (t,F (t,x))) t) (p : ℝ × E) :
    fderiv ℝ F p (1,0) = X (p.1,F p) := by
  have hd := (hF.differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  exact hd.unique (hflow p.1 p.2)

theorem joint_flow_variation {F X : ℝ × E → E} (hF : ContDiff ℝ ∞ F)
    (hX : ContDiff ℝ ∞ X)
    (hflow : ∀ t x, HasDerivAt (fun s => F (s,x)) (X (t,F (t,x))) t)
    (t : ℝ) (x v : E) :
    HasDerivAt (fun s => fderiv ℝ F (s,x) (0,v))
      (fderiv ℝ X (t,F (t,x)) (0,fderiv ℝ F (t,x) (0,v))) t := by
  have hFd : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hV : ContDiff ℝ ∞ (fun p => fderiv ℝ F p (0,v)) := hFd.clm_apply contDiff_const
  have hd := (hV.differentiable (by simp) (t,x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have he : (fun p => fderiv ℝ F p (1,0)) = fun p => X (p.1,F p) :=
    funext (joint_time_fderiv hF hflow)
  have hchain := (hX.differentiable (by simp) (t,F (t,x))).hasFDerivAt.comp (t,x)
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := (t,x))).prodMk
      (hF.differentiable (by simp) (t,x)).hasFDerivAt)
  have hc := congrArg (fun A : (ℝ × E) →L[ℝ] E => A (0,v)) hchain.fderiv
  change fderiv ℝ (fun p => X (p.1,F p)) (t,x) (0,v) = _ at hc
  have he' := congrArg (fun g : ℝ × E → E => fderiv ℝ g (t,x) (0,v)) he
  rw [smooth_fderiv_apply_const hF] at he'
  rw [hc] at he'
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply] at he'
  have hs := (hF.contDiffAt (x := (t,x))).isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  apply hd.congr_deriv
  rw [smooth_fderiv_apply_const hF,hs.eq (1,0) (0,v)]
  exact he'

theorem smooth_flow_form_transport_on {F X : ℝ × E → E} (hF : ContDiff ℝ ∞ F)
    (hX : ContDiff ℝ ∞ X)
    (hflow : ∀ t x, HasDerivAt (fun s => F (s,x)) (X (t,F (t,x))) t)
    {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ} (hΩ : ContDiff ℝ ∞ Ω)
    {a b : ℝ} (hab : a ≤ b) (x v w : E)
    (hPDE : ∀ t ∈ Ioo a b, ∀ u z,
      fderiv ℝ Ω (t,F (t,x)) (1,X (t,F (t,x))) u z +
      Ω (t,F (t,x)) (fderiv ℝ X (t,F (t,x)) (0,u)) z +
      Ω (t,F (t,x)) u (fderiv ℝ X (t,F (t,x)) (0,z)) = 0) :
    Ω (b,F (b,x)) (fderiv ℝ (fun y => F (b,y)) x v)
      (fderiv ℝ (fun y => F (b,y)) x w) =
    Ω (a,F (a,x)) (fderiv ℝ (fun y => F (a,y)) x v)
      (fderiv ℝ (fun y => F (a,y)) x w) := by
  let V (s : ℝ) := fderiv ℝ F (s,x) (0,v)
  let W (s : ℝ) := fderiv ℝ F (s,x) (0,w)
  let G (s : ℝ) := Ω (s,F (s,x)) (V s) (W s)
  have hpath : Continuous (fun s => (s,F (s,x))) :=
    continuous_id.prodMk (hF.continuous.comp (continuous_id.prodMk continuous_const))
  have hFd : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hVc : Continuous V := ((hFd.continuous.comp
    (continuous_id.prodMk continuous_const)).clm_apply continuous_const)
  have hWc : Continuous W := ((hFd.continuous.comp
    (continuous_id.prodMk continuous_const)).clm_apply continuous_const)
  have hGc : Continuous G := ((hΩ.continuous.comp hpath).clm_apply hVc).clm_apply hWc
  have hGd (s : ℝ) (hs : s ∈ Ioo a b) : HasDerivAt G 0 s := by
    have hdΩ := (hΩ.differentiable (by simp) (s,F (s,x))).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hflow s x))
    have hd := (hdΩ.clm_apply (joint_flow_variation hF hX hflow s x v)).clm_apply
      (joint_flow_variation hF hX hflow s x w)
    apply hd.congr_deriv
    simpa only [add_apply,Function.comp_apply,id_eq,V,W] using hPDE s hs (V s) (W s)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    hGc.continuousOn hGd (intervalIntegrable_const (c := (0:ℝ)))
  have he : G b = G a := sub_eq_zero.mp (by simpa using hi.symm)
  simpa only [G,V,W,joint_spatial_fderiv hF] using he


end

section
open scoped ContDiff BigOperators
open Set Function

@[simp] theorem planeRotate_comp (s t : ℝ) (z : Plane) :
    planeRotate s (planeRotate t z) = planeRotate (s+t) z := by
  apply Prod.ext <;> dsimp [planeRotate] <;> rw [Real.cos_add,Real.sin_add] <;> ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def toricFlow (F : (ι → ℝ) → ℝ) (t : ℝ) (z : PlanePhase ι) : PlanePhase ι :=
  fun i => planeRotate (t*toricAngularSpeed F z i) (z i)

omit [Fintype ι] in
@[simp] theorem toricFlow_zero (F : (ι → ℝ) → ℝ) (z : PlanePhase ι) : toricFlow F 0 z = z := by
  funext i
  simp [toricFlow]

omit [Fintype ι] in
@[simp] theorem toricFlow_moments (F : (ι → ℝ) → ℝ) (t : ℝ) (z : PlanePhase ι) :
    planeMoments (toricFlow F t z) = planeMoments z := by
  funext i
  exact radialArea_planeRotate _ _

omit [Fintype ι] in
@[simp] theorem toricAngularSpeed_flow (F : (ι → ℝ) → ℝ) (t : ℝ) (z : PlanePhase ι) (i : ι) :
    toricAngularSpeed F (toricFlow F t z) i = toricAngularSpeed F z i := by
  simp [toricAngularSpeed]

omit [Fintype ι] in
theorem toricFlow_add (F : (ι → ℝ) → ℝ) (s t : ℝ) (z : PlanePhase ι) :
    toricFlow F s (toricFlow F t z) = toricFlow F (s+t) z := by
  funext i
  change planeRotate (s*toricAngularSpeed F (toricFlow F t z) i)
    (planeRotate (t*toricAngularSpeed F z i) (z i)) = _
  rw [toricAngularSpeed_flow,planeRotate_comp]
  simp only [toricFlow,add_mul]

omit [DecidableEq ι] in

theorem phase_rotation_smooth {a : ℝ × PlanePhase ι → (ι → ℝ)}
    (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => fun i => planeRotate (a p i) (p.2 i)) := by
  apply contDiff_pi.mpr
  intro i
  have hi : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => a p i) :=
    (contDiff_apply ℝ ℝ i).comp ha
  have hz : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => p.2 i) :=
    (contDiff_apply ℝ Plane i).comp contDiff_snd
  convert! planeRotate_smooth.comp (hi.prodMk hz) using 1

theorem toric_flow_angles_smooth {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => fun i => p.1*toricAngularSpeed F p.2 i) := by
  apply contDiff_pi.mpr
  intro i
  have ha : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => toricAngularSpeed F p.2 i) :=
    (toricAngularSpeed_smooth hF i).comp contDiff_snd
  exact contDiff_fst.mul ha

@[fun_prop] theorem toricFlow_smooth {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => toricFlow F p.1 p.2) := by
  exact phase_rotation_smooth (toric_flow_angles_smooth hF)

theorem toricFlow_time_smooth {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) (t : ℝ) :
    ContDiff ℝ ∞ (toricFlow F t) := by
  convert! (toricFlow_smooth hF).comp (contDiff_const.prodMk contDiff_id) using 1

def toricFlowHomeomorph {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) (t : ℝ) :
    PlanePhase ι ≃ₜ PlanePhase ι where
  toFun := toricFlow F t
  invFun := toricFlow F (-t)
  left_inv z := by rw [toricFlow_add,neg_add_cancel,toricFlow_zero]
  right_inv z := by rw [toricFlow_add,add_neg_cancel,toricFlow_zero]
  continuous_toFun := (toricFlow_time_smooth hF t).continuous
  continuous_invFun := (toricFlow_time_smooth hF (-t)).continuous

theorem toricFlow_hasDerivAt {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (t : ℝ) (z : PlanePhase ι) :
    HasDerivAt (fun s => toricFlow F s z)
      (hamiltonianField phaseArea (toricHamiltonian F) (t,toricFlow F t z)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  have hd := planeRotate_hasDerivAt ((hasDerivAt_id t).mul_const (toricAngularSpeed F z i)) (z i)
  apply hd.congr_deriv
  rw [toricHamiltonian_field hF,toricAngularSpeed_flow]
  simp only [one_mul,toricFlow,id_eq]

theorem toricFlow_symplectic {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (t : ℝ) (z v w : PlanePhase ι) :
    phaseArea (fderiv ℝ (toricFlow F t) z v) (fderiv ℝ (toricFlow F t) z w) = phaseArea v w := by
  have hHs := toricHamiltonian_smooth hF
  have hXs := hamiltonianField_smooth phaseArea_isInvertible hHs
  have he (a b : ℝ) (hab : a ≤ b) :
      phaseArea (fderiv ℝ (toricFlow F b) z v) (fderiv ℝ (toricFlow F b) z w) =
      phaseArea (fderiv ℝ (toricFlow F a) z v) (fderiv ℝ (toricFlow F a) z w) := by
    apply smooth_flow_form_transport_on (toricFlow_smooth hF) hXs (toricFlow_hasDerivAt hF)
      (Ω := fun _ => phaseArea) contDiff_const hab z v w
    intro s _ u q
    simpa only [fderiv_const_apply,zero_apply,zero_add] using
      hamiltonianField_transport_equation phaseArea_isInvertible phaseArea_skew hHs
        (s,toricFlow F s z) u q
  have hzero : toricFlow F 0 = id := funext (toricFlow_zero F)
  by_cases ht : 0 ≤ t
  · simpa only [hzero,fderiv_id,ContinuousLinearMap.id_apply] using he 0 t ht
  · simpa only [hzero,fderiv_id,ContinuousLinearMap.id_apply] using (he t 0 (le_of_not_ge ht)).symm


end

section
open scoped ContDiff
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem joint_flow_fderiv {F X : ℝ × E → E} (hF : ContDiff ℝ ∞ F)
    (hflow : ∀ t x, HasDerivAt (fun s => F (s,x)) (X (t,F (t,x))) t)
    (t τ : ℝ) (x v : E) :
    fderiv ℝ F (t,x) (τ,v) = τ • X (t,F (t,x)) +
      fderiv ℝ (fun y => F (t,y)) x v := by
  rw [show (τ,v) = τ • ((1,0) : ℝ × E) + (0,v) by ext <;> simp,
    map_add,map_smul,joint_time_fderiv hF hflow,joint_spatial_fderiv hF]

theorem suspension_form_identity {A : E →L[ℝ] E →L[ℝ] ℝ}
    (hskew : ∀ v w, A v w = -A w v) {D : E →L[ℝ] E} {X : E} {η : E →L[ℝ] ℝ}
    (hsp : ∀ v w, A (D v) (D w) = A v w)
    (hX : ∀ v, A X (D v) = -η v) (v w : Plane × E) :
    productForm A (v.1,v.1.2 • X + D v.2) (w.1,w.1.2 • X + D w.2) =
      oneCovectorForm A 1 η v w := by
  have hXX : A X X = 0 := by have hh := hskew X X; linarith
  have hright : A (D v.2) X = η v.2 := by rw [hskew,hX,neg_neg]
  simp only [productForm_apply,oneCovectorForm_apply,planarArea_apply,map_add,map_smul,
    add_apply,smul_apply,smul_eq_mul,hXX,hsp,hX,hright]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def toricFunction (F : (ι → ℝ) → ℝ) (z : PlanePhase ι) : ℝ := F (planeMoments z)

omit [DecidableEq ι] in
@[fun_prop] theorem toricFunction_smooth {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (toricFunction F) := hF.comp planeMoments_smooth

theorem toricFlow_energy_differential {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (t : ℝ) (z v : PlanePhase ι) :
    fderiv ℝ (toricFunction F) (toricFlow F t z) (fderiv ℝ (toricFlow F t) z v) =
      fderiv ℝ (toricFunction F) z v := by
  have hs : ContDiff ℝ ∞ (toricFlow F t) := toricFlow_time_smooth hF t
  have he : toricFunction F ∘ toricFlow F t = toricFunction F := by
    funext z; simp [toricFunction]
  have hd := fderiv_comp z ((toricFunction_smooth hF).differentiable (by simp) _)
    (hs.differentiable (by simp) _)
  rw [he] at hd
  exact (congrArg (fun L : PlanePhase ι →L[ℝ] ℝ => L v) hd).symm

def toricSuspension (F : (ι → ℝ) → ℝ) (p : Plane × PlanePhase ι) : Plane × PlanePhase ι :=
  (p.1,toricFlow F p.1.2 p.2)

@[fun_prop] theorem toricSuspension_smooth {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (toricSuspension F) := by
  have ht : ContDiff ℝ ∞ (fun p : Plane × PlanePhase ι => p.1.2) :=
    contDiff_snd.comp contDiff_fst
  have hz : ContDiff ℝ ∞ (fun p : Plane × PlanePhase ι => toricFlow F p.1.2 p.2) := by
    convert! (toricFlow_smooth hF).comp (ht.prodMk contDiff_snd) using 1
  exact contDiff_fst.prodMk hz

theorem toricSuspension_fderiv {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (p v : Plane × PlanePhase ι) :
    fderiv ℝ (toricSuspension F) p v =
      (v.1,v.1.2 • hamiltonianField phaseArea (toricHamiltonian F)
        (p.1.2,toricFlow F p.1.2 p.2) + fderiv ℝ (toricFlow F p.1.2) p.2 v.2) := by
  have hg := (toricFlow_smooth hF).differentiable (by simp)
  have hc := (hg (p.1.2,p.2)).hasFDerivAt.comp p
    (((hasFDerivAt_snd (𝕜 := ℝ) (p := p.1)).comp p
      (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).prodMk
        (hasFDerivAt_snd (𝕜 := ℝ) (p := p)))
  have hd := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).prodMk hc
  change HasFDerivAt (toricSuspension F) _ p at hd
  rw [hd.fderiv]
  change (v.1,fderiv ℝ (fun q : ℝ × PlanePhase ι => toricFlow F q.1 q.2)
    (p.1.2,p.2) (v.1.2,v.2)) = _
  rw [joint_flow_fderiv (toricFlow_smooth hF) (toricFlow_hasDerivAt hF)]

theorem toricSuspension_pullback {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (p v w : Plane × PlanePhase ι) :
    productForm phaseArea (fderiv ℝ (toricSuspension F) p v)
      (fderiv ℝ (toricSuspension F) p w) =
    oneCovectorForm phaseArea 1 (fderiv ℝ (toricFunction F) p.2) v w := by
  rw [toricSuspension_fderiv hF,toricSuspension_fderiv hF]
  apply suspension_form_identity phaseArea_skew (toricFlow_symplectic hF p.1.2 p.2)
  intro u
  rw [hamiltonianField_contraction phaseArea_isInvertible]
  have hh : fderiv ℝ (toricHamiltonian F) (p.1.2,toricFlow F p.1.2 p.2)
      (0,fderiv ℝ (toricFlow F p.1.2) p.2 u) =
      fderiv ℝ (toricFunction F) (toricFlow F p.1.2 p.2)
        (fderiv ℝ (toricFlow F p.1.2) p.2 u) := by
    have hd := ((toricFunction_smooth hF).differentiable (by simp) _).hasFDerivAt.comp
      (p.1.2,toricFlow F p.1.2 p.2) (hasFDerivAt_snd (𝕜 := ℝ))
    exact congrArg (fun L : (ℝ × PlanePhase ι) →L[ℝ] ℝ =>
      L (0,fderiv ℝ (toricFlow F p.1.2) p.2 u)) hd.fderiv
  rw [hh,toricFlow_energy_differential hF]


end

section
open scoped ContDiff
open Set Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def toricSuspensionInverse (F : (ι → ℝ) → ℝ) (p : Plane × PlanePhase ι) : Plane × PlanePhase ι :=
  (p.1,toricFlow F (-p.1.2) p.2)

@[fun_prop] theorem toricSuspensionInverse_smooth {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (toricSuspensionInverse F) := by
  have ht : ContDiff ℝ ∞ (fun p : Plane × PlanePhase ι => -p.1.2) :=
    (contDiff_snd.comp contDiff_fst).neg
  have hz : ContDiff ℝ ∞ (fun p : Plane × PlanePhase ι => toricFlow F (-p.1.2) p.2) := by
    convert! (toricFlow_smooth hF).comp (ht.prodMk contDiff_snd) using 1
  exact contDiff_fst.prodMk hz

omit [Fintype ι] in
@[simp] theorem toricSuspensionInverse_left (F : (ι → ℝ) → ℝ) (p : Plane × PlanePhase ι) :
    toricSuspensionInverse F (toricSuspension F p) = p := by
  simp only [toricSuspensionInverse,toricSuspension,toricFlow_add,neg_add_cancel,toricFlow_zero]

omit [Fintype ι] in
@[simp] theorem toricSuspensionInverse_right (F : (ι → ℝ) → ℝ) (p : Plane × PlanePhase ι) :
    toricSuspension F (toricSuspensionInverse F p) = p := by
  simp only [toricSuspensionInverse,toricSuspension,toricFlow_add,add_neg_cancel,toricFlow_zero]

def toricSuspensionHomeomorph {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) :
    (Plane × PlanePhase ι) ≃ₜ (Plane × PlanePhase ι) where
  toFun := toricSuspension F
  invFun := toricSuspensionInverse F
  left_inv := toricSuspensionInverse_left F
  right_inv := toricSuspensionInverse_right F
  continuous_toFun := (toricSuspension_smooth hF).continuous
  continuous_invFun := (toricSuspensionInverse_smooth hF).continuous

omit [Fintype ι] in
@[simp] theorem toricSuspension_moments (F : (ι → ℝ) → ℝ) (p : Plane × PlanePhase ι) :
    planeMoments (toricSuspension F p).2 = planeMoments p.2 := toricFlow_moments F _ _

omit [Fintype ι] in
@[simp] theorem toricSuspensionInverse_moments (F : (ι → ℝ) → ℝ) (p : Plane × PlanePhase ι) :
    planeMoments (toricSuspensionInverse F p).2 = planeMoments p.2 := toricFlow_moments F _ _


end

section
open scoped ContDiff Topology
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def layerOrder : (Plane × E) ≃L[ℝ] ((ℝ × E) × ℝ) :=
  (ContinuousLinearEquiv.prodAssoc ℝ ℝ ℝ E).trans (ContinuousLinearEquiv.prodComm ℝ ℝ (ℝ × E))

omit [CompleteSpace E] in
@[simp] theorem layerOrder_apply (p : Plane × E) : layerOrder p = ((p.1.2,p.2),p.1.1) := rfl
omit [CompleteSpace E] in
@[simp] theorem layerOrder_symm_apply (p : (ℝ × E) × ℝ) : layerOrder.symm p = ((p.2,p.1.1),p.1.2) := rfl

def stripChart (f : Plane × E → ℝ) (p : Plane × E) : Plane × E := ((f p,p.1.2),p.2)

omit [CompleteSpace E] in
@[fun_prop] theorem stripChart_smooth {f : Plane × E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (stripChart f) := (hf.prodMk (contDiff_snd.comp contDiff_fst)).prodMk contDiff_snd

theorem stripChart_inverse {f : Plane × E → ℝ} (hf : ContDiff ℝ ∞ f)
    {V : Set E} (hV : IsOpen V) {a b : ℝ} (hab : a < b) (H : E → ℝ)
    (hderiv : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v ∈ V, ∀ s ∈ Ioo a b,
      0 < deriv (fun r => f ((r,T),v)) s)
    (hlo : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v ∈ V, f ((a,T),v) = 0)
    (hhi : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v ∈ V, H v < f ((b,T),v)) :
    ∃ (W : Set (Plane × E)) (g : Plane × E → Plane × E),
      IsOpen W ∧ ContDiffOn ℝ ∞ g W ∧
      W = stripChart f '' ((Ioo a b ×ˢ Ioo (0:ℝ) 1) ×ˢ V) ∧
      (∀ p, p.1.2 ∈ Ioo (0:ℝ) 1 → p.2 ∈ V → 0 < p.1.1 → p.1.1 < H p.2 → p ∈ W) ∧
      (∀ p ∈ (Ioo a b ×ˢ Ioo (0:ℝ) 1) ×ˢ V, g (stripChart f p) = p) ∧
      (∀ p ∈ W, g p ∈ (Ioo a b ×ˢ Ioo (0:ℝ) 1) ×ˢ V ∧ stripChart f (g p) = p) := by
  let e : (Plane × E) ≃L[ℝ] ((ℝ × E) × ℝ) := layerOrder
  let f' : (ℝ × E) × ℝ → ℝ := f ∘ e.symm
  have hf' : ContDiff ℝ ∞ f' := hf.comp e.symm.contDiff
  obtain ⟨W,g,hWo,hgs,hWe,havailable,hleft,hright⟩ := monotone_strip_inverse hf'
    (isOpen_Ioo.prod hV) hab (h := fun q : ℝ × E => H q.2)
    (fun q hq s hs => hderiv q.1 hq.1 q.2 hq.2 s hs)
    (fun q hq => hlo q.1 hq.1 q.2 hq.2)
    (fun q hq => hhi q.1 hq.1 q.2 hq.2)
  let G : Plane × E → Plane × E := fun p => ((g (e p),p.1.2),p.2)
  refine ⟨e ⁻¹' W,G,hWo.preimage e.continuous,?_,?_,?_,?_,?_⟩
  · have hg : ContDiffOn ℝ ∞ (fun p => g (e p)) (e ⁻¹' W) :=
      hgs.comp e.contDiff.contDiffOn (fun _ hp => hp)
    exact (hg.prodMk (contDiff_snd.comp contDiff_fst).contDiffOn).prodMk contDiff_snd.contDiffOn
  · ext p
    constructor
    · intro hp
      obtain ⟨q,hq,hqe⟩ := by simpa only [hWe] using hp
      refine ⟨e.symm q,⟨⟨hq.2,hq.1.1⟩,hq.1.2⟩,?_⟩
      apply e.injective
      change (q.1,f' q) = e p
      exact hqe
    · rintro ⟨q,hq,rfl⟩
      change e (stripChart f q) ∈ W
      rw [hWe]
      exact ⟨e q,⟨⟨hq.1.2,hq.2⟩,hq.1.1⟩,rfl⟩
  · intro p hpT hpV hp0 hpH
    exact havailable (p.1.2,p.2) ⟨hpT,hpV⟩ p.1.1 hp0 hpH
  · intro p hp
    have hh := hleft (p.1.2,p.2) ⟨hp.1.2,hp.2⟩ p.1.1 hp.1.1
    change ((g ((p.1.2,p.2),f p),p.1.2),p.2) = p
    change g ((p.1.2,p.2),f p) = p.1.1 at hh
    rw [hh]
  · intro p hp
    have hh := hright (e p) hp
    refine ⟨⟨⟨hh.2.1,hh.1.1⟩,hh.1.2⟩,?_⟩
    change ((f ((g (e p),p.1.2),p.2),p.1.2),p.2) = p
    have he : f ((g (e p),p.1.2),p.2) = p.1.1 := hh.2.2
    rw [he]


end

open scoped ContDiff Topology
open Set Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def layerChart (F : (ι → ℝ) → ℝ) (f : Plane × PlanePhase ι → ℝ) :
    Plane × PlanePhase ι → Plane × PlanePhase ι := toricSuspension F ∘ stripChart f

@[fun_prop] theorem layerChart_smooth {F : (ι → ℝ) → ℝ} {f : Plane × PlanePhase ι → ℝ}
    (hF : ContDiff ℝ ∞ F) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (layerChart F f) :=
  (toricSuspension_smooth hF).comp (stripChart_smooth hf)

def layerForm (F : (ι → ℝ) → ℝ) (f : Plane × PlanePhase ι → ℝ)
    (p : Plane × PlanePhase ι) :
    (Plane × PlanePhase ι) →L[ℝ] (Plane × PlanePhase ι) →L[ℝ] ℝ :=
  let dt := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ Plane (PlanePhase ι))
  let β := fderiv ℝ f p + (fderiv ℝ (toricFunction F) p.2).comp (ContinuousLinearMap.snd ℝ Plane (PlanePhase ι))
  phaseArea.bilinearComp (ContinuousLinearMap.snd ℝ Plane (PlanePhase ι))
    (ContinuousLinearMap.snd ℝ Plane (PlanePhase ι)) + β.smulRight dt - dt.smulRight β

omit [DecidableEq ι] in
theorem layerForm_apply (F : (ι → ℝ) → ℝ) (f : Plane × PlanePhase ι → ℝ)
    (p v w : Plane × PlanePhase ι) :
    layerForm F f p v w = phaseArea v.2 w.2 +
      (fderiv ℝ f p v + fderiv ℝ (toricFunction F) p.2 v.2)*w.1.2 -
      v.1.2*(fderiv ℝ f p w + fderiv ℝ (toricFunction F) p.2 w.2) := by
  simp [layerForm,ContinuousLinearMap.smulRight_apply,smul_eq_mul,mul_add]

omit [DecidableEq ι] in
theorem stripChart_fderiv {f : Plane × PlanePhase ι → ℝ} (hf : ContDiff ℝ ∞ f)
    (p v : Plane × PlanePhase ι) : fderiv ℝ (stripChart f) p v = ((fderiv ℝ f p v,v.1.2),v.2) := by
  have hd := (((hf.differentiable (by simp) p).hasFDerivAt).prodMk
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := p.1)).comp p (hasFDerivAt_fst (𝕜 := ℝ) (p := p)))).prodMk
      (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  change HasFDerivAt (stripChart f) _ p at hd
  rw [hd.fderiv]
  rfl

theorem layerChart_pullback {F : (ι → ℝ) → ℝ} {f : Plane × PlanePhase ι → ℝ}
    (hF : ContDiff ℝ ∞ F) (hf : ContDiff ℝ ∞ f) (p v w : Plane × PlanePhase ι) :
    productForm phaseArea (fderiv ℝ (layerChart F f) p v)
      (fderiv ℝ (layerChart F f) p w) = layerForm F f p v w := by
  rw [layerChart,fderiv_comp p ((toricSuspension_smooth hF).differentiable (by simp) _)
    ((stripChart_smooth hf).differentiable (by simp) _)]
  simp only [ContinuousLinearMap.comp_apply]
  rw [toricSuspension_pullback hF,stripChart_fderiv hf,stripChart_fderiv hf,
    oneCovectorForm_apply,layerForm_apply]
  change phaseArea v.2 w.2 + 1*(fderiv ℝ f p v*w.1.2-v.1.2*fderiv ℝ f p w) +
    fderiv ℝ (toricFunction F) p.2 v.2*w.1.2-v.1.2*fderiv ℝ (toricFunction F) p.2 w.2 = _
  ring

theorem layerChart_inverse {F : (ι → ℝ) → ℝ} {f : Plane × PlanePhase ι → ℝ}
    (hF : ContDiff ℝ ∞ F) (hf : ContDiff ℝ ∞ f)
    {V : Set (ι → ℝ)} (hV : IsOpen (planeMoments ⁻¹' V)) {a b : ℝ} (hab : a < b)
    (H : (ι → ℝ) → ℝ)
    (hderiv : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v, planeMoments v ∈ V → ∀ s ∈ Ioo a b,
      0 < deriv (fun r => f ((r,T),v)) s)
    (hlo : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v, planeMoments v ∈ V → f ((a,T),v) = 0)
    (hhi : ∀ T ∈ Ioo (0:ℝ) 1, ∀ v, planeMoments v ∈ V → H (planeMoments v) < f ((b,T),v)) :
    ∃ (W : Set (Plane × PlanePhase ι)) (g : Plane × PlanePhase ι → Plane × PlanePhase ι),
      IsOpen W ∧ ContDiffOn ℝ ∞ g W ∧
      W = layerChart F f '' ((Ioo a b ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V)) ∧
      (∀ p, p.1.2 ∈ Ioo (0:ℝ) 1 → planeMoments p.2 ∈ V →
        0 < p.1.1 → p.1.1 < H (planeMoments p.2) → p ∈ W) ∧
      (∀ p ∈ (Ioo a b ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V), g (layerChart F f p) = p) ∧
      (∀ p ∈ W, g p ∈ (Ioo a b ×ˢ Ioo (0:ℝ) 1) ×ˢ (planeMoments ⁻¹' V) ∧ layerChart F f (g p) = p) := by
  obtain ⟨W,g,hWo,hgs,hWe,hav,hl,hr⟩ := stripChart_inverse hf hV hab (H ∘ planeMoments) hderiv hlo hhi
  let e := toricSuspensionHomeomorph hF
  let G := g ∘ toricSuspensionInverse F
  have hpre : e.symm ⁻¹' W = e '' W := by
    ext p
    exact ⟨fun hp => ⟨e.symm p,hp,e.apply_symm_apply p⟩,by rintro ⟨p,hp,rfl⟩; simpa using hp⟩
  refine ⟨e '' W,G,e.isOpen_image.mpr hWo,?_,?_,?_,?_,?_⟩
  · apply hgs.comp (toricSuspensionInverse_smooth hF).contDiffOn
    intro p hp
    change p ∈ e.symm ⁻¹' W
    rw [hpre]
    exact hp
  · rw [hWe,←image_comp]
    rfl
  · intro p hpT hpV hp0 hpH
    refine ⟨e.symm p,?_,e.apply_symm_apply p⟩
    apply hav (e.symm p) hpT
    · change planeMoments (toricSuspensionInverse F p).2 ∈ V
      simpa only [toricSuspensionInverse_moments] using hpV
    · exact hp0
    · change p.1.1 < H (planeMoments (toricSuspensionInverse F p).2)
      simpa using hpH
  · intro p hp
    change g (toricSuspensionInverse F (toricSuspension F (stripChart f p))) = p
    rw [toricSuspensionInverse_left]
    exact hl p hp
  · rintro p ⟨z,hz,rfl⟩
    have hge : G (e z) = g z := by
      change g (toricSuspensionInverse F (toricSuspension F z)) = g z
      rw [toricSuspensionInverse_left]
    rw [hge]
    refine ⟨(hr z hz).1,?_⟩
    change toricSuspension F (stripChart f (g z)) = toricSuspension F z
    rw [(hr z hz).2]



end PackingSufficiencySupport.Hamiltonian
end

end OAI
