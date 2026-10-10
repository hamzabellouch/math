import Mathlib
import OAI.Geometry.BallPacking.Forms.ManifoldExteriorAlgebra

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold DiagonalQuadrics
open scoped ContDiff Manifold Topology BigOperators

section

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem manifoldExteriorOneForm_sub_at {α β : ManifoldOneForm E M} {x : M}
    (hα : ContDiffAt ℝ ∞ (chartOneForm α x) (extChartAt 𝓘(ℝ,E) x x))
    (hβ : ContDiffAt ℝ ∞ (chartOneForm β x) (extChartAt 𝓘(ℝ,E) x x)) :
    manifoldExteriorOneForm (α-β) x=manifoldExteriorOneForm α x-manifoldExteriorOneForm β x := by
  have he : chartOneForm (α-β) x=chartOneForm α x-chartOneForm β x :=
    funext (chartOneForm_sub α β x)
  simp only [manifoldExteriorOneForm,euclideanExteriorOneForm,he,
    fderiv_sub (hα.differentiableAt (by simp)) (hβ.differentiableAt (by simp))]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.bilinearComp_apply,sub_apply,ContinuousLinearMap.flip_apply]
  ring

omit [NormedAddCommGroup P] [NormedSpace ℝ P]
  [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in

theorem parameterManifoldPullbackOneForm_inverse_apply
    (e : PartialDiffeomorph 𝓘(ℝ,F) 𝓘(ℝ,E) N M ∞)
    (α : P → ManifoldOneForm E M) (p : P) {x : M} (hx : x∈e.target) (v : E) :
    parameterManifoldPullbackOneForm (E := E) (F := F) α e p (e.symm x)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) e.symm x v)=α p x v := by
  have hd := handle_mfderiv_symm_comp e.symm hx
  change α p (e (e.symm x))
    ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e (e.symm x))
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) e.symm x v))=α p x v
  have he : α p (e (e.symm x))=α p x := congrArg (α p) (e.right_inv hx)
  rw [he]
  exact congrArg (α p x) (congrArg (fun D : E →L[ℝ] E => D v) hd)

end

section

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem IsPrimitiveFamily.intrinsic {Ω : P → ManifoldTwoForm E M}
    {α : P → ManifoldOneForm E M} (hα : IsPrimitiveFamily Ω α) (p : P) (x : M) :
    manifoldExteriorOneForm (α p) x=Ω p x := by
  have hx := mem_extChartAt_source (I := 𝓘(ℝ,E)) x
  have he := hα.exterior p x (extChartAt 𝓘(ℝ,E) x x) ((extChartAt 𝓘(ℝ,E) x).map_source hx)
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  change euclideanExteriorOneForm (chartOneForm (α p) x) (extChartAt 𝓘(ℝ,E) x x)
    (chartDifferential x x v) (chartDifferential x x w)=Ω p x v w
  rw [he]
  exact chartTwoForm_apply_chart hx v w

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem manifoldExteriorOneForm_add_at {α β : ManifoldOneForm E M} {x : M}
    (hα : ContDiffAt ℝ ∞ (chartOneForm α x) (extChartAt 𝓘(ℝ,E) x x))
    (hβ : ContDiffAt ℝ ∞ (chartOneForm β x) (extChartAt 𝓘(ℝ,E) x x)) :
    manifoldExteriorOneForm (α+β) x=manifoldExteriorOneForm α x+manifoldExteriorOneForm β x := by
  have he : chartOneForm (α+β) x=chartOneForm α x+chartOneForm β x :=
    funext (chartOneForm_add α β x)
  simp only [manifoldExteriorOneForm,he,euclideanExteriorOneForm_add
    (hα.differentiableAt (by simp)) (hβ.differentiableAt (by simp))]
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rfl

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem manifoldExteriorOneForm_smul_at (a : ℝ) {α : ManifoldOneForm E M} {x : M}
    (hα : ContDiffAt ℝ ∞ (chartOneForm α x) (extChartAt 𝓘(ℝ,E) x x)) :
    manifoldExteriorOneForm (a • α) x=a • manifoldExteriorOneForm α x := by
  have he : chartOneForm (a • α) x=a • chartOneForm α x :=
    funext (chartOneForm_smul a α x)
  simp only [manifoldExteriorOneForm,he,
    euclideanExteriorOneForm_smul a (hα.differentiableAt (by simp))]
  rfl

end

section

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem chartOneForm_model (α : V → V →L[ℝ] ℝ) (c y : V) : chartOneForm α c y=α y := by
  simp only [chartOneForm,chartDifferential,extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe,PartialEquiv.refl_symm,fderiv_id,
    mfderiv_eq_fderiv,ContinuousLinearMap.inverse_id,ContinuousLinearMap.comp_id,id_eq]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem manifoldExteriorOneForm_model (α : V → V →L[ℝ] ℝ) (x : V) :
    manifoldExteriorOneForm α x=euclideanExteriorOneForm α x := by
  rw [manifoldExteriorOneForm,show chartOneForm α x=α from funext (chartOneForm_model α x)]
  simp only [chartDifferential,
    extChartAt_model_space_eq_id,PartialEquiv.refl_coe,mfderiv_eq_fderiv,fderiv_id,id_eq]
  ext u v
  rfl

def linearLiouville (Ω : V →L[ℝ] V →L[ℝ] ℝ) : V → V →L[ℝ] ℝ := fun v => (1/2:ℝ) • Ω v

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem linearLiouville_smooth (Ω : V →L[ℝ] V →L[ℝ] ℝ) : ContDiff ℝ ∞ (linearLiouville Ω) :=
  Ω.contDiff.const_smul _

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem linearLiouville_exterior (Ω : V →L[ℝ] V →L[ℝ] ℝ) (hs : ∀ u v,Ω u v= -Ω v u) (x : V) :
    manifoldExteriorOneForm (linearLiouville Ω) x=Ω := by
  rw [manifoldExteriorOneForm_model]
  have hd : fderiv ℝ (linearLiouville Ω) x=(1/2:ℝ) • Ω :=
    ((Ω.hasFDerivAt).const_smul (1/2:ℝ)).fderiv
  simp only [euclideanExteriorOneForm,hd]
  ext u v
  change (1/2:ℝ)*Ω u v-(1/2:ℝ)*Ω v u=Ω u v
  rw [hs v u]
  ring

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem flatProduct_snd_derivative (z : M × V) :
    mfderiv 𝓘(ℝ,E × V) 𝓘(ℝ,V) (Prod.snd : M × V → V) z=
      ContinuousLinearMap.snd ℝ E V := by
  rw [show 𝓘(ℝ,E × V)=(𝓘(ℝ,E)).prod 𝓘(ℝ,V) from modelWithCornersSelf_prod]
  exact mfderiv_snd

def productVerticalLiouville (Ω : V →L[ℝ] V →L[ℝ] ℝ) : ManifoldOneForm (E × V) (M × V) :=
  manifoldPullbackOneForm (fun _ => linearLiouville Ω) (Prod.snd : M × V → V) 0

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem productVerticalLiouville_apply (Ω : V →L[ℝ] V →L[ℝ] ℝ) (z : M × V) (v : E × V) :
    productVerticalLiouville Ω z v=(1/2:ℝ)*Ω z.2 v.2 := by
  simp only [productVerticalLiouville,manifoldPullbackOneForm,manifoldMapDifferential,
    flatProduct_snd_derivative,ContinuousLinearMap.comp_apply]
  rfl

 theorem productVerticalLiouville_smooth (Ω : V →L[ℝ] V →L[ℝ] ℝ) :
    SmoothOneFormFamily (fun _ : ℝ => (productVerticalLiouville Ω : ManifoldOneForm (E × V) (M × V))) := by
  exact manifoldPullbackOneForm_smooth (α := fun _ => linearLiouville Ω)
    (e := (Prod.snd : M × V → V)) flatProduct_snd_smooth (fun c => by
    simpa only [chartOneForm_model,Function.comp_def] using
      ((linearLiouville_smooth Ω).comp (contDiff_snd (E := ℝ))).contDiffOn)

 theorem productVerticalLiouville_exterior (Ω : V →L[ℝ] V →L[ℝ] ℝ)
    (hs : ∀ u v,Ω u v= -Ω v u) (z : M × V) :
    manifoldExteriorOneForm (productVerticalLiouville Ω) z=
      Ω.bilinearComp (ContinuousLinearMap.snd ℝ E V) (ContinuousLinearMap.snd ℝ E V) := by
  have ha : ContDiffAt ℝ ∞ (chartOneForm (linearLiouville Ω) z.2)
      (extChartAt 𝓘(ℝ,V) z.2 z.2) := by
    rw [show chartOneForm (linearLiouville Ω) z.2=linearLiouville Ω from
      funext (chartOneForm_model (linearLiouville Ω) z.2)]
    exact (linearLiouville_smooth Ω).contDiffAt
  rw [productVerticalLiouville,manifold_pullback_exterior_at ha flatProduct_snd_smooth.contMDiffAt]
  simp only [manifoldPullbackTwoForm,linearLiouville_exterior Ω hs,manifoldMapDifferential,
    flatProduct_snd_derivative]

def productCouplingPrimitive (Ω : V →L[ℝ] V →L[ℝ] ℝ)
    (Γ : V → ManifoldOneForm E M) : ManifoldOneForm (E × V) (M × V) :=
  productVerticalLiouville Ω+productHorizontalLift Γ

 theorem productCouplingPrimitive_smooth (Ω : V →L[ℝ] V →L[ℝ] ℝ)
    {Γ : ℝ × V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ) :
    SmoothOneFormFamily (fun t => productCouplingPrimitive Ω (fun v => Γ (t,v))) :=
  (productVerticalLiouville_smooth Ω).add (productHorizontalLift_smooth hΓ)

 theorem productCouplingPrimitive_exterior (Ω : V →L[ℝ] V →L[ℝ] ℝ)
    (hs : ∀ u v,Ω u v= -Ω v u) {Γ : V → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) (z : M × V) :
    manifoldExteriorOneForm (productCouplingPrimitive Ω Γ) z=globalHorizontalCoupling Ω Γ z := by
  have hg : SmoothOneFormFamily (fun q : ℝ × V => Γ q.2) := hΓ.comp contDiff_snd
  have hh := productHorizontalLift_smooth hg
  rw [productCouplingPrimitive,manifoldExteriorOneForm_add_at
    ((productVerticalLiouville_smooth Ω).spatial_smooth 0 z (mem_extChartAt_target z))
    (hh.spatial_smooth 0 z (mem_extChartAt_target z)),productVerticalLiouville_exterior Ω hs]
  rfl

end

section
variable {ι : Type*} [Fintype ι]

def standardLiouville (z : PlanePhase ι) : PlanePhase ι →L[ℝ] ℝ :=
  (1/2:ℝ) • phaseArea z

theorem standardLiouville_smooth : ContDiff ℝ ∞ (standardLiouville (ι := ι)) :=
  (phaseArea (ι := ι)).contDiff.const_smul _

theorem standardLiouville_exterior (z : PlanePhase ι) :
    euclideanExteriorOneForm standardLiouville z=phaseArea := by
  have hd : fderiv ℝ (standardLiouville (ι := ι)) z=(1/2:ℝ) • phaseArea :=
    ((phaseArea (ι := ι)).hasFDerivAt.const_smul (1/2:ℝ)).fderiv
  ext u v
  simp only [euclideanExteriorOneForm,hd,sub_apply,
    ContinuousLinearMap.flip_apply,smul_apply,smul_eq_mul]
  rw [phaseArea_skew v u]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def verticalLiouville : ManifoldOneForm (E × PlanePhase ι) (M × PlanePhase ι) :=
  manifoldPullbackOneForm (fun _ => standardLiouville) Prod.snd 0

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
@[simp] theorem verticalLiouville_apply (z : M × PlanePhase ι) (v : E × PlanePhase ι) :
    verticalLiouville z v=(1/2:ℝ)*phaseArea z.2 v.2 := by
  change standardLiouville z.2 (mfderiv 𝓘(ℝ,E × PlanePhase ι) 𝓘(ℝ,PlanePhase ι) Prod.snd z v)=_
  rw [flatProduct_snd_derivative]
  rfl

theorem verticalLiouville_smooth :
    SmoothOneFormFamily (fun _ : ℝ => (verticalLiouville : ManifoldOneForm (E × PlanePhase ι) (M × PlanePhase ι))) := by
  have hα : SmoothOneFormFamily (fun _ : ℝ => (standardLiouville (ι := ι))) :=
    vector_oneForm_smooth standardLiouville_smooth
  intro c
  exact manifoldPullbackOneForm_smooth (α := fun _ : ℝ => (standardLiouville (ι := ι)))
    (flatProduct_snd_smooth (E := E) (M := M)) hα c

theorem verticalLiouville_exterior (z : M × PlanePhase ι) :
    manifoldExteriorOneForm verticalLiouville z=
      (phaseArea (ι := ι)).bilinearComp (ContinuousLinearMap.snd ℝ E (PlanePhase ι))
        (ContinuousLinearMap.snd ℝ E (PlanePhase ι)) := by
  have hα : ∀ c : PlanePhase ι,ContDiffOn ℝ ∞ (chartOneForm standardLiouville c)
      (extChartAt 𝓘(ℝ,PlanePhase ι) c).target := by
    intro c
    rw [show chartOneForm standardLiouville c=standardLiouville from funext (vector_chartOneForm standardLiouville c)]
    exact standardLiouville_smooth.contDiffOn
  rw [verticalLiouville,manifold_pullback_exterior hα flatProduct_snd_smooth z]
  simp only [manifoldPullbackTwoForm,vector_exteriorOneForm,standardLiouville_exterior,
    manifoldMapDifferential,flatProduct_snd_derivative]

end

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def primitivePullback (α : F → F →L[ℝ] ℝ) (g : E → F) (x : E) : E →L[ℝ] ℝ :=
  (α (g x)).comp (fderiv ℝ g x)

theorem primitivePullback_smooth {α : F → F →L[ℝ] ℝ} {g : E → F}
    (hα : ContDiff ℝ ∞ α) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (primitivePullback α g) :=
  (hα.comp hg).clm_comp (hg.fderiv_right (by simp))

theorem primitivePullback_exterior {α : F → F →L[ℝ] ℝ} {g : E → F}
    (hα : ContDiff ℝ ∞ α) (hg : ContDiff ℝ ∞ g) (x : E) :
    euclideanExteriorOneForm (primitivePullback α g) x=
      (euclideanExteriorOneForm α (g x)).bilinearComp (fderiv ℝ g x) (fderiv ℝ g x) := by
  have hh := manifold_pullback_exterior (α := α) (g := g)
    (fun c => by
      rw [show chartOneForm α c=α from funext (vector_chartOneForm α c)]
      exact hα.contDiffOn)
    hg.contMDiff x
  have he : manifoldPullbackOneForm (fun _ => α) g 0=primitivePullback α g := by
    funext z
    simp [manifoldPullbackOneForm,manifoldMapDifferential,mfderiv_eq_fderiv,primitivePullback]
  rw [he] at hh
  simpa only [vector_exteriorOneForm,manifoldPullbackOneForm,manifoldPullbackTwoForm,
    manifoldMapDifferential,mfderiv_eq_fderiv,primitivePullback] using hh

end

variable {ι : Type*} [Fintype ι]

 def hopfPrimitive (c : ℝ) (z : PlanePhase ι) : PlanePhase ι →L[ℝ] ℝ :=
  (c/(2*phaseSq z)) • phaseArea z

 theorem hopfPrimitive_smoothAt (c : ℝ) {z : PlanePhase ι} (hz : z≠0) :
    ContDiffAt ℝ ∞ (hopfPrimitive c) z := by
  exact (contDiffAt_const.div (contDiffAt_const.mul phaseSq_smooth.contDiffAt)
    (mul_ne_zero (by norm_num) (phaseSq_pos hz).ne')).smul (phaseArea (ι := ι)).contDiff.contDiffAt

 theorem hopfPrimitive_fderiv (c : ℝ) {z : PlanePhase ι} (hz : z≠0) (v w : PlanePhase ι) :
    fderiv ℝ (hopfPrimitive c) z v w=
      c/(2*phaseSq z)*phaseArea v w-c/(phaseSq z)^2*phaseDot z v*phaseArea z w := by
  have hc := ((hasDerivAt_inv (phaseSq_pos hz).ne').comp_hasFDerivAt z
    (phaseSq_hasFDerivAt z)).const_mul (c/2)
  have hc' : HasFDerivAt (fun y : PlanePhase ι => c/(2*phaseSq y))
      ((-c/(phaseSq z)^2) • phaseDot z) z := by
    have he : (fun y : PlanePhase ι => c/(2*phaseSq y))=(fun y => c/2*(phaseSq y)⁻¹) := by
      funext y
      ring
    rw [he]
    apply hc.congr_fderiv
    ext v
    simp only [smul_apply,smul_eq_mul,smul_smul]
    ring
  have hd := hc'.smul (phaseArea (ι := ι)).hasFDerivAt
  rw [show fderiv ℝ (hopfPrimitive c) z=_ from hd.fderiv]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,smul_eq_mul]
  ring

 def hopfForm (c : ℝ) := euclideanExteriorOneForm (hopfPrimitive (ι := ι) c)

 theorem hopfForm_apply (c : ℝ) {z : PlanePhase ι} (hz : z≠0) (v w : PlanePhase ι) :
    hopfForm c z v w=c/phaseSq z*phaseArea v w-
      c/(phaseSq z)^2*(phaseDot z v*phaseArea z w-phaseDot z w*phaseArea z v) := by
  simp only [hopfForm,euclideanExteriorOneForm,sub_apply,
    ContinuousLinearMap.flip_apply,hopfPrimitive_fderiv c hz,phaseArea_skew w v]
  ring

 theorem hopfPrimitive_radial (c : ℝ) (z : PlanePhase ι) : hopfPrimitive c z z=0 := by
  simp only [hopfPrimitive,smul_apply,smul_eq_mul,phaseArea_self,mul_zero]

 theorem hopfPrimitive_circle (c : ℝ) {z : PlanePhase ι} (hz : z≠0) :
    hopfPrimitive c z (phaseJ z)=c/2 := by
  simp only [hopfPrimitive,smul_apply,smul_eq_mul,phaseArea_J_right,phaseSq]
  calc
    c/(2*phaseDot z z)*phaseDot z z=c/2*(phaseDot z z/phaseDot z z) := by ring
    _=c/2 := by rw [div_self (show phaseDot z z≠0 from (phaseSq_pos hz).ne'),mul_one]

 theorem hopfForm_radial (c : ℝ) {z : PlanePhase ι} (hz : z≠0) (v : PlanePhase ι) :
    hopfForm c z z v=0 := by
  rw [hopfForm_apply c hz]
  simp only [phaseArea_self,mul_zero,sub_zero,phaseSq]
  field_simp [show phaseDot z z≠0 from (phaseSq_pos hz).ne']
  ring

 theorem hopfForm_circle (c : ℝ) {z : PlanePhase ι} (hz : z≠0) (v : PlanePhase ι) :
    hopfForm c z (phaseJ z) v=0 := by
  rw [hopfForm_apply c hz]
  simp only [phaseDot_J_right,phaseArea_J_left,phaseArea_self,neg_zero,zero_mul,
    phaseArea_J_right,phaseSq,zero_sub]
  field_simp [show phaseDot z z≠0 from (phaseSq_pos hz).ne']
  ring

 theorem hopfForm_complex_diagonal (c : ℝ) {z : PlanePhase ι} (hz : z≠0) (v : PlanePhase ι) :
    hopfForm c z v (phaseJ v)=c/(phaseSq z)^2*
      (phaseSq z*phaseSq v-((phaseDot z v)^2+(phaseArea z v)^2)) := by
  rw [hopfForm_apply c hz]
  simp only [phaseArea_J_right,phaseDot_J_right,phaseSq]
  field_simp [show phaseDot z z≠0 from (phaseSq_pos hz).ne']
  ring

 theorem hopfForm_semipositive {c : ℝ} (hc : 0≤c) {z : PlanePhase ι} (hz : z≠0)
    (v : PlanePhase ι) : 0≤hopfForm c z v (phaseJ v) := by
  rw [hopfForm_complex_diagonal c hz]
  exact mul_nonneg (div_nonneg hc (sq_nonneg _)) (sub_nonneg.mpr (phase_complex_cauchy z v))

theorem complexCartesian_complex_smul (ζ : ℂ) (z : ι → ℂ) :
    complexCartesian (ζ•z)=ζ.re•complexCartesian z+ζ.im•phaseJ (complexCartesian z) := by
  ext i <;> simp [complexCartesian_apply,Pi.smul_apply,Complex.mul_re,Complex.mul_im,phaseJ]; ring

theorem hopfForm_skew (c : ℝ) (z v w : PlanePhase ι) :
    hopfForm c z v w= -hopfForm c z w v := by
  simp only [hopfForm,euclideanExteriorOneForm,sub_apply,ContinuousLinearMap.flip_apply]
  ring

theorem hopfForm_complex_line (c : ℝ) {z : ι → ℂ} (hz : complexCartesian z≠0)
    (ζ : ℂ) (v : PlanePhase ι) : hopfForm c (complexCartesian z) (complexCartesian (ζ•z)) v=0 := by
  rw [complexCartesian_complex_smul]
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul,
    hopfForm_radial c hz,hopfForm_circle c hz,mul_zero,add_zero]

theorem complexPairing_complex_smul (ζ : ℂ) (z v : ι → ℂ) :
    complexPairing (ζ•z) (ζ•v)=(Complex.normSq ζ : ℂ)*complexPairing z v := by
  simp only [complexPairing,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [star_mul,Complex.star_def,Complex.normSq_eq_conj_mul_self]
  ring

theorem complexCartesian_smul_dot (ζ : ℂ) (z v : ι → ℂ) :
    phaseDot (complexCartesian (ζ•z)) (complexCartesian (ζ•v))=
      Complex.normSq ζ*phaseDot (complexCartesian z) (complexCartesian v) := by
  rw [←complexPairing_re,complexPairing_complex_smul,Complex.mul_re]
  simp [complexPairing_re]

theorem complexCartesian_smul_area (ζ : ℂ) (z v : ι → ℂ) :
    phaseArea (complexCartesian (ζ•z)) (complexCartesian (ζ•v))=
      Complex.normSq ζ*phaseArea (complexCartesian z) (complexCartesian v) := by
  rw [←complexPairing_im,complexPairing_complex_smul,Complex.mul_im]
  simp [complexPairing_im]

theorem hopfForm_complex_scale (c : ℝ) {ζ : ℂ} (hζ : ζ≠0) {z : ι → ℂ}
    (hz : complexCartesian z≠0) (v w : ι → ℂ) :
    hopfForm c (complexCartesian (ζ•z)) (complexCartesian (ζ•v)) (complexCartesian (ζ•w))=
      hopfForm c (complexCartesian z) (complexCartesian v) (complexCartesian w) := by
  have hn : Complex.normSq ζ≠0 := (Complex.normSq_pos.mpr hζ).ne'
  have hz' : complexCartesian (ζ•z)≠0 := by
    intro h
    have hs := complexCartesian_complex_smul_sq ζ z
    simp only [h,phaseSq,map_zero] at hs
    exact (mul_ne_zero hn (phaseSq_pos hz).ne') hs.symm
  rw [hopfForm_apply c hz',hopfForm_apply c hz,complexCartesian_complex_smul_sq,
    complexCartesian_smul_area,complexCartesian_smul_dot,complexCartesian_smul_area,
    complexCartesian_smul_dot,complexCartesian_smul_area]
  field_simp [hn,(phaseSq_pos hz).ne']

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hopfForm_variable_gauge {S : E → ℂ} {G : E → (ι → ℂ)} {x : E}
    (hS : DifferentiableAt ℝ S x) (hG : DifferentiableAt ℝ G x)
    (hSx : S x≠0) (hGx : complexCartesian (G x)≠0) (c : ℝ) (v w : E) :
    hopfForm c (complexCartesian (S x•G x))
      (fderiv ℝ (fun y => complexCartesian (S y•G y)) x v)
      (fderiv ℝ (fun y => complexCartesian (S y•G y)) x w)=
    hopfForm c (complexCartesian (G x))
      (fderiv ℝ (fun y => complexCartesian (G y)) x v)
      (fderiv ℝ (fun y => complexCartesian (G y)) x w) := by
  have hdG := complexCartesian.hasFDerivAt.comp x hG.hasFDerivAt
  have hd := complexCartesian.hasFDerivAt.comp x (hS.hasFDerivAt.smul hG.hasFDerivAt)
  have hz' : complexCartesian (S x•G x)≠0 := by
    intro h
    have hs := complexCartesian_complex_smul_sq (S x) (G x)
    simp only [h,phaseSq,map_zero] at hs
    exact (mul_ne_zero ((Complex.normSq_pos.mpr hSx).ne') (phaseSq_pos hGx).ne') hs.symm
  have hline (u : E) (q : PlanePhase ι) :
      hopfForm c (complexCartesian (S x•G x)) (complexCartesian (fderiv ℝ S x u•G x)) q=0 := by
    have he : fderiv ℝ S x u•G x=(fderiv ℝ S x u/S x)•(S x•G x) := by
      rw [smul_smul,div_mul_cancel₀ _ hSx]
    rw [he]
    exact hopfForm_complex_line c hz' _ q
  have hliner (u : E) (q : PlanePhase ι) :
      hopfForm c (complexCartesian (S x•G x)) q (complexCartesian (fderiv ℝ S x u•G x))=0 := by
    rw [hopfForm_skew,hline,neg_zero]
  rw [show fderiv ℝ (fun y => complexCartesian (S y•G y)) x=_ from hd.fderiv,
    show fderiv ℝ (fun y => complexCartesian (G y)) x=_ from hdG.fderiv]
  simp only [ContinuousLinearMap.comp_apply,add_apply,
    ContinuousLinearMap.smulRight_apply,smul_apply,
    map_add,ContinuousLinearEquiv.coe_coe]
  simp only [hline,hliner,add_zero]
  exact hopfForm_complex_scale c hSx hGx _ _

 theorem hopfPrimitive_complex_line (c : ℝ) {z : ι → ℂ} (hz : complexCartesian z≠0)
    (ζ : ℂ) : hopfPrimitive c (complexCartesian z) (complexCartesian (ζ•z))=(c/2)*ζ.im := by
  rw [complexCartesian_complex_smul]
  simp only [map_add,map_smul,hopfPrimitive_radial,hopfPrimitive_circle c hz,
    smul_eq_mul,mul_zero,zero_add]
  ring

 theorem hopfPrimitive_complex_scale (c : ℝ) {ζ : ℂ} (hζ : ζ≠0) {z : ι → ℂ}
    (hz : complexCartesian z≠0) (v : ι → ℂ) :
    hopfPrimitive c (complexCartesian (ζ•z)) (complexCartesian (ζ•v))=
      hopfPrimitive c (complexCartesian z) (complexCartesian v) := by
  have hn : Complex.normSq ζ≠0 := (Complex.normSq_pos.mpr hζ).ne'
  simp only [hopfPrimitive,smul_apply,smul_eq_mul,
    complexCartesian_complex_smul_sq,complexCartesian_smul_area]
  field_simp [hn,(phaseSq_pos hz).ne']

 variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 theorem hopfPrimitive_variable_gauge {S : E → ℂ} {G : E → (ι → ℂ)} {x : E}
    (hS : DifferentiableAt ℝ S x) (hG : DifferentiableAt ℝ G x)
    (hSx : S x≠0) (hGx : complexCartesian (G x)≠0) (c : ℝ) (v : E) :
    hopfPrimitive c (complexCartesian (S x•G x))
      (fderiv ℝ (fun y => complexCartesian (S y•G y)) x v)=
    hopfPrimitive c (complexCartesian (G x))
      (fderiv ℝ (fun y => complexCartesian (G y)) x v)+
        c/(2*Complex.normSq (S x))*complexArea (S x) (fderiv ℝ S x v) := by
  have hdG := complexCartesian.hasFDerivAt.comp x hG.hasFDerivAt
  have hd := complexCartesian.hasFDerivAt.comp x (hS.hasFDerivAt.smul hG.hasFDerivAt)
  have hz' : complexCartesian (S x•G x)≠0 := by
    intro h
    have hs := complexCartesian_complex_smul_sq (S x) (G x)
    simp only [h,phaseSq,map_zero] at hs
    exact (mul_ne_zero ((Complex.normSq_pos.mpr hSx).ne') (phaseSq_pos hGx).ne') hs.symm
  have he : fderiv ℝ S x v•G x=(fderiv ℝ S x v/S x)•(S x•G x) := by
    rw [smul_smul,div_mul_cancel₀ _ hSx]
  rw [show fderiv ℝ (fun y => complexCartesian (S y•G y)) x=_ from hd.fderiv,
    show fderiv ℝ (fun y => complexCartesian (G y)) x=_ from hdG.fderiv]
  simp only [ContinuousLinearMap.comp_apply,add_apply,
    ContinuousLinearMap.smulRight_apply,smul_apply,map_add,ContinuousLinearEquiv.coe_coe]
  rw [hopfPrimitive_complex_scale c hSx hGx,he,hopfPrimitive_complex_line c hz',complex_div_im]
  ring

 theorem complexAffineLift_derivative (z v : ι → ℂ) :
    fderiv ℝ complexAffineLift z v=fun i => match i with
      | none => 0
      | some i => v i := by
  have h : HasFDerivAt (complexAffineLift (ι := ι))
      (ContinuousLinearMap.pi fun i => match i with
        | none => 0
        | some i => (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℝ] ℂ)) z := by
    apply hasFDerivAt_pi.mpr
    intro i
    cases i with
    | none => exact hasFDerivAt_const _ _
    | some i => exact (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℝ] ℂ).hasFDerivAt
  rw [h.fderiv]
  funext i
  cases i <;> rfl

 theorem affineFSPrimitive_hopf (c : ℝ) (z v : ι → ℂ) :
    hopfPrimitive c (complexCartesian (complexAffineLift z))
      (complexCartesian (fderiv ℝ complexAffineLift z v))=
    affineFSPrimitive c (complexCartesian z) (complexCartesian v) := by
  rw [hopfPrimitive,complexAffineLift_sq,smul_apply,smul_eq_mul]
  change _=c/(2*(1+phaseSq (complexCartesian z)))*phaseArea (complexCartesian z) (complexCartesian v)
  congr 1
  rw [← complexPairing_im,← complexPairing_im,complexAffineLift_derivative]
  simp [complexPairing,Fintype.sum_option,complexAffineLift]

 theorem affineFSPrimitive_hopf_pullback {G : E → (ι → ℂ)} {x : E}
    (hG : DifferentiableAt ℝ G x) (c : ℝ) (v : E) :
    hopfPrimitive c (complexCartesian (complexAffineLift (G x)))
      (fderiv ℝ (fun y => complexCartesian (complexAffineLift (G y))) x v)=
    affineFSPrimitive c (complexCartesian (G x))
      (fderiv ℝ (fun y => complexCartesian (G y)) x v) := by
  have hL := complexAffineLift_smooth.differentiable (by simp) (G x)
  have hd := complexCartesian.hasFDerivAt.comp x (hL.hasFDerivAt.comp x hG.hasFDerivAt)
  have hd' := complexCartesian.hasFDerivAt.comp x hG.hasFDerivAt
  rw [show fderiv ℝ (fun y => complexCartesian (complexAffineLift (G y))) x=_ from hd.fderiv,
    show fderiv ℝ (fun y => complexCartesian (G y)) x=_ from hd'.fderiv]
  exact affineFSPrimitive_hopf c (G x) (fderiv ℝ G x v)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
