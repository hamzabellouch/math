import Mathlib
import OAI.Geometry.BallPacking.CircleAction.CircleRelativeRadialMoser

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold
open scoped ContDiff Manifold Topology

section

variable {ι κ : Type} [Fintype ι] [Fintype κ]

 theorem phaseDot_rotate (s : ℝ) (z v : PlanePhase ι) :
    phaseDot (phaseRotate s z) (phaseRotate s v)=phaseDot z v := by
  simp only [phaseRotate_apply,map_add,map_smul,add_apply,smul_apply,smul_eq_mul,
    phaseDot_J_left,phaseDot_J_right,phaseArea_J_left]
  linear_combination (phaseDot z v)*Real.sin_sq_add_cos_sq s

 theorem phaseArea_rotate (s : ℝ) (z v : PlanePhase ι) :
    phaseArea (phaseRotate s z) (phaseRotate s v)=phaseArea z v := by
  simp only [phaseRotate_apply,map_add,map_smul,add_apply,smul_apply,smul_eq_mul,
    phaseArea_J_left,phaseArea_J_right,phaseDot_J_left]
  linear_combination (phaseArea z v)*Real.sin_sq_add_cos_sq s

 theorem phaseCircleAction_differential (s : ℝ) (z : PlanePhase ι) :
    phaseCircleAction.differential s z=phaseRotate (2*Real.pi*s) := by
  change mfderiv 𝓘(ℝ,PlanePhase ι) 𝓘(ℝ,PlanePhase ι)
    (phaseRotate (2*Real.pi*s)) z=_
  rw [mfderiv_eq_fderiv,(phaseRotate (2*Real.pi*s)).fderiv]

 theorem degreeHopfDifference_rotate {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) {q : ℝ}
    (hrot : ∀ s z,F (phaseRotate s z)=phaseRotate (q*s) (F z)) (c s : ℝ)
    (z v : PlanePhase ι) :
    degreeHopfDifference q F c (phaseRotate s z) (phaseRotate s v)=degreeHopfDifference q F c z v := by
  simp only [degreeHopfDifference,Pi.sub_apply,Pi.smul_apply,sub_apply,smul_apply,
    primitivePullback,ContinuousLinearMap.comp_apply,
    linear_equivariant_fderiv hF (phaseRotate s) (phaseRotate (q*s)) (hrot s),hrot,
    hopfPrimitive_linear_invariant _ (phaseDot_rotate _) (phaseArea_rotate _)]

 theorem cutoffDegreePrimitive_rotate {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) {q : ℝ}
    (hrot : ∀ s z,F (phaseRotate s z)=phaseRotate (q*s) (F z))
    (c d : ℝ) (χ : ℝ → ℝ) (t s : ℝ) (z v : PlanePhase ι) :
    cutoffDegreePrimitive q F c d χ t (phaseRotate s z) (phaseRotate s v)=
      cutoffDegreePrimitive q F c d χ t z v := by
  simp only [cutoffDegreePrimitive,add_apply,smul_apply,phaseSq_rotate,
    degreeHopfDifference_rotate hF hrot,standardLiouville,phaseArea_rotate]

 theorem cutoffDegreeForm_circle_invariant {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (hF0 : ∀ z,z≠0 → F z≠0) {q : ℝ}
    (hrot : ∀ s z,F (phaseRotate s z)=phaseRotate (q*s) (F z))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ=ᶠ[𝓝 (0:ℝ)] 0)
    (c d s t : ℝ) (z : PlanePhase ι) :
    (manifoldExteriorOneForm (cutoffDegreePrimitive q F c d χ t) (phaseCircleAction.slice s z)).bilinearComp
      (phaseCircleAction.differential s z) (phaseCircleAction.differential s z)=
      manifoldExteriorOneForm (cutoffDegreePrimitive q F c d χ t) z := by
  have hΓ : ContDiff ℝ ∞ (cutoffDegreePrimitive q F c d χ t) :=
    cutoffDegreePrimitive_slice_smooth hF hF0 hχ hχ0 q c d t
  rw [phaseCircleAction_differential]
  ext v w
  simp only [ContinuousLinearMap.bilinearComp_apply,vector_exteriorOneForm]
  exact exterior_linear_invariant (phaseRotate (2*Real.pi*s)) hΓ.contDiffAt
    (cutoffDegreePrimitive_rotate hF hrot c d χ t (2*Real.pi*s)) v w

end

section

variable {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]

 theorem cutoffDegreePrimitive_linear_pullback {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (e : PlanePhase ν →L[ℝ] PlanePhase ι)
    (heD : ∀ z v,phaseDot (e z) (e v)=phaseDot z v)
    (heA : ∀ z v,phaseArea (e z) (e v)=phaseArea z v)
    (q c d t : ℝ) (χ : ℝ → ℝ) :
    primitivePullback (cutoffDegreePrimitive q F c d χ t) e=
      cutoffDegreePrimitive q (F ∘ e) c d χ t := by
  funext z
  ext v
  simp only [cutoffDegreePrimitive,primitivePullback,ContinuousLinearMap.comp_apply,e.fderiv,
    add_apply,smul_apply,smul_eq_mul,degreeHopfDifference,Pi.sub_apply,Pi.smul_apply,sub_apply,
    standardLiouville,hopfPrimitive,phaseSq,heD,heA,
    fderiv_comp z (hF.differentiable (by simp) (e z)) (e.differentiableAt),Function.comp_apply]

 theorem cutoffDegreeForm_subspace_nondegenerate {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (hF0 : ∀ z,z≠0 → F z≠0) {q : ℝ}
    (hD : ∀ z,fderiv ℝ F z z=q•F z)
    (hJ : ∀ z v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v))
    (e : PlanePhase ν →L[ℝ] PlanePhase ι)
    (heD : ∀ z v,phaseDot (e z) (e v)=phaseDot z v)
    (heA : ∀ z v,phaseArea (e z) (e v)=phaseArea z v)
    (heJ : ∀ z,e (phaseJ z)=phaseJ (e z))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ=ᶠ[𝓝 (0:ℝ)] 0)
    (hχr : ∀ a,χ a∈Icc (0:ℝ) 1) {c d : ℝ} (hc : 0<c) (hd : 0≤d)
    (hq : 0≤q) (hdq : q*d<1) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (z : PlanePhase ν) :
    ((manifoldExteriorOneForm (cutoffDegreePrimitive q F c d χ t) (e z)).bilinearComp e e).IsInvertible := by
  have hn (z : PlanePhase ν) (hz : z≠0) : e z≠0 := by
    intro he
    have hh := heD z z
    rw [he,map_zero] at hh
    exact (phaseSq_pos hz).ne' hh.symm
  have hcomp : ContDiff ℝ ∞ (F ∘ e) := hF.comp e.contDiff
  have hcompD (z : PlanePhase ν) : fderiv ℝ (F ∘ e) z z=q•(F ∘ e) z := by
    rw [fderiv_comp z (hF.differentiable (by simp) (e z)) e.differentiableAt,e.fderiv,
      ContinuousLinearMap.comp_apply,hD,Function.comp_apply]
  have hcompJ (z v : PlanePhase ν) :
      fderiv ℝ (F ∘ e) z (phaseJ v)=phaseJ (fderiv ℝ (F ∘ e) z v) := by
    rw [fderiv_comp z (hF.differentiable (by simp) (e z)) e.differentiableAt,e.fderiv]
    simp only [ContinuousLinearMap.comp_apply,heJ,hJ]
  have hh := cutoffDegreePrimitive_nondegenerate hcomp (fun z hz => hF0 _ (hn z hz))
    hcompD hcompJ hχ hχ0 hχr hc hd hq hdq ht z
  have hΓ : ContDiff ℝ ∞ (cutoffDegreePrimitive q F c d χ t) :=
    cutoffDegreePrimitive_slice_smooth hF hF0 hχ hχ0 q c d t
  have hext := primitivePullback_exteriorAt hΓ.contDiffAt e.contDiff.contDiffAt (x := z)
  rw [cutoffDegreePrimitive_linear_pullback hF e heD heA,e.fderiv] at hext
  rw [vector_exteriorOneForm,←hext]
  exact hh

end

section

variable {ι κ : Type} [Fintype ι] [Fintype κ]

 theorem euler_circle_curve_derivative {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) {q : ℝ}
    (hDJ : ∀ z,fderiv ℝ F z (phaseJ z)=q•phaseJ (F z)) (s : ℝ) (z : PlanePhase ι) :
    HasDerivAt (fun t => F (phaseRotate t z)) (q•phaseJ (F (phaseRotate s z))) s := by
  have hh := (hF.differentiable (by simp) (phaseRotate s z)).hasFDerivAt.comp_hasDerivAt s
    (phaseRotate_hasDerivAt s z)
  simpa only [hDJ,Function.comp_def] using hh

 theorem euler_circle_untwisted_derivative {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) {q : ℝ}
    (hDJ : ∀ z,fderiv ℝ F z (phaseJ z)=q•phaseJ (F z)) (s : ℝ) (z : PlanePhase ι) :
    HasDerivAt (fun t => phaseRotate (-q*t) (F (phaseRotate t z))) 0 s := by
  have hL : HasDerivAt (fun t : ℝ => -q*t) (-q) s := by
    simpa only [mul_one,Function.id_def] using (hasDerivAt_id s).const_mul (-q)
  have hg := euler_circle_curve_derivative hF hDJ s z
  have hJg := (phaseJ (ι := κ)).hasFDerivAt.comp_hasDerivAt s hg
  have hh := (((Real.hasDerivAt_cos (-q*s)).scomp s hL).smul hg).add
    (((Real.hasDerivAt_sin (-q*s)).scomp s hL).smul hJg)
  change HasDerivAt (fun t => phaseRotate (-q*t) (F (phaseRotate t z))) _ s at hh
  convert! hh using 1
  simp only [Function.comp_apply,map_smul,phaseJ_sq,smul_neg,smul_smul,smul_eq_mul]
  module

 theorem euler_circle_equivariant {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) {q : ℝ}
    (hD : ∀ z,fderiv ℝ F z z=q•F z)
    (hJ : ∀ z v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v)) (s : ℝ) (z : PlanePhase ι) :
    F (phaseRotate s z)=phaseRotate (q*s) (F z) := by
  have hDJ (z : PlanePhase ι) : fderiv ℝ F z (phaseJ z)=q•phaseJ (F z) := by rw [hJ,hD,map_smul]
  have hc := is_const_of_deriv_eq_zero
    (fun t => (euler_circle_untwisted_derivative hF hDJ t z).differentiableAt)
    (fun t => (euler_circle_untwisted_derivative hF hDJ t z).deriv) s 0
  simp only [mul_zero,phaseRotate_zero] at hc
  have hh := congrArg (phaseRotate (q*s)) hc
  rw [←phaseRotate_add] at hh
  simpa only [neg_mul,add_neg_cancel,phaseRotate_zero] using hh

end

section
variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
 theorem splitInclusion_isSmoothEmbedding (L : (F × G) ≃L[ℝ] E) :
    IsSmoothEmbedding 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ (splitInclusion L) := by
  have hi : IsImmersionOfComplement G 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ (splitInclusion L) := by
    intro x
    apply IsImmersionAtOfComplement.mk_of_continuousAt (splitInclusion L).continuous.continuousAt L
      (chartAt F x) (chartAt E (splitInclusion L x)) (mem_chart_source F x)
      (mem_chart_source E (splitInclusion L x))
      (IsManifold.chart_mem_maximalAtlas x) (IsManifold.chart_mem_maximalAtlas (splitInclusion L x))
    intro y _
    simp [splitInclusion,chartAt_self_eq]
  refine ⟨hi.isImmersion,?_⟩
  exact L.toHomeomorph.isEmbedding.comp (isEmbedding_prodMkLeft (0:G))

end

section

variable {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]

 theorem exists_degree_relative_radial_moser
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
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ=ᶠ[𝓝 (0:ℝ)] 0)
    (hχr : ∀ a,χ a∈Icc (0:ℝ) 1) {c d : ℝ} (hc : 0<c) (hd : 0≤d)
    (hq : 0≤q) (hdq : q*d<1)
    {K : Set (PlanePhase ι)} (hK : IsCompact K)
    (hKr : ∀ x∈K,∀ y,phaseSq y=phaseSq x → y∈K) :
    ∃ Φ Ψ : ℝ × PlanePhase ι → PlanePhase ι,
      ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Ψ ∧
      (∀ x,Φ (0,x)=x) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x,Ψ (t,Φ (t,x))=x ∧ Φ (t,Ψ (t,x))=x) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x,phaseSq (Φ (t,x))=phaseSq x) ∧
      (∀ t∈Icc (0:ℝ) 1,(fun x => Φ (t,x)) '' range e=range e) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x∈K,∀ v w,
        manifoldPullback Φ (fun s => manifoldExteriorOneForm (cutoffDegreePrimitive q F c d χ s)) t x v w=
          c*phaseArea v w) := by
  have hdata := cutoffDegreePrimitive_moser_data hF hF0 hD hJ hχ hχ0 hχr hc hd hq hdq
  have heq (s : ℝ) (z : PlanePhase ν) :
      e ((phaseCircleAction (ι := ν)).slice s z)=(phaseCircleAction (ι := ι)).slice s (e z) := by
    change e (phaseRotate (2*Real.pi*s) z)=phaseRotate (2*Real.pi*s) (e z)
    simp only [phaseRotate_apply,map_add,map_smul,heJ]
  have hDJ (z : PlanePhase ι) : fderiv ℝ F z (phaseJ z)=q•phaseJ (F z) := by rw [hJ,hD,map_smul]
  obtain ⟨Φ,Ψ,hΦ,hΨ,h0,hi,hr,hepres,hω⟩ := exists_circle_relative_radial_moser hdata
    phaseCircleAction phaseCircleAction (by positivity : 2*Real.pi≠0) phaseCircleAction_generator
    e P hPe he heq (fun s t z => cutoffDegreeForm_circle_invariant hF hF0
      (euler_circle_equivariant hF hD hJ) hχ hχ0 c d s t z)
    (fun t ht z => cutoffDegreeForm_subspace_nondegenerate hF hF0 hD hJ e heD heA heJ hχ hχ0 hχr hc hd hq hdq ht z)
    hK isOpen_univ (subset_univ K) hKr hc.ne'
    (fun s z _ v => cutoffDegreePrimitive_circle_contraction hF hF0 hDJ hχ c d s z v)
    (fun s z => cutoffDegreePrimitive_time_circle hF hF0 hDJ hχ hχ0 c d s z)
  refine ⟨Φ,Ψ,hΦ,hΨ,h0,hi,hr,hepres,?_⟩
  intro t ht x hx v w
  rw [hω t ht x hx v w,vector_exteriorOneForm]
  have hezero : cutoffDegreePrimitive q F c d χ 0=c•(standardLiouville (ι := ι)) := by
    funext z
    simp only [cutoffDegreePrimitive,zero_mul,zero_smul,add_zero,Pi.smul_apply]
  rw [hezero,euclideanExteriorOneForm_smul c
    ((standardLiouville_smooth (ι := ι)).contDiffAt.differentiableAt (by simp)),standardLiouville_exterior]
  rfl

end

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem diffeomorphicFormPullback_inverse {f : E → F} {g : F → E}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hfg : Function.RightInverse g f)
    (Ω₀ : E → E →L[ℝ] E →L[ℝ] ℝ) (Ω₁ : F → F →L[ℝ] F →L[ℝ] ℝ)
    (hω : ∀ x v w,Ω₁ (f x) (fderiv ℝ f x v) (fderiv ℝ f x w)=Ω₀ x v w)
    (y v w : F) :
    Ω₀ (g y) (fderiv ℝ g y v) (fderiv ℝ g y w)=Ω₁ y v w := by
  have he : (fun z => f (g z))=id := funext hfg
  have hd := (hf.differentiable (by simp) (g y)).hasFDerivAt.comp y
    (hg.differentiable (by simp) y).hasFDerivAt
  have hD (u : F) : fderiv ℝ f (g y) (fderiv ℝ g y u)=u := by
    have hh := congrArg (fun L => L u) hd.fderiv
    change fderiv ℝ (fun z => f (g z)) y u=_ at hh
    rw [he,fderiv_id] at hh
    exact hh.symm
  rw [←hω (g y),hfg,hD,hD]

end

variable {ι : Type} [Fintype ι]

 theorem radius_preserving_fderiv {f : PlanePhase ι → PlanePhase ι}
    (hf : ContDiff ℝ ∞ f) (hr : ∀ z,phaseSq (f z)=phaseSq z) (z v : PlanePhase ι) :
    phaseDot (f z) (fderiv ℝ f z v)=phaseDot z v := by
  have he : (fun x => phaseSq (f x))=phaseSq := funext hr
  have h := (phaseSq_hasFDerivAt (f z)).comp z (hf.differentiable (by simp) z).hasFDerivAt
  have hd := congrArg (fun L => L v) h.fderiv
  change fderiv ℝ (fun x => phaseSq (f x)) z v=_ at hd
  rw [he,phaseSq_fderiv] at hd
  simp only [ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul] at hd
  linarith

 theorem moment_pullback_generator {f g : PlanePhase ι → PlanePhase ι}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hgf : LeftInverse g f) (hfg : RightInverse g f)
    (hr : ∀ z,phaseSq (f z)=phaseSq z)
    {Ω : PlanePhase ι → PlanePhase ι →L[ℝ] PlanePhase ι →L[ℝ] ℝ}
    {c : ℝ} {z : PlanePhase ι}
    (hsk : ∀ y v w,Ω y v w= -Ω y w v)
    (hnd : (Ω (f z)).IsInvertible)
    (hm : ∀ y v,Ω y v (phaseJ y)=c*phaseDot y v)
    (hω : ∀ v w,Ω (f z) (fderiv ℝ f z v) (fderiv ℝ f z w)=c*phaseArea v w) :
    fderiv ℝ f z (phaseJ z)=phaseJ (f z) := by
  have he : (fun x => f (g x))=id := funext hfg
  have hd := (hf.differentiable (by simp) (g (f z))).hasFDerivAt.comp (f z)
    (hg.differentiable (by simp) (f z)).hasFDerivAt
  have hD (v : PlanePhase ι) : fderiv ℝ f z (fderiv ℝ g (f z) v)=v := by
    have hh := congrArg (fun L => L v) hd.fderiv
    change fderiv ℝ (fun x => f (g x)) (f z) v=_ at hh
    rw [he,fderiv_id,hgf z] at hh
    exact hh.symm
  rcases hnd with ⟨L,hL⟩
  apply L.injective
  change L.toContinuousLinearMap _=L.toContinuousLinearMap _
  rw [hL]
  ext v
  calc
    _= -Ω (f z) v (fderiv ℝ f z (phaseJ z)) := hsk _ _ _
    _= -Ω (f z) v (phaseJ (f z)) := by
      congr 1
      rw [←hD v,hω,phaseArea_J_right,hm,radius_preserving_fderiv hf hr,phaseDot_symm]
    _=_ := (hsk _ _ _).symm

 theorem circle_equivariant_on_radius {f : PlanePhase ι → PlanePhase ι}
    (hf : ContDiff ℝ ∞ f) {K : Set (PlanePhase ι)}
    (hKr : ∀ x∈K,∀ y,phaseSq y=phaseSq x → y∈K)
    (hJ : ∀ z∈K,fderiv ℝ f z (phaseJ z)=phaseJ (f z))
    (s : ℝ) {z : PlanePhase ι} (hz : z∈K) :
    f (phaseRotate s z)=phaseRotate s (f z) := by
  have hd (t : ℝ) : HasDerivAt (fun u => f (phaseRotate u z)) (phaseJ (f (phaseRotate t z))) t := by
    have hh := (hf.differentiable (by simp) (phaseRotate t z)).hasFDerivAt.comp_hasDerivAt t
      (phaseRotate_hasDerivAt t z)
    simpa only [Function.comp_def,hJ _ (hKr z hz _ (phaseSq_rotate t z))] using hh
  have hu (t : ℝ) : HasDerivAt (fun u => phaseRotate (-u) (f (phaseRotate u z))) 0 t := by
    have hL := (hasDerivAt_id t).neg
    have hJg := (phaseJ (ι := ι)).hasFDerivAt.comp_hasDerivAt t (hd t)
    have hh := (((Real.hasDerivAt_cos (-t)).scomp t hL).smul (hd t)).add
      (((Real.hasDerivAt_sin (-t)).scomp t hL).smul hJg)
    change HasDerivAt (fun u => phaseRotate (-u) (f (phaseRotate u z))) _ t at hh
    convert! hh using 1
    simp only [Function.comp_apply,phaseJ_sq,smul_neg,smul_eq_mul]
    module
  have hc := is_const_of_deriv_eq_zero (fun t => (hu t).differentiableAt) (fun t => (hu t).deriv) s 0
  simp only [neg_zero,phaseRotate_zero] at hc
  have hh := congrArg (phaseRotate s) hc
  rw [←phaseRotate_add,add_neg_cancel,phaseRotate_zero] at hh
  exact hh

end PackingSufficiencySupport.Hamiltonian
end

end OAI
