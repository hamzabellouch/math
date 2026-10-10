import Mathlib
import OAI.Geometry.BallPacking.Moser.ManifoldExteriorNaturality
import OAI.Geometry.BallPacking.CircleAction.CircleRelativeOneForm

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open scoped BigOperators
section

variable {ι : Type} [Fintype ι]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

 theorem exists_circle_relative_radial_moser
    {Ω : ℝ → ManifoldTwoForm (PlanePhase ι) (PlanePhase ι)}
    {α : ℝ → ManifoldOneForm (PlanePhase ι) (PlanePhase ι)}
    (h : ManifoldMoserData Ω α)
    (A : SmoothCircleAction (PlanePhase ι) (PlanePhase ι)) (B : SmoothCircleAction F F)
    {lam : ℝ} (hlam : lam≠0) (hgen : ∀ z,A.generator z=lam•phaseJ z)
    (e : F →L[ℝ] PlanePhase ι) (P : PlanePhase ι →L[ℝ] F)
    (hPe : P.comp e=ContinuousLinearMap.id ℝ F)
    (he : IsSmoothEmbedding 𝓘(ℝ,F) 𝓘(ℝ,PlanePhase ι) ∞ e)
    (heq : ∀ s b,e (B.slice s b)=A.slice s (e b))
    (hΩ : ∀ s t z,(Ω t (A.slice s z)).bilinearComp (A.differential s z) (A.differential s z)=Ω t z)
    (hi : ∀ t∈Icc (0:ℝ) 1,∀ b,((Ω t (e b)).bilinearComp e e).IsInvertible)
    {K O : Set (PlanePhase ι)} (hK : IsCompact K) (hO : IsOpen O) (hKO : K⊆O)
    (hKr : ∀ x∈K,∀ y,phaseSq y=phaseSq x → y∈K)
    {c : ℝ} (hc : c≠0)
    (hcircle : ∀ s,∀ z∈O,∀ v,Ω s z v (phaseJ z)=c*phaseDot z v)
    (ha : ∀ s z,α s z (phaseJ z)=0) :
    ∃ Φ Ψ : ℝ × PlanePhase ι → PlanePhase ι,
      ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Ψ ∧
      (∀ x,Φ (0,x)=x) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x,Ψ (t,Φ (t,x))=x ∧ Φ (t,Ψ (t,x))=x) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x,phaseSq (Φ (t,x))=phaseSq x) ∧
      (∀ t∈Icc (0:ℝ) 1,(fun x => Φ (t,x)) '' range e=range e) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x∈K,∀ v w,manifoldPullback Φ Ω t x v w=Ω 0 x v w) := by
  have hPe' (x : F) : P (e x)=x := congrArg (fun L : F →L[ℝ] F => L x) hPe
  have hclosed : IsClosed (range e) :=
    (LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.mpr (LeftInverse.injective hPe'))).isClosed_range
  have hI (b : F) : manifoldMapDifferential (E := PlanePhase ι) (F := F) e b=e := by
    simp only [manifoldMapDifferential,mfderiv_eq_fderiv,e.fderiv]
  obtain ⟨f,hf,hjet⟩ := exists_relative_global_potential h.smooth_two h.smooth_one he hclosed
    (isClosed_Icc (a := (0:ℝ)) (b := 1)) (by simpa only [hI] using hi)
  have hfs : ContDiff ℝ ∞ f := by
    rw [←modelWithCornersSelf_prod,chartedSpaceSelf_prod] at hf
    exact contMDiff_iff_contDiff.mp hf
  let β := correctedOneForm (E := PlanePhase ι) α f
  have hβ : ManifoldMoserData Ω β := h.corrected (by
    rw [←modelWithCornersSelf_prod,chartedSpaceSelf_prod]
    exact hfs.contMDiff)
  have hγ : ManifoldMoserData Ω (A.averageOneForm β) := A.averaged_moser_data hβ hΩ
  have hαgen (t : ℝ) (z : PlanePhase ι) : α t z (A.generator z)=0 := by
    rw [hgen,map_smul,ha,smul_zero]
  have hγcircle (t : ℝ) (z : PlanePhase ι) : A.averageOneForm β t z (phaseJ z)=0 := by
    have hh := A.averaged_corrected_generator_zero h.smooth_one hαgen hfs t z
    change A.averageOneForm β t z (A.generator z)=0 at hh
    rw [hgen,map_smul,smul_eq_mul] at hh
    exact (mul_eq_zero.mp hh).resolve_left hlam
  have hβnormal (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (b : F) (v : PlanePhase ι) :
      β t (e b) v=β t (e b) (e (symplecticProjection (Ω t (e b)) e v)) := by
    have hd := manifoldSpatialDifferential_of_jet (hjet t ht b).2
    rw [hI] at hd
    simp only [β,correctedOneForm,hd,symplecticNormalJet,add_apply,sub_apply,
      ContinuousLinearMap.comp_apply,symplecticProjection_leftInverse (hi t ht b)]
    ring
  have hγnormal (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (b : F) (v : PlanePhase ι) :
      A.averageOneForm β t (e b) v=A.averageOneForm β t (e b)
        (e (symplecticProjection (Ω t (e b)) e v)) := by
    have hh := A.averageOneForm_normal_annihilation B he.contMDiff heq
      (fun s t z u v => congrArg (fun L : PlanePhase ι →L[ℝ] PlanePhase ι →L[ℝ] ℝ => L u v) (hΩ s t z))
      hβ.smooth_one (by simpa only [manifoldPullbackTwoForm,hI] using hi t ht)
      (by simpa only [hI] using hβnormal t ht) b v
    simpa only [hI] using hh
  apply exists_compact_radial_relative_moser hγ hK hO hKO hKr hc hcircle
    (fun t z _ => hγcircle t z) e P hPe
  intro t ht b _
  have hh := moser_vector_tangent_of_annihilation (h.nondegenerate t ht (e b))
    (hi t ht b) (h.skew_intrinsic ht (e b)) (A.averageOneForm β t (e b)) (hγnormal t ht b)
  change e (P (-((Ω t (e b)).inverse (A.averageOneForm β t (e b))))) =
    -((Ω t (e b)).inverse (A.averageOneForm β t (e b)))
  rw [hh,hPe']

end
section

variable {ι κ : Type} [Fintype ι] [Fintype κ]

 theorem cutoffDegreePrimitive_smooth_family {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (hF0 : ∀ z,z≠0 → F z≠0) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ=ᶠ[𝓝 (0:ℝ)] 0) (q c d : ℝ) :
    SmoothOneFormFamily (cutoffDegreePrimitive q F c d χ) := by
  intro b
  simpa only [vector_chartOneForm] using
    (cutoffDegreePrimitive_smooth hF hF0 hχ hχ0 q c d).contDiffOn

 theorem cutoffDegreePrimitive_moser_data {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (hF0 : ∀ z,z≠0 → F z≠0) {q : ℝ}
    (hD : ∀ z,fderiv ℝ F z z=q•F z)
    (hJ : ∀ z v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ=ᶠ[𝓝 (0:ℝ)] 0)
    (hχr : ∀ a,χ a∈Icc (0:ℝ) 1) {c d : ℝ} (hc : 0<c) (hd : 0≤d)
    (hq : 0≤q) (hdq : q*d<1) :
    ManifoldMoserData (fun t => manifoldExteriorOneForm (cutoffDegreePrimitive q F c d χ t))
      (manifoldTimePrimitive (cutoffDegreePrimitive q F c d χ)) := by
  have hΓ := cutoffDegreePrimitive_smooth_family hF hF0 hχ hχ0 q c d
  refine ⟨manifoldExteriorOneForm_path_smooth hΓ,manifoldTimePrimitive_smooth hΓ,?_,?_,?_,?_⟩
  · intro t ht z
    rw [vector_exteriorOneForm]
    exact cutoffDegreePrimitive_nondegenerate hF hF0 hD hJ hχ hχ0 hχr hc hd hq hdq ht z
  · intro t _ b y _ u v
    simp only [vector_chartTwoForm]
    exact manifoldExteriorOneForm_skew _ _ _ _
  · intro t _ b y hy u v w
    exact manifoldExteriorOneForm_path_closed hΓ t b y hy u v w
  · intro t _ b y hy u v
    exact manifoldExteriorOneForm_path_time hΓ t b y hy u v

 theorem cutoffDegreePrimitive_circle_contraction {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (hF0 : ∀ z,z≠0 → F z≠0) {q : ℝ}
    (hDJ : ∀ z,fderiv ℝ F z (phaseJ z)=q•phaseJ (F z))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (c d t : ℝ) (z v : PlanePhase ι) :
    manifoldExteriorOneForm (cutoffDegreePrimitive q F c d χ t) z v (phaseJ z)=c*phaseDot z v := by
  rw [vector_exteriorOneForm]
  by_cases hz : z=0
  · subst z
    simp only [map_zero,zero_apply,mul_zero]
  · rw [cutoffDegreePrimitive_eq]
    exact radialDegreeConePrimitive_circle_contraction hF.contDiffAt hz (hF0 _ hz) (hDJ z)
      ((hχ.differentiable (by simp) _).const_mul (t*d)) c v

 theorem cutoffDegreePrimitive_time_circle {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (hF0 : ∀ z,z≠0 → F z≠0) {q : ℝ}
    (hDJ : ∀ z,fderiv ℝ F z (phaseJ z)=q•phaseJ (F z))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ=ᶠ[𝓝 (0:ℝ)] 0)
    (c d t : ℝ) (z : PlanePhase ι) :
    manifoldTimePrimitive (cutoffDegreePrimitive q F c d χ) t z (phaseJ z)=0 := by
  apply manifoldTimePrimitive_eval_constant (cutoffDegreePrimitive_smooth_family hF hF0 hχ hχ0 q c d)
  intro s
  by_cases hz : z=0
  · subst z
    simp only [map_zero]
  · simp only [cutoffDegreePrimitive,add_apply,smul_apply,smul_eq_mul,
      degreeHopfDifference_circle hz (hF0 _ hz) (hDJ z),mul_zero,add_zero]

end
section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def phaseShell (a b : ℝ) : Set (PlanePhase ι) := phaseSq ⁻¹' Icc a b

theorem phaseShell_isCompact (a b : ℝ) : IsCompact (phaseShell (ι := ι) a b) := by
  apply (isCompact_closedBall (0:PlanePhase ι) (max b 0+1)).of_isClosed_subset
    (isClosed_Icc.preimage phaseSq_smooth.continuous)
  intro z hz
  rw [Metric.mem_closedBall,dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ max b 0+1)).mpr
  intro i
  have hi : (z i).1*(z i).1+(z i).2*(z i).2≤phaseSq z := by
    simpa only [phaseSq,phaseDot_apply] using Finset.single_le_sum (f := fun j => (z j).1*(z j).1+(z j).2*(z j).2)
      (fun j _ => add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (Finset.mem_univ i)
  have hb := hz.2
  change phaseSq z≤b at hb
  rw [Prod.norm_def,max_le_iff]
  constructor
  · rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (z i).2,sq_nonneg (|(z i).1|-1),sq_abs (z i).1,le_max_left b 0,le_max_right b 0]
  · rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (z i).1,sq_nonneg (|(z i).2|-1),sq_abs (z i).2,le_max_left b 0,le_max_right b 0]

theorem phaseShell_nonzero {a b : ℝ} (ha : 0<a) {z : PlanePhase ι}
    (hz : z∈phaseShell a b) : z≠0 := by
  intro h
  have hh := hz.1
  change a≤phaseSq z at hh
  rw [h,phaseSq] at hh
  simp only [map_zero] at hh
  linarith

theorem phaseShell_radial (a b : ℝ) {x : PlanePhase ι} (hx : x∈phaseShell a b)
    {y : PlanePhase ι} (h : phaseSq y=phaseSq x) : y∈phaseShell a b := by
  change phaseSq y∈Icc a b
  rw [h]
  exact hx

theorem exists_global_homogeneous_cone_path
    {F : PlanePhase ι → PlanePhase κ} (hF : ContDiff ℝ ∞ F)
    (hF0 : ∀ z,z≠0 → F z≠0) {K : Set (PlanePhase ι)} (hK : IsCompact K)
    (hK0 : ∀ z∈K,z≠0) (c d : ℝ) :
    ∃ Γ : ℝ → ManifoldOneForm (PlanePhase ι) (PlanePhase ι),
      SmoothOneFormFamily Γ ∧ ∃ O : Set (PlanePhase ι),IsOpen O ∧ K⊆O ∧
      (∀ z∈O,z≠0) ∧ ∀ s,EqOn (Γ s) (homogeneousConePrimitive F c (s*d)) O := by
  let f : PlanePhase ι → (PlanePhase ι →L[ℝ] ℝ) × (PlanePhase ι →L[ℝ] ℝ) :=
    fun z => (homogeneousConePrimitive F c 0 z,homogeneousConePrimitive F c d z)
  have hf : ContDiffOn ℝ ∞ f ({0}ᶜ : Set (PlanePhase ι)) := by
    intro z hz
    exact ((homogeneousConePrimitive_smoothAt hF.contDiffAt hz (hF0 z hz) c 0).prodMk
      (homogeneousConePrimitive_smoothAt hF.contDiffAt hz (hF0 z hz) c d)).contDiffWithinAt
  obtain ⟨χ,_hχ,_hχc,_hχs,_hχr,_hχ1,hg,_hgc,hge⟩ :=
    exists_smooth_compact_extension hK isClosed_singleton.isOpen_compl hK0 hf
  let g := fun z => χ z • f z
  let Γ : ℝ → ManifoldOneForm (PlanePhase ι) (PlanePhase ι) :=
    fun s z => (1-s)•(g z).1+s•(g z).2
  have hΓe : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => Γ p.1 p.2) :=
    ((contDiff_const.sub contDiff_fst).smul (hg.fst.comp contDiff_snd)).add
      (contDiff_fst.smul (hg.snd.comp contDiff_snd))
  have hΓ : SmoothOneFormFamily Γ := by
    intro z
    simpa only [vector_chartOneForm] using hΓe.contDiffOn
  obtain ⟨A,hA,hKA,hAe⟩ := mem_nhdsSet_iff_exists.mp hge
  let O := A∩({0}ᶜ : Set (PlanePhase ι))
  refine ⟨Γ,hΓ,O,hA.inter isClosed_singleton.isOpen_compl,
    fun z hz => ⟨hKA hz,hK0 z hz⟩,fun _ hz => hz.2,?_⟩
  intro s z hz
  have he : g z=f z := hAe hz.1
  dsimp only [Γ]
  rw [he]
  exact homogeneousConePrimitive_affine F c d s z

theorem homogeneous_cone_path_properties
    {F : PlanePhase ι → PlanePhase κ} (hF : ContDiff ℝ ∞ F)
    (hF0 : ∀ z,z≠0 → F z≠0)
    (hD : ∀ z,fderiv ℝ F z z=(2:ℝ)•F z)
    (hJ : ∀ z v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v))
    {c d : ℝ} (hc : 0<c) (hd : 0≤d) (hdhalf : d<1/2)
    {Γ : ℝ → ManifoldOneForm (PlanePhase ι) (PlanePhase ι)} (hΓ : SmoothOneFormFamily Γ)
    {O : Set (PlanePhase ι)} (hO : IsOpen O) (hO0 : ∀ z∈O,z≠0)
    (heq : ∀ s,EqOn (Γ s) (homogeneousConePrimitive F c (s*d)) O) :
    (∀ s,∀ z∈O,manifoldExteriorOneForm (Γ s) z=
      euclideanExteriorOneForm (homogeneousConePrimitive F c (s*d)) z) ∧
    (∀ s,∀ z∈O,∀ v,manifoldExteriorOneForm (Γ s) z v (phaseJ z)=c*phaseDot z v) ∧
    (∀ s,∀ z∈O,manifoldTimePrimitive Γ s z (phaseJ z)=0) ∧
    (∀ s∈Icc (0:ℝ) 1,∀ z∈O,(manifoldExteriorOneForm (Γ s) z).IsInvertible) := by
  have he (s : ℝ) (z : PlanePhase ι) (hz : z∈O) :
      manifoldExteriorOneForm (Γ s) z=euclideanExteriorOneForm (homogeneousConePrimitive F c (s*d)) z := by
    rw [vector_exteriorOneForm,euclideanExteriorOneForm,euclideanExteriorOneForm]
    rw [Filter.EventuallyEq.fderiv_eq ((heq s).eventuallyEq_of_mem (hO.mem_nhds hz))]
  have hDJ (z : PlanePhase ι) : fderiv ℝ F z (phaseJ z)=(2:ℝ)•phaseJ (F z) := by
    rw [hJ,hD,map_smul]
  refine ⟨he,?_,?_,?_⟩
  · intro s z hz v
    rw [he s z hz]
    exact homogeneousConePrimitive_circle_contraction hF.contDiffAt (hO0 z hz) (hF0 z (hO0 z hz)) (hDJ z) c (s*d) v
  · intro s z hz
    apply manifoldTimePrimitive_eval_constant hΓ _ s
    intro t
    rw [heq t hz,heq 0 hz,homogeneousConePrimitive_circle (hO0 z hz) (hF0 z (hO0 z hz)) (hDJ z),
      homogeneousConePrimitive_circle (hO0 z hz) (hF0 z (hO0 z hz)) (hDJ z)]
  · intro s hs z hz
    rw [he s z hz]
    apply homogeneousConePrimitive_nondegenerate hF.contDiffAt (hO0 z hz)
      (hF0 z (hO0 z hz)) (hD z) (hJ z) hc (mul_nonneg hs.1 hd)
    exact lt_of_le_of_lt (by nlinarith [hs.2]) hdhalf

def homogeneousConeField (F : PlanePhase ι → PlanePhase κ) (c d s : ℝ) (z : PlanePhase ι) :=
  -(euclideanExteriorOneForm (homogeneousConePrimitive F c (s*d)) z).inverse
    (homogeneousConePrimitive F c d z-homogeneousConePrimitive F c 0 z)

theorem homogeneousCone_timePrimitive
    {F : PlanePhase ι → PlanePhase κ} {c d : ℝ}
    {Γ : ℝ → ManifoldOneForm (PlanePhase ι) (PlanePhase ι)} {z : PlanePhase ι}
    (he : ∀ s,Γ s z=homogeneousConePrimitive F c (s*d) z) (s : ℝ) :
    manifoldTimePrimitive Γ s z=homogeneousConePrimitive F c d z-homogeneousConePrimitive F c 0 z := by
  have he' : (fun s => Γ s z)=(fun s : ℝ => (1-s)•homogeneousConePrimitive F c 0 z+
      s•homogeneousConePrimitive F c d z) :=
    funext fun s => (he s).trans (homogeneousConePrimitive_affine F c d s z).symm
  have hd := (((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)).smul_const
    (homogeneousConePrimitive F c 0 z)).add
    ((hasDerivAt_id s).smul_const (homogeneousConePrimitive F c d z))
  simp only [Pi.sub_apply,id_eq] at hd
  rw [manifoldTimePrimitive,he']
  convert! hd.deriv using 1
  simp [sub_eq_add_neg,add_comm]

 theorem exists_homogeneousCone_shell_flow
    {F : PlanePhase ι → PlanePhase κ} (hF : ContDiff ℝ ∞ F)
    (hF0 : ∀ z,z≠0 → F z≠0)
    (hD : ∀ z,fderiv ℝ F z z=(2:ℝ)•F z)
    (hJ : ∀ z v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v))
    {c d a b : ℝ} (hc : 0<c) (hd : 0≤d) (hdhalf : d<1/2) (ha : 0<a) :
    ∃ Φ Ψ : ℝ × PlanePhase ι → PlanePhase ι,
      ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Ψ ∧
      (∀ x,Φ (0,x)=x) ∧
      (∀ s∈Icc (0:ℝ) 1,∀ x,Ψ (s,Φ (s,x))=x ∧ Φ (s,Ψ (s,x))=x) ∧
      (∀ s∈Icc (0:ℝ) 1,∀ x,phaseSq (Φ (s,x))=phaseSq x) ∧
      (∀ s∈Icc (0:ℝ) 1,∀ x∈phaseShell a b,∀ v w,
        euclideanExteriorOneForm (homogeneousConePrimitive F c (s*d)) (Φ (s,x))
            (fderiv ℝ (fun y => Φ (s,y)) x v) (fderiv ℝ (fun y => Φ (s,y)) x w)=
          euclideanExteriorOneForm (homogeneousConePrimitive F c 0) x v w) ∧
      ∃ V : ℝ × PlanePhase ι → PlanePhase ι,
        ContDiff ℝ ∞ V ∧
        (∀ x s,s∈Ioo (-2:ℝ) 2 → HasDerivAt (fun r => Φ (r,x)) (V (s,Φ (s,x))) s) ∧
        ∀ s∈Icc (0:ℝ) 1,∀ x∈phaseShell a b,V (s,x)=homogeneousConeField F c d s x := by
  obtain ⟨Γ,hΓ,O,hO,hKO,hO0,heq⟩ := exists_global_homogeneous_cone_path hF hF0
    (phaseShell_isCompact a b) (fun _ hz => phaseShell_nonzero ha hz) c d
  obtain ⟨he,hcircle,hβ,hinv⟩ := homogeneous_cone_path_properties hF hF0 hD hJ hc hd hdhalf hΓ hO hO0 heq
  obtain ⟨Φ,Ψ,hΦ,hΨ,hΦ0,hΦi,hΦr,hΦω,V,hV,hODE,hVe⟩ :=
    exists_compact_radial_exact_moser hΓ (phaseShell_isCompact a b) hO hKO
      (fun _ hx _ he => phaseShell_radial a b hx he) hc.ne' hcircle hβ
      (fun s hs z hz => hinv s hs z (hKO hz))
  refine ⟨Φ,Ψ,hΦ,hΨ,hΦ0,hΦi,hΦr,?_,V,hV,hODE,?_⟩
  · intro s hs x hx v w
    have hh := hΦω s hs x hx v w
    have hx' := hKO (phaseShell_radial a b hx (hΦr s hs x))
    simpa only [manifoldPullback,ContinuousLinearMap.bilinearComp_apply,
      preferredDifferential,mfderiv_eq_fderiv,he s _ hx',he 0 x (hKO hx),zero_mul] using hh
  · intro s hs x hx
    rw [hVe s hs x hx,manifoldMoserField,he s x (hKO hx),
      homogeneousCone_timePrimitive (fun r => heq r (hKO hx))]
    rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem moser_vector_natural
    {Ω₀ Ω₁ : E →L[ℝ] E →L[ℝ] ℝ} {α₀ α₁ : E →L[ℝ] ℝ} {L : E →L[ℝ] E}
    (h₀ : Ω₀.IsInvertible) (h₁ : Ω₁.IsInvertible) (hL : Function.Surjective L)
    (hΩ : ∀ u v, Ω₁ (L u) (L v) = Ω₀ u v)
    (hα : ∀ v, α₁ (L v) = α₀ v) :
    L (-Ω₀.inverse α₀) = -Ω₁.inverse α₁ := by
  apply h₁.injective
  ext w
  obtain ⟨v,rfl⟩ := hL w
  rw [hΩ,map_neg,h₀.self_apply_inverse,map_neg,h₁.self_apply_inverse]
  exact congrArg Neg.neg (hα v).symm

theorem linear_equivariant_fderiv {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (U : PlanePhase ι →L[ℝ] PlanePhase ι)
    (T : PlanePhase κ →L[ℝ] PlanePhase κ) (hFT : ∀ z,F (U z)=T (F z))
    (z v : PlanePhase ι) : fderiv ℝ F (U z) (U v)=T (fderiv ℝ F z v) := by
  have he : (fun z => F (U z))=(fun z => T (F z)) := funext hFT
  have h₁ := ((hF.differentiable (by simp) (U z)).hasFDerivAt).comp z U.hasFDerivAt
  have h₂ := T.hasFDerivAt.comp z ((hF.differentiable (by simp) z).hasFDerivAt)
  change HasFDerivAt (fun z => F (U z)) _ z at h₁
  rw [he] at h₁
  exact congrArg (fun L => L v) (h₁.unique h₂)

theorem hopfPrimitive_linear_invariant (U : PlanePhase ι →L[ℝ] PlanePhase ι)
    (hD : ∀ z v,phaseDot (U z) (U v)=phaseDot z v)
    (hA : ∀ z v,phaseArea (U z) (U v)=phaseArea z v)
    (c : ℝ) (z v : PlanePhase ι) : hopfPrimitive c (U z) (U v)=hopfPrimitive c z v := by
  simp only [hopfPrimitive,smul_apply,smul_eq_mul,phaseSq,hD,hA]

theorem mixedHopfPrimitive_linear_invariant {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (U : PlanePhase ι →L[ℝ] PlanePhase ι)
    (T : PlanePhase κ →L[ℝ] PlanePhase κ) (hFT : ∀ z,F (U z)=T (F z))
    (hUD : ∀ z v,phaseDot (U z) (U v)=phaseDot z v)
    (hUA : ∀ z v,phaseArea (U z) (U v)=phaseArea z v)
    (hTD : ∀ z v,phaseDot (T z) (T v)=phaseDot z v)
    (hTA : ∀ z v,phaseArea (T z) (T v)=phaseArea z v)
    (c d : ℝ) (z v : PlanePhase ι) :
    mixedHopfPrimitive F c d (U z) (U v)=mixedHopfPrimitive F c d z v := by
  simp only [mixedHopfPrimitive,Pi.add_apply,Pi.smul_apply,add_apply,smul_apply,smul_eq_mul,primitivePullback,
    ContinuousLinearMap.comp_apply,hopfPrimitive_linear_invariant U hUD hUA,
    linear_equivariant_fderiv hF U T hFT,hFT,hopfPrimitive_linear_invariant T hTD hTA]

theorem homogeneousConePrimitive_linear_invariant {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (U : PlanePhase ι →L[ℝ] PlanePhase ι)
    (T : PlanePhase κ →L[ℝ] PlanePhase κ) (hFT : ∀ z,F (U z)=T (F z))
    (hUD : ∀ z v,phaseDot (U z) (U v)=phaseDot z v)
    (hUA : ∀ z v,phaseArea (U z) (U v)=phaseArea z v)
    (hTD : ∀ z v,phaseDot (T z) (T v)=phaseDot z v)
    (hTA : ∀ z v,phaseArea (T z) (T v)=phaseArea z v)
    (c d : ℝ) (z v : PlanePhase ι) :
    homogeneousConePrimitive F c d (U z) (U v)=homogeneousConePrimitive F c d z v := by
  simp only [homogeneousConePrimitive,smul_apply,smul_eq_mul,phaseSq,hUD,
    mixedHopfPrimitive_linear_invariant hF U T hFT hUD hUA hTD hTA]

theorem exterior_linear_invariant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : E → E →L[ℝ] ℝ} (U : E →L[ℝ] E) {z : E}
    (hα : ContDiffAt ℝ ∞ α (U z)) (he : ∀ x v,α (U x) (U v)=α x v) (v w : E) :
    euclideanExteriorOneForm α (U z) (U v) (U w)=euclideanExteriorOneForm α z v w := by
  have he' : primitivePullback α U=α := by
    funext x
    ext v
    simpa only [primitivePullback,ContinuousLinearMap.comp_apply,U.fderiv] using he x v
  have hh := primitivePullback_exteriorAt hα U.contDiff.contDiffAt
  rw [he',U.fderiv] at hh
  exact (congrArg (fun B => B v w) hh).symm

theorem homogeneousConeField_linear_invariant {F : PlanePhase ι → PlanePhase κ}
    (hF : ContDiff ℝ ∞ F) (hF0 : ∀ z,z≠0 → F z≠0)
    (hD : ∀ z,fderiv ℝ F z z=(2:ℝ)•F z)
    (hJ : ∀ z v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v))
    (U : PlanePhase ι ≃L[ℝ] PlanePhase ι) (T : PlanePhase κ →L[ℝ] PlanePhase κ)
    (hFT : ∀ z,F (U z)=T (F z))
    (hUD : ∀ z v,phaseDot (U z) (U v)=phaseDot z v)
    (hUA : ∀ z v,phaseArea (U z) (U v)=phaseArea z v)
    (hTD : ∀ z v,phaseDot (T z) (T v)=phaseDot z v)
    (hTA : ∀ z v,phaseArea (T z) (T v)=phaseArea z v)
    {c d s : ℝ} (hc : 0<c) (hd : 0 ≤ s * d) (hdhalf : s * d < 1/2)
    {z : PlanePhase ι} (hz : z≠0) :
    homogeneousConeField F c d s (U z)=U (homogeneousConeField F c d s z) := by
  have hUz : U z≠0 := fun h => hz (U.injective (h.trans (map_zero U).symm))
  have hI (e : ℝ) (x v : PlanePhase ι) :=
    homogeneousConePrimitive_linear_invariant hF U.toContinuousLinearMap T hFT hUD hUA hTD hTA c e x v
  symm
  unfold homogeneousConeField
  apply moser_vector_natural (L := U.toContinuousLinearMap)
    (homogeneousConePrimitive_nondegenerate hF.contDiffAt hz (hF0 z hz) (hD z) (hJ z) hc hd hdhalf)
    (homogeneousConePrimitive_nondegenerate hF.contDiffAt hUz (hF0 _ hUz) (hD _) (hJ _) hc hd hdhalf)
    U.surjective
  · exact exterior_linear_invariant U.toContinuousLinearMap
      (homogeneousConePrimitive_smoothAt hF.contDiffAt hUz (hF0 _ hUz) c (s*d)) (hI (s*d))
  · intro v
    exact congrArg₂ (· - ·) (hI d z v) (hI 0 z v)

end

variable {ι : Type} [Fintype ι]

 def phaseRotate (s : ℝ) : PlanePhase ι →L[ℝ] PlanePhase ι :=
  Real.cos s • ContinuousLinearMap.id ℝ _+Real.sin s • phaseJ

 omit [Fintype ι] in
 theorem phaseRotate_apply (s : ℝ) (z : PlanePhase ι) :
    phaseRotate s z=Real.cos s•z+Real.sin s•phaseJ z := rfl

 theorem phaseRotate_smooth : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => phaseRotate p.1 p.2) := by
  simp only [phaseRotate_apply]
  exact (Real.contDiff_cos.comp contDiff_fst).smul contDiff_snd |>.add
    ((Real.contDiff_sin.comp contDiff_fst).smul ((phaseJ (ι := ι)).contDiff.comp contDiff_snd))

 omit [Fintype ι] in
 @[simp] theorem phaseRotate_zero (z : PlanePhase ι) : phaseRotate 0 z=z := by
  simp [phaseRotate]

 omit [Fintype ι] in
 theorem phaseRotate_add (s t : ℝ) (z : PlanePhase ι) :
    phaseRotate (s+t) z=phaseRotate s (phaseRotate t z) := by
  ext i <;> simp only [phaseRotate_apply,Pi.add_apply,Pi.smul_apply,Prod.smul_fst,Prod.smul_snd,
    Prod.fst_add,Prod.snd_add,phaseJ_apply,smul_eq_mul,Real.cos_add,Real.sin_add] <;> ring

 omit [Fintype ι] in
 theorem phaseRotate_period (s : ℝ) (z : PlanePhase ι) :
    phaseRotate (s+2*Real.pi) z=phaseRotate s z := by
  simp only [phaseRotate_apply,Real.cos_add_two_pi,Real.sin_add_two_pi]

 theorem phaseRotate_hasDerivAt (s : ℝ) (z : PlanePhase ι) :
    HasDerivAt (fun t => phaseRotate t z) (phaseJ (phaseRotate s z)) s := by
  have hh := ((Real.hasDerivAt_cos s).smul_const z).add
    ((Real.hasDerivAt_sin s).smul_const (phaseJ z))
  convert! hh using 1
  simp only [phaseRotate_apply,map_add,map_smul,phaseJ_sq,smul_neg,neg_smul]
  abel

 theorem phaseCircle_smooth :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,PlanePhase ι)) 𝓘(ℝ,PlanePhase ι) ∞
      (fun p : ℝ × PlanePhase ι => phaseRotate (2*Real.pi*p.1) p.2) := by
  let L : ℝ × PlanePhase ι →L[ℝ] ℝ × PlanePhase ι :=
    ((2*Real.pi) • ContinuousLinearMap.fst ℝ ℝ (PlanePhase ι)).prod
      (ContinuousLinearMap.snd ℝ ℝ (PlanePhase ι))
  have hh0 : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => phaseRotate p.1 p.2) := phaseRotate_smooth
  have hh1 : ContDiff ℝ ∞ ((fun p : ℝ × PlanePhase ι => phaseRotate p.1 p.2) ∘ L) :=
    hh0.comp L.contDiff
  have hh : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => phaseRotate (2*Real.pi*p.1) p.2) := by
    simpa only [Function.comp_def,L,ContinuousLinearMap.prod_apply,smul_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',smul_eq_mul] using hh1
  rw [←modelWithCornersSelf_prod,chartedSpaceSelf_prod]
  exact hh.contMDiff

 def phaseCircleAction : SmoothCircleAction (PlanePhase ι) (PlanePhase ι) where
  toFun p := phaseRotate (2*Real.pi*p.1) p.2
  smooth := phaseCircle_smooth
  zero z := by simp
  add s t z := by rw [mul_add,phaseRotate_add]
  period s z := by rw [mul_add,mul_one,phaseRotate_period]

 theorem phaseCircleAction_generator (z : PlanePhase ι) :
    phaseCircleAction.generator z=(2*Real.pi)•phaseJ z := by
  have hg : HasDerivAt (fun t : ℝ => 2*Real.pi*t) (2*Real.pi) 0 := by
    simpa only [mul_one,Function.id_def] using (hasDerivAt_id (0:ℝ)).const_mul (2*Real.pi)
  have hh := (phaseRotate_hasDerivAt (ι := ι) (2*Real.pi*0) z).scomp 0 hg
  have he : HasDerivAt (fun t : ℝ => phaseRotate (2*Real.pi*t) z)
      ((2*Real.pi)•phaseJ z) 0 := by
    convert! hh using 1; simp
  change manifoldMapDifferential (E := PlanePhase ι) (F := ℝ) (fun t : ℝ => phaseRotate (2*Real.pi*t) z) 0 1=_
  simp only [manifoldMapDifferential,mfderiv_eq_fderiv,he.hasFDerivAt.fderiv,
    ContinuousLinearMap.toSpanSingleton_apply,one_smul]

 theorem phaseSq_rotate (s : ℝ) (z : PlanePhase ι) : phaseSq (phaseRotate s z)=phaseSq z := by
  simp only [phaseRotate_apply,phaseSq,map_add,map_smul,add_apply,smul_apply,
    smul_eq_mul,phaseDot_J_left,phaseDot_J_right,phaseArea_J_left,neg_neg,phaseArea_self,neg_zero,mul_zero,
    add_zero,zero_add]
  linear_combination (phaseDot z z) * Real.sin_sq_add_cos_sq s

end PackingSufficiencySupport.Hamiltonian
end

end OAI
