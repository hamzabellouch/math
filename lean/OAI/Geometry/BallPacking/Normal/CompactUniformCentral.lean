import Mathlib
import OAI.Geometry.BallPacking.Hopf.DegreeHopfDeformation

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N]

 theorem exists_uniform_compact_exact_fibre_embedding_central_into {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) {K : Set M} (hK : IsCompact K)
    (hinv : ∀ x∈K,(manifoldExteriorOneForm (Γ 0) x).IsInvertible)
    {U : Set M} (hU : IsOpen U) (hKU : K⊆U)
    {δ : ℝ} (hδ : 0<δ) {A : ℝ × M → N}
    (hA : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,F) ∞ A)
    (hemb : ∀ t∈Ioc (0:ℝ) δ,Topology.IsEmbedding (fun x : U => A (t,x.val)))
    {T : Set N} (hT : IsOpen T) (hinto : MapsTo (fun x => A (0,x)) K T)
    (Ω : ℝ → ManifoldTwoForm F N)
    (hform : ∀ t∈Ioc (0:ℝ) δ,∀ x∈U,
      manifoldExteriorOneForm (Γ t) x=(Ω t (A (t,x))).bilinearComp
        (manifoldMapDifferential (E := F) (F := E) (fun y => A (t,y)) x)
        (manifoldMapDifferential (E := F) (F := E) (fun y => A (t,y)) x)) :
    ∃ η>0,η≤δ ∧ ∀ t∈Ioc (0:ℝ) η,∃ g : M → N,∃ W : Set M,IsOpen W ∧ K⊆W ∧
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ g ∧ Topology.IsEmbedding (fun x : W => g x.val) ∧
      MapsTo g W T ∧ ∀ x∈W,∀ v w,Ω t (g x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) g x v)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) g x w)=manifoldExteriorOneForm (Γ 0) x v w := by
  have hS : IsOpen (A ⁻¹' T) := hT.preimage hA.continuous
  have hKS : ({0}:Set ℝ)×ˢK⊆A ⁻¹' T := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    rcases ht with rfl
    exact hinto hx
  obtain ⟨V,W,hV,hW,h0V,hKW,hVW⟩ := generalized_tube_lemma isCompact_singleton hK hS hKS
  obtain ⟨η,hη,hηV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (mem_singleton 0))
  let δ' := min δ (η/2)
  have hδ' : 0<δ' := lt_min hδ (by positivity)
  have htδ {t : ℝ} (ht : t∈Ioc (0:ℝ) δ') : t∈Ioc (0:ℝ) δ :=
    ⟨ht.1,ht.2.trans (min_le_left _ _)⟩
  have htV {t : ℝ} (ht : t∈Ioc (0:ℝ) δ') : t∈V := by
    apply hηV
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht.1]
    have h := ht.2.trans (min_le_right δ (η/2))
    linarith
  obtain ⟨τ,hτ,hτδ,hτall⟩ :=
    exists_uniform_compact_exact_fibre_embedding_into hΓ hK hinv (hU.inter hW)
      (fun x hx => ⟨hKU hx,hKW hx⟩) hδ' hA
      (fun t ht => (hemb t (htδ ht)).comp (Topology.IsEmbedding.inclusion inter_subset_left))
      (fun t ht x hx => hVW ⟨htV ht,hx.2⟩) Ω
      (fun t ht x hx => hform t (htδ ht) x hx.1)
  exact ⟨τ,hτ,hτδ.trans (min_le_left _ _),hτall⟩

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial
open scoped Topology
open Set Function Manifold

 theorem cubicBubblePrimitive_coefficient_affine {A B : ℕ} (L S m p N : ℕ) (t δ c d ε : ℝ) :
     cubicBubblePrimitive (A := A) (B := B) L S m p N t δ c d ε=
       cubicBubblePrimitive (A := A) (B := B) L S m p N t δ c 0 ε+
         d•(cubicBubblePrimitive (A := A) (B := B) L S m p N t δ c 1 ε-cubicBubblePrimitive (A := A) (B := B) L S m p N t δ c 0 ε) := by
   simp only [cubicBubblePrimitive]
   module

 theorem cubicBubbleVariable_joint_smooth {A B : ℕ} (L S m p N : ℕ) (t δ c : ℝ)
     {D : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) :
     ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) =>
       cubicBubblePrimitive (A := A) (B := B) L S m p N t δ c (D a.1) a.1 a.2) := by
   have he : (fun a : ℝ×(Fin 3 → ℂ) => cubicBubblePrimitive (A := A) (B := B) L S m p N t δ c (D a.1) a.1 a.2)=
       (fun a : ℝ×(Fin 3 → ℂ) => cubicBubblePrimitive (A := A) (B := B) L S m p N t δ c 0 a.1 a.2+
         D a.1•(cubicBubblePrimitive (A := A) (B := B) L S m p N t δ c 1 a.1 a.2-cubicBubblePrimitive (A := A) (B := B) L S m p N t δ c 0 a.1 a.2)) := by
     funext a
     exact congrFun (cubicBubblePrimitive_coefficient_affine (A := A) (B := B) L S m p N t δ c (D a.1) a.1) a.2
   rw [he]
   exact (cubicBubblePrimitive_joint_smooth (A := A) (B := B) L S m p N t δ c 0).add
     ((hD.comp contDiff_fst).smul ((cubicBubblePrimitive_joint_smooth (A := A) (B := B) L S m p N t δ c 1).sub
       (cubicBubblePrimitive_joint_smooth (A := A) (B := B) L S m p N t δ c 0)))

 theorem cubicBubbleVariable_smooth_family {A B : ℕ} (L S m p N : ℕ) (t δ c : ℝ)
     {D : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) :
     SmoothOneFormFamily (fun ε => cubicBubblePrimitive (A := A) (B := B) L S m p N t δ c (D ε) ε) := by
   intro x
   simpa only [vector_chartOneForm] using (cubicBubbleVariable_joint_smooth (A := A) (B := B) L S m p N t δ c hD).contDiffOn

 theorem exists_uniform_cubic_bubble_transfer {L S A B p N : ℕ} (m : ℕ)
     (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hp : p<L-S) (hN : p<N)
     (hm : m+1≤p) (t δ : ℝ) {c : ℝ} (hc : 0<c)
     {D : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) (hD0 : 0<D 0)
     {K : Set (Fin 3 → ℂ)} (hK : IsCompact K)
     {T : Set (Fin 3 → ℂ)} (hT : IsOpen T) (h0T : (0 : Fin 3 → ℂ)∈T)
     {η : ℝ} (hη : 0<η) :
     ∃ τ>0,τ≤η ∧ ∀ ε∈Ioc (0:ℝ) τ,∃ g : (Fin 3 → ℂ) → (Fin 3 → ℂ),∃ W,
       IsOpen W ∧ K⊆W ∧ ContDiff ℝ ∞ g ∧ Topology.IsEmbedding (fun x : W => g x.val) ∧
       MapsTo g W T ∧ ∀ x∈W,∀ v w,
         degreeAffineForm (L:ℝ) (cubicBubblePolynomial (A := A) (B := B) L S (m+1) p N t δ ε) c (D ε)
           (g x) (fderiv ℝ g x v) (fderiv ℝ g x w)=
         D 0*affineFSForm ((m+1:ℕ)*c) (complexCartesian x) (complexCartesian v) (complexCartesian w) := by
   have hscale : ContDiff ℝ ∞ (fun a : ℝ×(Fin 3 → ℂ) => (a.1:ℂ)•a.2) :=
     (Complex.ofRealCLM.contDiff.comp contDiff_fst).smul contDiff_snd
   have hscaleM : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Fin 3 → ℂ)) 𝓘(ℝ,Fin 3 → ℂ) ∞
       (fun a : ℝ×(Fin 3 → ℂ) => (a.1:ℂ)•a.2) := by
     rw [←modelWithCornersSelf_prod,chartedSpaceSelf_prod]
     exact hscale.contMDiff
   have hemb (ε : ℝ) (hε : ε∈Ioc (0:ℝ) η) :
       Topology.IsEmbedding (fun x : (univ : Set (Fin 3 → ℂ)) => (ε:ℂ)•x.val) :=
     (Homeomorph.smulOfNeZero (α := Fin 3 → ℂ) (ε:ℂ) (Complex.ofReal_ne_zero.mpr hε.1.ne')).isEmbedding.comp
       Topology.IsEmbedding.subtypeVal
   let Γ := fun ε : ℝ => cubicBubblePrimitive (A := A) (B := B) L S (m+1) p N t δ c (D ε) ε
   let Ω := fun ε : ℝ => degreeAffineForm (L:ℝ) (cubicBubblePolynomial (A := A) (B := B) L S (m+1) p N t δ ε) c (D ε)
   have hform (ε : ℝ) (hε : ε∈Ioc (0:ℝ) η) (x : Fin 3 → ℂ) (_hx : x∈(univ : Set (Fin 3 → ℂ))) :
       manifoldExteriorOneForm (Γ ε) x=(Ω ε ((ε:ℂ)•x)).bilinearComp
         (manifoldMapDifferential (fun y : Fin 3 → ℂ => (ε:ℂ)•y) x)
         (manifoldMapDifferential (fun y : Fin 3 → ℂ => (ε:ℂ)•y) x) := by
     ext v w
     simp only [ContinuousLinearMap.bilinearComp_apply,manifoldMapDifferential,mfderiv_eq_fderiv]
     exact cubicBubblePrimitive_curvature hAS hS hB hp.le hm hN.le t δ c (D ε) hε.1.ne' x v w
   obtain ⟨τ,hτ,hτη,hall⟩ := exists_uniform_compact_exact_fibre_embedding_central_into
     (cubicBubbleVariable_smooth_family (A := A) (B := B) L S (m+1) p N t δ c hD) hK
     (fun x _ => cubicBubblePrimitive_zero_invertible m hAS hS hB hp hN t δ hc hD0 x)
     isOpen_univ (subset_univ K) hη hscaleM hemb hT
     (by intro x _; simpa only [Complex.ofReal_zero,zero_smul] using h0T) Ω hform
   refine ⟨τ,hτ,hτη,?_⟩
   intro ε hε
   obtain ⟨g,W,hW,hKW,hg,he,hgT,hgf⟩ := hall ε hε
   refine ⟨g,W,hW,hKW,hg.contDiff,he,hgT,?_⟩
   intro x hx v w
   have hh := hgf x hx v w
   simp only [mfderiv_eq_fderiv,cubicBubblePrimitive_zero_exterior m hAS hS hB hp hN] at hh
   convert! hh using 1

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function
open scoped Manifold Topology
open Manifold
section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

 def degreeHopfDifference (q : ℝ) (F : PlanePhase ι → PlanePhase κ) (c : ℝ) :=
  primitivePullback (hopfPrimitive c) F-q•hopfPrimitive c

 def radialDegreeConePrimitive (q : ℝ) (F : PlanePhase ι → PlanePhase κ) (c : ℝ)
    (d : ℝ → ℝ) (z : PlanePhase ι) := degreeConePrimitive q F c (d (phaseSq z)) z

 theorem degreeConePrimitive_split (q : ℝ) (F : PlanePhase ι → PlanePhase κ)
    (c d : ℝ) (z : PlanePhase ι) :
    degreeConePrimitive q F c d z=degreeConePrimitive q F c 0 z+
      d•(phaseSq z•degreeHopfDifference q F c z) := by
  ext v
  simp only [degreeConePrimitive,degreeHopfPrimitive,degreeHopfDifference,
    Pi.add_apply,Pi.smul_apply,Pi.sub_apply,add_apply,smul_apply,sub_apply,smul_eq_mul]
  ring

 theorem degreeHopfDifference_smoothAt {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0) (q c : ℝ) :
    ContDiffAt ℝ ∞ (degreeHopfDifference q F c) z :=
  (primitivePullback_smoothAt (hopfPrimitive_smoothAt c hFz) hF).sub
    ((hopfPrimitive_smoothAt c hz).const_smul q)

 theorem degreeHopfDifference_circle {F : PlanePhase ι → PlanePhase κ} {z : PlanePhase ι}
    {q : ℝ} (hz : z≠0) (hFz : F z≠0)
    (hD : fderiv ℝ F z (phaseJ z)=q•phaseJ (F z)) (c : ℝ) :
    degreeHopfDifference q F c z (phaseJ z)=0 := by
  simp only [degreeHopfDifference,Pi.sub_apply,Pi.smul_apply,sub_apply,smul_apply,
    smul_eq_mul,primitivePullback,ContinuousLinearMap.comp_apply,hD,map_smul,
    hopfPrimitive_circle c hz,hopfPrimitive_circle c hFz]
  ring

 theorem radialDegreeConePrimitive_smoothAt {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} {d : ℝ → ℝ} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0)
    (hd : ContDiffAt ℝ ∞ d (phaseSq z)) (q c : ℝ) :
    ContDiffAt ℝ ∞ (radialDegreeConePrimitive q F c d) z := by
  have he : radialDegreeConePrimitive q F c d=fun y => degreeConePrimitive q F c 0 y+
      d (phaseSq y)•(phaseSq y•degreeHopfDifference q F c y) :=
    funext fun y => degreeConePrimitive_split q F c (d (phaseSq y)) y
  rw [he]
  exact (degreeConePrimitive_smoothAt hF hz hFz q c 0).add
    ((hd.comp z phaseSq_smooth.contDiffAt).smul
      (phaseSq_smooth.contDiffAt.smul (degreeHopfDifference_smoothAt hF hz hFz q c)))

 theorem radialDegreeConePrimitive_exterior {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} {d : ℝ → ℝ} (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0)
    (hd : DifferentiableAt ℝ d (phaseSq z)) (q c : ℝ) :
    euclideanExteriorOneForm (radialDegreeConePrimitive q F c d) z=
      radialSymplectization z
        (degreeHopfPrimitive q F c (d (phaseSq z)) z+
          (phaseSq z*deriv d (phaseSq z))•degreeHopfDifference q F c z)
        (degreeHopfForm q F c (d (phaseSq z)) z) := by
  let ξ : PlanePhase ι → PlanePhase ι →L[ℝ] ℝ := fun y => phaseSq y•degreeHopfDifference q F c y
  have hξ : DifferentiableAt ℝ ξ z :=
    (phaseSq_smooth.contDiffAt.smul (degreeHopfDifference_smoothAt hF hz hFz q c)).differentiableAt (by simp)
  have h₀ := (degreeConePrimitive_smoothAt hF hz hFz q c 0).differentiableAt (by simp)
  have hds := hd.hasDerivAt.comp_hasFDerivAt z (phaseSq_hasFDerivAt z)
  have hr := h₀.hasFDerivAt.add (hds.smul hξ.hasFDerivAt)
  have hs := h₀.hasFDerivAt.add (hξ.hasFDerivAt.const_smul (d (phaseSq z)))
  have her : (fun y => degreeConePrimitive q F c 0 y+d (phaseSq y)•ξ y)=
      radialDegreeConePrimitive q F c d :=
    funext fun y => (degreeConePrimitive_split q F c (d (phaseSq y)) y).symm
  have hes : (fun y => degreeConePrimitive q F c 0 y+d (phaseSq z)•ξ y)=
      degreeConePrimitive q F c (d (phaseSq z)) :=
    funext fun y => (degreeConePrimitive_split q F c (d (phaseSq z)) y).symm
  change HasFDerivAt (fun y => degreeConePrimitive q F c 0 y+d (phaseSq y)•ξ y) _ z at hr
  change HasFDerivAt (fun y => degreeConePrimitive q F c 0 y+d (phaseSq z)•ξ y) _ z at hs
  rw [her] at hr
  rw [hes] at hs
  have he := degreeConePrimitive_exterior hF hz hFz q c (d (phaseSq z))
  ext v w
  have hh := congrArg (fun L : PlanePhase ι →L[ℝ] PlanePhase ι →L[ℝ] ℝ => L v w) he
  rw [euclideanExteriorOneForm,hs.fderiv] at hh
  rw [euclideanExteriorOneForm,hr.fderiv]
  simp only [sub_apply,ContinuousLinearMap.flip_apply,add_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul,radialSymplectization_apply,
    Function.comp_apply,ξ] at hh ⊢
  nlinarith only [hh]

 theorem radialDegreeConePrimitive_nondegenerate {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} {d : ℝ → ℝ} {q : ℝ}
    (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0)
    (hD : fderiv ℝ F z z=q•F z)
    (hJ : ∀ v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v))
    (hd : DifferentiableAt ℝ d (phaseSq z)) {c : ℝ} (hc : 0<c)
    (hd0 : 0≤d (phaseSq z)) (hdq : q*d (phaseSq z)<1) :
    (euclideanExteriorOneForm (radialDegreeConePrimitive q F c d) z).IsInvertible := by
  have hDJ : fderiv ℝ F z (phaseJ z)=q•phaseJ (F z) := by rw [hJ,hD,map_smul]
  rw [radialDegreeConePrimitive_exterior hF hz hFz hd]
  apply radialSymplectization_nondegenerate hz _ _ (half_pos hc)
  · simp only [add_apply,smul_apply,smul_eq_mul,degreeHopfPrimitive_circle hz hFz hDJ,
      degreeHopfDifference_circle hz hFz hDJ,mul_zero,add_zero]
  · intro v
    rw [degreeHopfForm_skew,degreeHopfForm_radial hF hz hFz hD,neg_zero]
  · intro v
    rw [degreeHopfForm_skew,degreeHopfForm_circle hF hz hFz hDJ,neg_zero]
  · exact degreeHopfForm_circle hF hz hFz hDJ c _
  · intro v hdv hav hv
    exact degreeHopfForm_horizontal_positive hF hz hFz hJ hc hd0 hdq hdv hav hv

 theorem radialDegreeConePrimitive_circle_contraction {F : PlanePhase ι → PlanePhase κ}
    {z : PlanePhase ι} {d : ℝ → ℝ} {q : ℝ}
    (hF : ContDiffAt ℝ ∞ F z) (hz : z≠0) (hFz : F z≠0)
    (hDJ : fderiv ℝ F z (phaseJ z)=q•phaseJ (F z))
    (hd : DifferentiableAt ℝ d (phaseSq z)) (c : ℝ) (v : PlanePhase ι) :
    euclideanExteriorOneForm (radialDegreeConePrimitive q F c d) z v (phaseJ z)=c*phaseDot z v := by
  rw [radialDegreeConePrimitive_exterior hF hz hFz hd]
  have hα : (degreeHopfPrimitive q F c (d (phaseSq z)) z+
      (phaseSq z*deriv d (phaseSq z))•degreeHopfDifference q F c z) (phaseJ z)=c/2 := by
    simp only [add_apply,smul_apply,smul_eq_mul,degreeHopfPrimitive_circle hz hFz hDJ,
      degreeHopfDifference_circle hz hFz hDJ,mul_zero,add_zero]
  rw [radialSymplectization_circle z _ _ hα
    (fun v => by rw [degreeHopfForm_skew,degreeHopfForm_circle hF hz hFz hDJ,neg_zero])]
  ring

end
section

variable {ι : Type*} [Fintype ι]

theorem radial_moser_field_tangent
    {Ω : ℝ → ManifoldTwoForm (PlanePhase ι) (PlanePhase ι)}
    {α : ℝ → ManifoldOneForm (PlanePhase ι) (PlanePhase ι)}
    {p : ℝ × PlanePhase ι} (hinv : (Ω p.1 p.2).IsInvertible)
    {c : ℝ} (hc : c≠0)
    (hC : ∀ v,Ω p.1 p.2 v (phaseJ p.2)=c*phaseDot p.2 v)
    (hβ : α p.1 p.2 (phaseJ p.2)=0) :
    phaseDot p.2 (manifoldMoserField Ω α p)=0 := by
  have he : Ω p.1 p.2 (manifoldMoserField Ω α p) = -α p.1 p.2 := by
    simp only [manifoldMoserField,map_neg,hinv.self_apply_inverse]
  have he' := congrArg (fun L : PlanePhase ι →L[ℝ] ℝ => L (phaseJ p.2)) he
  let v : PlanePhase ι := manifoldMoserField Ω α p
  change Ω p.1 p.2 v (phaseJ p.2)= -(α p.1 p.2 (phaseJ p.2)) at he'
  rw [hC,hβ,neg_zero] at he'
  exact (mul_eq_zero.mp he').resolve_left hc

theorem phaseSq_nonautonomous_flow_constant {Φ : ℝ × PlanePhase ι → PlanePhase ι}
    {V : ℝ × PlanePhase ι → PlanePhase ι} (hΦ0 : ∀ x,Φ (0,x)=x)
    (hODE : ∀ x t,t∈Ioo (-2:ℝ) 2 → HasDerivAt (fun s => Φ (s,x)) (V (t,Φ (t,x))) t)
    (hVrad : ∀ p,phaseDot p.2 (V p)=0) {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (x : PlanePhase ι) : phaseSq (Φ (t,x))=phaseSq x := by
  have hd (s : ℝ) (hs : s∈Icc (0:ℝ) 1) : HasDerivAt (fun r => phaseSq (Φ (r,x))) 0 s := by
    have hh := (phaseSq_hasFDerivAt (Φ (s,x))).comp_hasDerivAt s
      (hODE x s (by constructor <;> linarith [hs.1,hs.2]))
    simpa only [Function.comp_def,smul_apply,smul_eq_mul,hVrad (s,Φ (s,x)),mul_zero] using hh
  have he := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hd s hs).hasDerivWithinAt)
    (fun _ _ => (by simp : ‖(0:ℝ)‖≤(0:ℝ))) (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num) ht
  simpa only [zero_mul,norm_le_zero_iff,sub_eq_zero,hΦ0] using he

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exact_path_transport_on_unit_interval
    {Γ : ℝ → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {Φ : ℝ × M → M}
    (hΦ : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ)
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M)))
    (hΦ0 : ∀ x,Φ (0,x)=x)
    (hODE : ∀ x s,s∈Ioo (-2:ℝ) 2 → HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E)
      (fun r => Φ (r,x)) s ((1:ℝ →L[ℝ] ℝ).smulRight (V (s,Φ (s,x)))))
    {O : Set (ℝ × M)} (hO : IsOpen O)
    (hinv : ∀ p∈O,(manifoldExteriorOneForm (Γ p.1) p.2).IsInvertible)
    (heq : ∀ p∈O,V p=manifoldMoserField
      (fun s => manifoldExteriorOneForm (Γ s)) (manifoldTimePrimitive Γ) p)
    {x : M} (hstay : ∀ s∈Icc (0:ℝ) 1,(s,Φ (s,x))∈O)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (v w : E) :
      manifoldPullback Φ (fun s => manifoldExteriorOneForm (Γ s)) t x v w=
        manifoldExteriorOneForm (Γ 0) x v w := by
  let Ω : ℝ → ManifoldTwoForm E M := fun s => manifoldExteriorOneForm (Γ s)
  have hd (s : ℝ) (hs : s∈Icc (0:ℝ) 1) :
      HasDerivAt (fun r => manifoldPullback Φ Ω r x v w) 0 s :=
    exact_path_local_transport_derivative (Γ := Γ) hΓ hΦ hV hODE hO hinv heq
      (by constructor <;> linarith [hs.1,hs.2]) (hstay s hs) v w
  have he := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hd s hs).hasDerivWithinAt)
    (fun _ _ => (by simp : ‖(0:ℝ)‖≤(0:ℝ))) (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num) ht
  have he' : manifoldPullback Φ Ω t x v w=manifoldPullback Φ Ω 0 x v w := by
    simpa only [zero_mul,norm_le_zero_iff,sub_eq_zero] using he
  rw [he']
  have hid : (fun y => Φ (0,y))=id := funext hΦ0
  have hD : preferredDifferential (fun y => Φ (0,y)) x=ContinuousLinearMap.id ℝ E := by
    change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun y => Φ (0,y)) x=_
    rw [hid]; exact mfderiv_id
  rw [manifoldPullback,hD]
  simp only [hΦ0,ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.id_apply,Ω]

end

variable {ι : Type*} [Fintype ι]

 theorem exists_compact_radial_exact_moser
    {Γ : ℝ → ManifoldOneForm (PlanePhase ι) (PlanePhase ι)}
    (hΓ : SmoothOneFormFamily Γ) {K O : Set (PlanePhase ι)}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K⊆O)
    (hKr : ∀ x∈K,∀ y,phaseSq y=phaseSq x → y∈K)
    {c : ℝ} (hc : c≠0)
    (hcircle : ∀ s,∀ z∈O,∀ v,
      manifoldExteriorOneForm (Γ s) z v (phaseJ z)=c*phaseDot z v)
    (hβcircle : ∀ s,∀ z∈O,manifoldTimePrimitive Γ s z (phaseJ z)=0)
    (hinv : ∀ s∈Icc (0:ℝ) 1,∀ z∈K,(manifoldExteriorOneForm (Γ s) z).IsInvertible) :
    ∃ Φ Ψ : ℝ × PlanePhase ι → PlanePhase ι,
      ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Ψ ∧
      (∀ x,Φ (0,x)=x) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x,Ψ (t,Φ (t,x))=x ∧ Φ (t,Ψ (t,x))=x) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x,phaseSq (Φ (t,x))=phaseSq x) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x∈K,∀ v w,
        manifoldPullback Φ (fun s => manifoldExteriorOneForm (Γ s)) t x v w=
          manifoldExteriorOneForm (Γ 0) x v w) ∧
      ∃ V : ℝ × PlanePhase ι → PlanePhase ι,
        ContDiff ℝ ∞ V ∧
        (∀ x t,t∈Ioo (-2:ℝ) 2 → HasDerivAt (fun s => Φ (s,x)) (V (t,Φ (t,x))) t) ∧
        ∀ s∈Icc (0:ℝ) 1,∀ x∈K,
          V (s,x)=manifoldMoserField (fun t => manifoldExteriorOneForm (Γ t)) (manifoldTimePrimitive Γ) (s,x) := by
  let Ω : ℝ → ManifoldTwoForm (PlanePhase ι) (PlanePhase ι) := fun t => manifoldExteriorOneForm (Γ t)
  let α : ℝ → ManifoldOneForm (PlanePhase ι) (PlanePhase ι) := manifoldTimePrimitive Γ
  have hΩ : SmoothTwoFormFamily Ω := manifoldExteriorOneForm_path_smooth hΓ
  have hα : SmoothOneFormFamily α := manifoldTimePrimitive_smooth hΓ
  let U : Set (ℝ × PlanePhase ι) := (univ×ˢO) ∩ {p | (Ω p.1 p.2).IsInvertible}
  have hU : IsOpen U := (isOpen_univ.prod hO).inter (manifoldTwoForm_isOpen_nondegenerate hΩ)
  have hKU : Icc (0:ℝ) 1×ˢK⊆U := fun p hp => ⟨⟨mem_univ _,hKO hp.2⟩,hinv _ hp.1 _ hp.2⟩
  obtain ⟨V,hV,hVe,_hVz,⟨C,hC,hVC⟩,hVL⟩ :=
    exists_joint_localized_manifold_moser_field (Ω := Ω) (α := α) hΩ hα (isCompact_Icc.prod hK) hU hKU (fun _ hp => hp.2)
  obtain ⟨A,hA,hKA,hAV⟩ := mem_nhdsSet_iff_exists.mp hVe
  have hVrad (p : ℝ × PlanePhase ι) : phaseDot p.2 (V p)=0 := by
    apply hVL p (phaseDot p.2)
    intro hp
    exact radial_moser_field_tangent (Ω := Ω) (α := α) hp.2 hc
      (hcircle _ _ hp.1.2) (hβcircle _ _ hp.1.2)
  obtain ⟨Φ,Ψ,hΦ,hΨ,hΦ0,hΦi,hODE,_hfix⟩ :=
    exists_spatially_compact_nonautonomous_flow hV hC hVC
  have hODE' (x : PlanePhase ι) (t : ℝ) (ht : t∈Ioo (-2:ℝ) 2) :
      HasDerivAt (fun s => Φ (s,x)) (V (t,Φ (t,x))) t := by
    have hd : HasFDerivAt (fun s => Φ (s,x))
        ((1 : ℝ →L[ℝ] ℝ).smulRight (show PlanePhase ι from V (t,Φ (t,x)))) t :=
      hasMFDerivAt_iff_hasFDerivAt.mp (hODE x t ht)
    exact hasDerivAt_iff_hasFDerivAt.mpr hd
  have hrad (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (x : PlanePhase ι) :
      phaseSq (Φ (t,x))=phaseSq x := by
    exact phaseSq_nonautonomous_flow_constant hΦ0 hODE' hVrad ht x
  have hstay (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (x : PlanePhase ι) (hx : x∈K) :
      (t,Φ (t,x))∈A∩U := by
    have hk : (t,Φ (t,x))∈Icc (0:ℝ) 1×ˢK := ⟨ht,hKr x hx _ (hrad t ht x)⟩
    exact ⟨hKA hk,hKU hk⟩
  have hform (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (x : PlanePhase ι) (hx : x∈K) (v w : PlanePhase ι) :
      manifoldPullback Φ Ω t x v w=Ω 0 x v w := by
    exact exact_path_transport_on_unit_interval (Γ := Γ) hΓ hΦ hV hΦ0 hODE (hA.inter hU)
      (fun _ hp => hp.2.2) (fun _ hp => hAV hp.1) (fun s hs => hstay s hs x hx) ht v w
  have hΦs : ContDiff ℝ ∞ Φ := by
    rw [← modelWithCornersSelf_prod,chartedSpaceSelf_prod] at hΦ
    exact contMDiff_iff_contDiff.mp hΦ
  have hΨs : ContDiff ℝ ∞ Ψ := by
    rw [← modelWithCornersSelf_prod,chartedSpaceSelf_prod] at hΨ
    exact contMDiff_iff_contDiff.mp hΨ
  have hVs : ContDiff ℝ ∞ V := by
    have hs := (contMDiff_snd_tangentBundle_modelSpace (PlanePhase ι) 𝓘(ℝ,PlanePhase ι)).comp hV
    rw [← modelWithCornersSelf_prod,chartedSpaceSelf_prod] at hs
    exact contMDiff_iff_contDiff.mp hs
  exact ⟨Φ,Ψ,hΦs,hΨs,hΦ0,hΦi,hrad,hform,V,hVs,hODE',fun s hs x hx => hAV (hKA ⟨hs,hx⟩)⟩

end PackingSufficiencySupport.Hamiltonian
end

end OAI
