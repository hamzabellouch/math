import OAI.MathematicalPhysics.Elasticity.TransportAlgebra
import OAI.MathematicalPhysics.Elasticity.Homotopy
import OAI.MathematicalPhysics.Elasticity.Extension

namespace OAI

noncomputable section

namespace ElasticityPlanar
open Set Complex Module
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

section
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R] [FiniteDimensional ℂ R]
variable {n : Type*} [Fintype n]

/-- A smooth frame for the actual constant complex characteristic direction
in ambient space. Transverse coordinates are obtained by a proved continuous
left inverse, not assumed to exist. Arbitrary smooth coefficients are allowed. -/
theorem spatial_frame_of_left_inverse (J : ℂ →L[ℝ] E) (K : E →L[ℝ] ℂ)
    (hK : Function.LeftInverse K J)
    {S Ω Ω' : Set ℂ} (hS : IsCompact S) (hΩS : Ω ⊆ S)
    (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω) (q : Basis n ℂ R)
    (A : E → R) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Ω) (h1 : Set.EqOn g 1 Ω') :
    ∃ V : E → R, ContDiff ℝ (⊤ : ℕ∞) V ∧ (∀ x, IsUnit (V x)) ∧
        ∀ x, K x∈Ω' → fderiv ℝ V x (J 1)+I • fderiv ℝ V x (J I)=A x*V x := by
  let P : E →L[ℝ] E := ContinuousLinearMap.id ℝ E-J.comp K
  have hPJ (z : ℂ) : P (J z)=0 := by
    change J z-J (K (J z))=0
    rw [hK z,sub_self]
  have hrec (x : E) : P x+J (K x)=x := sub_add_cancel x (J (K x))
  let B : E × ℂ → R := fun w => g w.2 • A (w.1+J w.2)
  have hB : ContDiff ℝ (⊤ : ℕ∞) B :=
    (hg.comp contDiff_snd).smul (hA.comp (contDiff_fst.add (J.contDiff.comp contDiff_snd)))
  have hBc (p : E) (z : ℂ) (hz : z∉tsupport g) : B (p,z)=0 := by
    simp only [B,image_eq_zero_of_notMem_tsupport hz,zero_smul]
  obtain ⟨W,hW,hunit,he⟩ := exists_variable_planar_frame hS hΩS hΩ' hsub hc q B hB hBc hg hc hs h1
  let L := P.prod K
  let V : E → R := W ∘ L
  have hV : ContDiff ℝ (⊤ : ℕ∞) V := hW.comp L.contDiff
  refine ⟨V,hV,fun x => hunit (L x),fun x hx => ?_⟩
  have hd (v : ℂ) : fderiv ℝ V x (J v)=fderiv ℝ (fun z => W (P x,z)) (K x) v := by
    have hw := ((hW.differentiable (by simp)) (L x)).hasFDerivAt.comp x L.hasFDerivAt
    have ht : HasFDerivAt (fun z : ℂ => (P x,z)) (ContinuousLinearMap.inr ℝ E ℂ) (K x) := by
      simpa only [ContinuousLinearMap.inr,id] using
        (hasFDerivAt_const (P x) (K x)).prodMk (hasFDerivAt_id (K x))
    have hw' := ((hW.differentiable (by simp)) (L x)).hasFDerivAt.comp (K x) ht
    change HasFDerivAt V _ x at hw
    change HasFDerivAt (fun z => W (P x,z)) _ (K x) at hw'
    rw [hw.fderiv,hw'.fderiv]
    change fderiv ℝ W (L x) (P (J v),K (J v))=fderiv ℝ W (L x) (0,v)
    rw [hPJ v,hK v]
  rw [hd 1,hd I]
  have hh := he (P x) (K x) hx
  change classicalDbar (fun z => W (P x,z)) (K x)=_
  rw [hh]
  change (g (K x) • A (P x+J (K x)))*W (P x,K x)=A x*W (P x,K x)
  rw [h1 hx,hrec]
  simp only [Pi.one_apply,one_smul]
/-- Actual frames on every compact physical region, with no coordinate,
cutoff, or planar-solvability existence hypothesis. -/
theorem exists_spatial_frame (J : ℂ →L[ℝ] E) (hJ : Function.Injective J)
    (q : Basis n ℂ R) (A : E → R) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    {C : Set E} (hC : IsCompact C) :
    ∃ V : E → R, ContDiff ℝ (⊤ : ℕ∞) V ∧ (∀ x, IsUnit (V x)) ∧
      ∀ x∈C, fderiv ℝ V x (J 1)+I • fderiv ℝ V x (J I)=A x*V x := by
  obtain ⟨K,hK⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hJ
  obtain ⟨r,hr⟩ := (hC.image K.continuous).isBounded.subset_ball (0 : ℂ)
  have hbb : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball 0 (r+1) := by
    intro z hz
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith)
  obtain ⟨g,hg,hc,hs,h1,_⟩ := ElasticityBoundary.compact_smooth_cutoff
    (isCompact_closedBall (0 : ℂ) r) Metric.isOpen_ball hbb
  let g' : ℂ → ℂ := fun z => (g z : ℂ)
  have hg' : ContDiff ℝ (⊤ : ℕ∞) g' := Complex.ofRealCLM.contDiff.comp hg
  have hsupport : tsupport g'⊆tsupport g := by
    apply closure_mono
    intro z hz
    exact fun hh => hz (by simp only [g',hh,Complex.ofReal_zero])
  have hc' : HasCompactSupport g' := hc.of_isClosed_subset (isClosed_tsupport _) hsupport
  have h1' : Set.EqOn g' 1 (Metric.ball (0 : ℂ) r) := by
    intro z hz
    have hh := h1.self_of_nhdsSet z (Metric.ball_subset_closedBall hz)
    simp only [g',hh,Complex.ofReal_one,Pi.one_apply]
  obtain ⟨V,hV,hu,he⟩ := spatial_frame_of_left_inverse J K hK
    (isCompact_closedBall (0 : ℂ) (r+1)) Metric.ball_subset_closedBall Metric.isOpen_ball
    (Metric.ball_subset_ball (by linarith : r≤r+1)) q A hA hg' hc' (hsupport.trans hs) h1'
  exact ⟨V,hV,hu,fun x hx => he x (hr (Set.mem_image_of_mem K hx))⟩
end
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- Genuine invertible transport frames on any finite dimensional complex
fiber, with arbitrary smooth coefficients. Applies to the rank-three physical
null hyperplane plus scalar fiber, without assuming a frame exists. -/
theorem exists_spatial_linear_frame (J : ℂ →L[ℝ] E) (hJ : Function.Injective J)
    (A : E → F →L[ℂ] F) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    {C : Set E} (hC : IsCompact C) :
    ∃ V : E → F →L[ℂ] F, ContDiff ℝ (⊤ : ℕ∞) V ∧
      (∀ x, IsUnit (V x)) ∧
      ∀ x∈C, fderiv ℝ V x (J 1)+I • fderiv ℝ V x (J I)=A x*V x := by
  let : CompleteSpace F := FiniteDimensional.complete ℂ F
  exact exists_spatial_frame J hJ (Module.finBasis ℂ (F →L[ℂ] F)) A hA hC

end ElasticityPlanar
namespace ElasticityPlanar
open MeasureTheory Set Topology
open scoped BigOperators ComplexConjugate
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : Type*} [Fintype n]

def planeMap (J : ℂ →L[ℝ] E) (x : E) (z : ℂ) : E := x+J z
lemma planeMap_smooth (J : ℂ →L[ℝ] E) (x : E) :
    ContDiff ℝ (⊤ : ℕ∞) (planeMap J x) := contDiff_const.add J.contDiff
lemma planeMap_closedEmbedding (J : ℂ →L[ℝ] E) (hJ : Function.Injective J) (x : E) :
    IsClosedEmbedding (planeMap J x) := by
  exact (Homeomorph.addLeft x).isClosedEmbedding.comp
    (LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hJ))
lemma plane_compact (J : ℂ →L[ℝ] E) (hJ : Function.Injective J) (x : E)
    {f : E → ℂ} (hf : HasCompactSupport f) : HasCompactSupport (f ∘ planeMap J x) := by
  apply HasCompactSupport.intro ((planeMap_closedEmbedding J hJ x).isCompact_preimage hf)
  intro z hz
  exact image_eq_zero_of_notMem_tsupport (f := f) (x := planeMap J x z) hz
lemma plane_deriv (J : ℂ →L[ℝ] E) (x : E) {f : E → ℂ}
    (hf : Differentiable ℝ f) (z v : ℂ) :
    fderiv ℝ (f ∘ planeMap J x) z v=fderiv ℝ f (planeMap J x z) (J v) := by
  have hp : HasFDerivAt (planeMap J x) J z := by
    change HasFDerivAt (fun t : ℂ => x+J t) J z
    simpa only [Pi.add_def,zero_add] using (hasFDerivAt_const x z).add J.hasFDerivAt
  exact congrArg (fun T : ℂ →L[ℝ] ℂ => T v) ((hf _).hasFDerivAt.comp z hp).fderiv

/-- Compact kernel uniqueness in ambient physical space, by restriction to
all affine characteristic planes. The plane embedding is actual and injective. -/
theorem spatial_compact_kernel (J : ℂ →L[ℝ] E) (hJ : Function.Injective J)
    (a : n → n → E → ℂ) (ha : ∀ i j, Continuous (a i j))
    (u : n → E → ℂ) (hu : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (u i))
    (hc : ∀ i, HasCompactSupport (u i))
    (he : ∀ i x, fderiv ℝ (u i) x (J 1)+Complex.I*fderiv ℝ (u i) x (J Complex.I)=
      ∑ j, a i j x*u j x) : ∀ i x, u i x=0 := by
  intro i x
  let v : n → Test := fun i => ⟨u i ∘ planeMap J x,
    (hu i).comp (planeMap_smooth J x),plane_compact J hJ x (hc i)⟩
  have hv := compact_kernel (fun i j => a i j ∘ planeMap J x)
    (fun i j => (ha i j).comp (planeMap_smooth J x).continuous) v (fun j z => ?_)
  · have hh := congrArg (fun f : Test => f 0) (hv i)
    change u i (x+J 0)=0 at hh
    simpa only [map_zero,add_zero] using hh
  · change fderiv ℝ (u j ∘ planeMap J x) z 1+
      Complex.I*fderiv ℝ (u j ∘ planeMap J x) z Complex.I=_
    rw [plane_deriv J x ((hu j).differentiable (by simp)),
      plane_deriv J x ((hu j).differentiable (by simp))]
    exact he j (planeMap J x z)
end ElasticityPlanar
namespace ElasticityParameter
open scoped BigOperators
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
def smoothAlgebra : Subalgebra ℂ (E → ℂ) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f}
  add_mem' := by
    intro f g hf hg
    change ContDiff ℝ (⊤ : ℕ∞) f at hf
    change ContDiff ℝ (⊤ : ℕ∞) g at hg
    exact hf.add hg
  mul_mem' := by
    intro f g hf hg
    change ContDiff ℝ (⊤ : ℕ∞) f at hf
    change ContDiff ℝ (⊤ : ℕ∞) g at hg
    exact hf.mul hg
  zero_mem' := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun _ : E => (0 : ℂ))
    exact contDiff_const
  one_mem' := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun _ : E => (1 : ℂ))
    exact contDiff_const
  algebraMap_mem' c := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun _ : E => c)
    exact contDiff_const
abbrev Smooth := smoothAlgebra E
variable {E}
lemma smooth (f : Smooth E) : ContDiff ℝ (⊤ : ℕ∞) (f : E → ℂ) := f.property

def delta (v : E) : Derivation ℂ (Smooth E) (Smooth E) := Derivation.mk'
  { toFun := fun f => ⟨fun x => fderiv ℝ (f : E → ℂ) x v,
      ((smooth f).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const⟩
    map_add' f g := by
      apply Subtype.ext
      funext x
      exact congrArg (fun T : E →L[ℝ] ℂ => T v)
        (fderiv_add ((smooth f).differentiable (by simp) x) ((smooth g).differentiable (by simp) x))
    map_smul' c f := by
      apply Subtype.ext
      funext x
      exact congrArg (fun T : E →L[ℝ] ℂ => T v)
        (fderiv_const_smul ((smooth f).differentiable (by simp) x) c) }
  (by
    intro f g
    apply Subtype.ext
    funext x
    exact congrArg (fun T : E →L[ℝ] ℂ => T v)
      (fderiv_mul ((smooth f).differentiable (by simp) x) ((smooth g).differentiable (by simp) x)))
lemma delta_apply (v : E) (f : Smooth E) (x : E) :
    (delta v f : E → ℂ) x=fderiv ℝ (f : E → ℂ) x v := rfl
lemma delta_delta (v w : E) (f : Smooth E) (x : E) :
    (delta v (delta w f) : E → ℂ) x=fderiv ℝ (fderiv ℝ (f : E → ℂ)) x v w := by
  have hd : Differentiable ℝ (fderiv ℝ (f : E → ℂ)) :=
    ((smooth f).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  change fderiv ℝ (fun y => fderiv ℝ (f : E → ℂ) y w) x v=_
  rw [fderiv_clm_apply (hd x) (differentiableAt_const w)]
  simp
lemma delta_commute (v w : E) (f : Smooth E) : delta v (delta w f)=delta w (delta v f) := by
  apply Subtype.ext
  funext x
  rw [delta_delta,delta_delta]
  exact (smooth f).contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞)≤⊤)) _ _

/-- Parameter antiholomorphic derivative in fixed physical coordinates, without
changing the physical point or differentiating any moving plane coordinates. -/
def pbar : Derivation ℂ (Smooth (E × ℂ)) (Smooth (E × ℂ)) :=
  delta ((0 : E),(1 : ℂ))+Complex.I • delta ((0 : E),Complex.I)
lemma pbar_delta (v : E) (f : Smooth (E × ℂ)) :
    pbar (delta (v,0) f)=delta (v,0) (pbar f) := by
  simp only [pbar,Derivation.add_apply,Derivation.smul_apply,map_add,Derivation.map_smul]
  rw [delta_commute,delta_commute (0,Complex.I)]
lemma slice_deriv (f : Smooth (E × ℂ)) (x : E) (z v : ℂ) :
    fderiv ℝ (fun w => (f : E × ℂ → ℂ) (x,w)) z v=
      fderiv ℝ (f : E × ℂ → ℂ) (x,z) (0,v) := by
  have he : HasFDerivAt (fun w : ℂ => (x,w)) (ContinuousLinearMap.inr ℝ E ℂ) z := by
    simpa only [ContinuousLinearMap.inr,id] using (hasFDerivAt_const x z).prodMk (hasFDerivAt_id z)
  exact congrArg (fun L : ℂ →L[ℝ] ℂ => L v)
    (((smooth f).differentiable (by simp) (x,z)).hasFDerivAt.comp z he).fderiv
lemma pbar_apply (f : Smooth (E × ℂ)) (x : E) (z : ℂ) :
    (pbar f : E × ℂ → ℂ) (x,z)=
      fderiv ℝ (fun w => (f : E × ℂ → ℂ) (x,w)) z 1+
      Complex.I*fderiv ℝ (fun w => (f : E × ℂ → ℂ) (x,w)) z Complex.I := by
  rw [slice_deriv,slice_deriv]
  rfl
lemma pbar_zero_of_holomorphic (f : Smooth (E × ℂ))
    (hf : ∀ x, Differentiable ℂ (fun z => (f : E × ℂ → ℂ) (x,z))) : pbar f=0 := by
  apply Subtype.ext
  funext q
  obtain ⟨x,z⟩ := q
  rw [pbar_apply]
  have he := (differentiableAt_complex_iff_differentiableAt_real.mp (hf x z)).2
  simp only [smul_eq_mul] at he
  rw [he,← mul_assoc,Complex.I_mul_I]
  change _=0
  ring
lemma holomorphic_of_pbar_zero (f : Smooth (E × ℂ)) (hf : pbar f=0) (x : E) :
    Differentiable ℂ (fun z => (f : E × ℂ → ℂ) (x,z)) := by
  intro z
  apply differentiableAt_complex_iff_differentiableAt_real.mpr
  refine ⟨((smooth f).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) z,?_⟩
  have he := congrArg (fun g : Smooth (E × ℂ) => (g : E × ℂ → ℂ) (x,z)) hf
  rw [pbar_apply] at he
  change _=0 at he
  simp only [smul_eq_mul]
  have hh := congrArg (fun c : ℂ => -Complex.I*c) he
  simp only [mul_add,neg_mul,← mul_assoc Complex.I Complex.I,Complex.I_mul_I] at hh
  linear_combination hh

variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {k n : Type*} [Fintype k] [Fintype n]
/-- Differentiating the transport in fixed coordinates produces a homogeneous
transport for the antiholomorphic derivative. -/
lemma differentiate_transport (Q : Derivation ℂ A A) (D : k → Derivation ℂ A A)
    (hQD : ∀ r f, Q (D r f)=D r (Q f))
    (θ : k → A) (a : n → n → A) (u : n → A)
    (hθ : ∀ r, Q (θ r)=0) (ha : ∀ i j, Q (a i j)=0)
    (he : ∀ i, ∑ r, θ r*D r (u i)=∑ j, a i j*u j) :
    ∀ i, ∑ r, θ r*D r (Q (u i))=∑ j, a i j*Q (u j) := by
  intro i
  have hh := congrArg Q (he i)
  simpa only [map_sum,Derivation.leibniz,hθ,ha,hQD,mul_zero,zero_add,smul_eq_mul,add_zero] using hh
end ElasticityParameter
namespace ElasticityParameter
open Set
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {k n : Type*} [Fintype k] [Fintype n]

def characteristicPlane (e : k → E) (θ : k → ℂ) : ℂ →L[ℝ] E :=
  Complex.reCLM.smulRight (∑ r, (θ r).re • e r)+
    Complex.imCLM.smulRight (∑ r, (θ r).im • e r)
lemma characteristicPlane_one (e : k → E) (θ : k → ℂ) :
    characteristicPlane e θ 1=∑ r, (θ r).re • e r := by simp [characteristicPlane]
lemma characteristicPlane_I (e : k → E) (θ : k → ℂ) :
    characteristicPlane e θ Complex.I=∑ r, (θ r).im • e r := by simp [characteristicPlane]
lemma spatial_slice_deriv (f : Smooth (E × ℂ)) (x v : E) (z : ℂ) :
    fderiv ℝ (fun y => (f : E × ℂ → ℂ) (y,z)) x v=
      fderiv ℝ (f : E × ℂ → ℂ) (x,z) (v,0) := by
  have he : HasFDerivAt (fun y : E => (y,z)) (ContinuousLinearMap.inl ℝ E ℂ) x := by
    simpa only [ContinuousLinearMap.inl,id] using (hasFDerivAt_id x).prodMk (hasFDerivAt_const z x)
  exact congrArg (fun L : E →L[ℝ] ℂ => L v)
    (((smooth f).differentiable (by simp) (x,z)).hasFDerivAt.comp x he).fderiv
lemma characteristicPlane_principal (e : k → E) (θ : k → ℂ) (L : E →L[ℝ] ℂ) :
    L (characteristicPlane e θ 1)+Complex.I*L (characteristicPlane e θ Complex.I)=
      ∑ r, θ r*L (e r) := by
  rw [characteristicPlane_one,characteristicPlane_I]
  simp only [map_sum,map_smul,Complex.real_smul,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  calc
    _ = ((θ r).re+(θ r).im*Complex.I)*L (e r) := by ring
    _ = θ r*L (e r) := by rw [Complex.re_add_im]

lemma compact_pbar_slice {S : Set E} (hS : IsCompact S)
    (u : Smooth (E × ℂ)) (c : ℂ)
    (hs : ∀ x∉S, ∀ z, (u : E × ℂ → ℂ) (x,z)=c) (z : ℂ) :
    HasCompactSupport (fun x => (pbar u : E × ℂ → ℂ) (x,z)) := by
  apply HasCompactSupport.intro hS
  intro x hx
  have he : (fun z => (u : E × ℂ → ℂ) (x,z))=fun _ => c := funext (hs x hx)
  rw [pbar_apply,he]
  simp

/-- Holomorphy of a supported comparison is derived, not assumed. The parameter
is differentiated with the physical point fixed, including the holomorphic
principal direction, and ambient compact kernel uniqueness then applies. -/
theorem holomorphic_of_supported_transport
    (e : k → E) (θ : k → Smooth (E × ℂ))
    (hθx : ∀ r x z, (θ r : E × ℂ → ℂ) (x,z)=(θ r : E × ℂ → ℂ) (0,z))
    (hθ : ∀ r x, Differentiable ℂ (fun z => (θ r : E × ℂ → ℂ) (x,z)))
    (hplane : ∀ z, Function.Injective (characteristicPlane e (fun r => (θ r : E × ℂ → ℂ) (0,z))))
    (a : n → n → Smooth (E × ℂ))
    (ha : ∀ i j x, Differentiable ℂ (fun z => (a i j : E × ℂ → ℂ) (x,z)))
    (u : n → Smooth (E × ℂ))
    (he : ∀ i, ∑ r, θ r*delta (e r,0) (u i)=∑ j, a i j*u j)
    {S : Set E} (hS : IsCompact S) (c : n → ℂ)
    (hs : ∀ i x, x∉S → ∀ z, (u i : E × ℂ → ℂ) (x,z)=c i) :
    ∀ i x, Differentiable ℂ (fun z => (u i : E × ℂ → ℂ) (x,z)) := by
  have hd := differentiate_transport pbar (fun r => delta (e r,0))
    (fun r f => pbar_delta (e r) f) θ a u
    (fun r => pbar_zero_of_holomorphic (θ r) (hθ r))
    (fun i j => pbar_zero_of_holomorphic (a i j) (ha i j)) he
  have hb (z : ℂ) : ∀ i x, (pbar (u i) : E × ℂ → ℂ) (x,z)=0 := by
    apply ElasticityPlanar.spatial_compact_kernel
      (characteristicPlane e (fun r => (θ r : E × ℂ → ℂ) (0,z))) (hplane z)
      (fun i j x => (a i j : E × ℂ → ℂ) (x,z))
      (fun i j => (smooth (a i j)).continuous.comp (continuous_id.prodMk continuous_const))
      (fun i x => (pbar (u i) : E × ℂ → ℂ) (x,z))
      (fun i => (smooth (pbar (u i))).comp (contDiff_id.prodMk contDiff_const))
      (fun i => compact_pbar_slice hS (u i) (c i) (hs i) z)
    intro i x
    rw [characteristicPlane_principal]
    simp_rw [spatial_slice_deriv]
    have hh := congrArg (fun f : Smooth (E × ℂ) => (f : E × ℂ → ℂ) (x,z)) (hd i)
    simpa only [AddSubmonoidClass.coe_finsetSum,Finset.sum_apply,Subalgebra.coe_mul,Pi.mul_apply,
      delta_apply,hθx] using hh
  intro i x
  apply holomorphic_of_pbar_zero (u i) _ x
  apply Subtype.ext
  funext q
  exact hb q.2 i q.1
end ElasticityParameter
namespace ElasticityParameter
open scoped BigOperators InnerProductSpace

lemma real_complex_plane_injective {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (ha : a≠0) (hb : b≠0) (hab : inner ℝ a b=0) :
    Function.Injective (Complex.reCLM.smulRight a+Complex.imCLM.smulRight b : ℂ →L[ℝ] E) := by
  let J : ℂ →L[ℝ] E := Complex.reCLM.smulRight a+Complex.imCLM.smulRight b
  suffices hn : ∀ z : ℂ, J z=0 → z=0 by
    intro z w h
    apply sub_eq_zero.mp
    apply hn
    rw [map_sub,h,sub_self]
  intro z hz
  have ha0 : inner ℝ a a≠0 := by
    intro h
    exact ha (inner_self_eq_zero.mp h)
  have hb0 : inner ℝ b b≠0 := by
    intro h
    exact hb (inner_self_eq_zero.mp h)
  have hba : inner ℝ b a=0 := by rwa [real_inner_comm]
  have hr := congrArg (fun v : E => inner ℝ a v) hz
  have hi := congrArg (fun v : E => inner ℝ b v) hz
  change inner ℝ a (z.re • a+z.im • b)=inner ℝ a 0 at hr
  change inner ℝ b (z.re • a+z.im • b)=inner ℝ b 0 at hi
  simp only [inner_add_right,inner_smul_right,hab,hba,mul_zero,zero_add,add_zero,inner_zero_right] at hr hi
  apply Complex.ext
  · exact (mul_eq_zero.mp hr).resolve_right ha0
  · exact (mul_eq_zero.mp hi).resolve_right hb0

abbrev X := EuclideanSpace ℝ (Fin 3)
def basis (i : Fin 3) : X := EuclideanSpace.single i 1
lemma basis_sum_apply (v : Fin 3 → ℝ) (i : Fin 3) :
    (∑ r, v r • basis r : X) i=v i := by
  simp [basis,Pi.single_apply]

lemma null_re_im (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0) :
    (∑ i, (θ i).re*(θ i).re)=(∑ i, (θ i).im*(θ i).im) ∧
      (∑ i, (θ i).re*(θ i).im)=0 := by
  have hr := congrArg Complex.re hθ
  have hi := congrArg Complex.im hθ
  simp only [Complex.re_sum,Complex.mul_re,Complex.zero_re,Finset.sum_sub_distrib] at hr
  simp only [Complex.im_sum,Complex.mul_im,Complex.zero_im,Finset.sum_add_distrib] at hi
  have he : (∑ i, (θ i).im*(θ i).re)=(∑ i, (θ i).re*(θ i).im) :=
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [he] at hi
  constructor
  · exact sub_eq_zero.mp hr
  · linarith

lemma null_plane_injective (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0) (hne : θ≠0) :
    Function.Injective (characteristicPlane basis θ) := by
  obtain ⟨hre,him⟩ := null_re_im θ hθ
  let a : X := ∑ i, (θ i).re • basis i
  let b : X := ∑ i, (θ i).im • basis i
  have hai (i : Fin 3) : a i=(θ i).re := basis_sum_apply _ i
  have hbi (i : Fin 3) : b i=(θ i).im := basis_sum_apply _ i
  have haa : inner ℝ a a=∑ i, (θ i).re*(θ i).re := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,hai]
  have hbb : inner ℝ b b=∑ i, (θ i).im*(θ i).im := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,hbi]
  have hab : inner ℝ a b=0 := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,hai,hbi]
    simpa only [mul_comm] using him
  have he : inner ℝ a a=inner ℝ b b := by rw [haa,hbb,hre]
  have hboth : ¬ (a=0 ∧ b=0) := by
    rintro ⟨ha,hb⟩
    apply hne
    funext i
    apply Complex.ext
    · simpa only [ha,PiLp.zero_apply,Pi.zero_apply,Complex.zero_re] using (hai i).symm
    · simpa only [hb,PiLp.zero_apply,Pi.zero_apply,Complex.zero_im] using (hbi i).symm
  have ha : a≠0 := by
    intro hz
    apply hboth
    refine ⟨hz,(@inner_self_eq_zero ℝ X _ _ _).mp ?_⟩
    rw [← he,hz,inner_zero_left]
  have hb : b≠0 := by
    intro hz
    apply ha
    apply (@inner_self_eq_zero ℝ X _ _ _).mp
    rw [he,hz,inner_zero_left]
  exact real_complex_plane_injective a b ha hb hab
end ElasticityParameter
namespace ElasticityFrame
open Set Complex Module
open scoped BigOperators
abbrev X := EuclideanSpace ℝ (Fin 3)
abbrev Amp := (Fin 3 → ℂ) × ℂ

def normal (θ : Fin 3 → ℂ) : Amp →ₗ[ℂ] ℂ where
  toFun v := ∑ i, θ i*v.1 i
  map_add' v w := by simp only [Prod.fst_add,Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Prod.smul_fst,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
def fiber (θ : Fin 3 → ℂ) : Submodule ℂ Amp := (normal θ).ker
abbrev Fiber (θ : Fin 3 → ℂ) := ↥(fiber θ)

lemma finrank_fiber (θ : Fin 3 → ℂ) (hne : θ≠0) : Module.finrank ℂ (Fiber θ)=3 := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hne
  change θ i≠0 at hi
  have hs : Function.Surjective (normal θ) := by
    intro c
    refine ⟨(Pi.single i (c/(θ i)),0),?_⟩
    change (∑ j,θ j*(Pi.single i (c/(θ i)) : Fin 3 → ℂ) j)=c
    simp [Pi.single_apply]
    field_simp [hi]
  have he := (normal θ).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs,finrank_top] at he
  change Module.finrank ℂ ℂ+Module.finrank ℂ (Fiber θ)=Module.finrank ℂ Amp at he
  simp only [Module.finrank_self,Module.finrank_prod,Module.finrank_pi,Fintype.card_fin] at he
  omega

def scalarVector (θ : Fin 3 → ℂ) : Fiber θ := ⟨(0,1),by simp [fiber,normal,LinearMap.mem_ker]⟩
def nullVector (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) : Fiber θ := ⟨(θ,0),hθ⟩
def scalarPr (θ : Fin 3 → ℂ) : Fiber θ →L[ℂ] ℂ :=
  (ContinuousLinearMap.snd ℂ (Fin 3 → ℂ) ℂ).comp (fiber θ).subtypeL
def vectorPr (θ : Fin 3 → ℂ) (i : Fin 3) : Fiber θ →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj i).comp ((ContinuousLinearMap.fst ℂ (Fin 3 → ℂ) ℂ).comp (fiber θ).subtypeL)
def connection (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (t : ℂ) (q : Fin 3 → ℂ) :
    Fiber θ →L[ℂ] Fiber θ :=
  (scalarPr θ).smulRight (nullVector θ hθ)+
    t • (scalarPr θ).smulRight (scalarVector θ)+
      ∑ i, q i • (vectorPr θ i).smulRight (scalarVector θ)

lemma connection_vector (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0)
    (t : ℂ) (q : Fin 3 → ℂ) (v : Fiber θ) (i : Fin 3) :
    ((connection θ hθ t q v : Fiber θ) : Amp).1 i=θ i*(v : Amp).2 := by
  simp [connection,scalarPr,vectorPr,nullVector,scalarVector,Fin.sum_univ_three,mul_comm]
lemma connection_scalar (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0)
    (t : ℂ) (q : Fin 3 → ℂ) (v : Fiber θ) :
    ((connection θ hθ t q v : Fiber θ) : Amp).2=t*(v : Amp).2+∑ i,q i*(v : Amp).1 i := by
  simp [connection,scalarPr,vectorPr,nullVector,scalarVector,Fin.sum_univ_three]

lemma connection_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (t : E → ℂ) (q : Fin 3 → E → ℂ)
    (ht : ContDiff ℝ (⊤ : ℕ∞) t) (hq : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (q i)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => connection θ hθ (t x) (fun i => q i x)) := by
  have hs (B : Fiber θ →L[ℂ] Fiber θ) {f : E → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
      ContDiff ℝ (⊤ : ℕ∞) (fun x => f x • B) := by
    exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := ℂ) (F := Fiber θ →L[ℂ] Fiber θ)
      (((ContinuousLinearMap.id ℂ ℂ).smulRight B).restrictScalars ℝ)).comp hf
  exact (contDiff_const.add (hs _ ht)).add (ContDiff.sum (fun i _ => hs _ (hq i)))

/-- The actual rank-three constrained transport admits a smooth invertible
frame on every compact physical region. The null-plane geometry and smooth
planar solvability are proved dependencies, not existence hypotheses. -/
theorem exists_constraint_frame (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
    (t : X → ℂ) (q : Fin 3 → X → ℂ)
    (ht : ContDiff ℝ (⊤ : ℕ∞) t) (hq : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (q i))
    {C : Set X} (hC : IsCompact C) :
    ∃ V : X → Fiber θ →L[ℂ] Fiber θ, ContDiff ℝ (⊤ : ℕ∞) V ∧
      (∀ x,IsUnit (V x)) ∧
      ∀ x∈C, fderiv ℝ V x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ 1)+
        I • fderiv ℝ V x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ I)=
        connection θ hθ (t x) (fun i => q i x)*V x := by
  exact ElasticityPlanar.exists_spatial_linear_frame
    (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ)
    (ElasticityParameter.null_plane_injective θ hθ hne)
    (fun x => connection θ hθ (t x) (fun i => q i x)) (connection_smooth θ hθ t q ht hq) hC
end ElasticityFrame
namespace ElasticityPlanar
open Set Complex Module
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

section
variable {n : Type*} [Fintype n]

/-- Inhomogeneous transport in the actual ambient characteristic plane,
with arbitrary smooth coefficients and source. -/
theorem spatial_transport_of_left_inverse (J : ℂ →L[ℝ] E) (K : E →L[ℝ] ℂ)
    (hK : Function.LeftInverse K J)
    {S Ω Ω' : Set ℂ} (hS : IsCompact S) (hΩS : Ω ⊆ S)
    (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω)
    (a : n → n → E → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (f : n → E → ℂ) (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Ω) (h1 : Set.EqOn g 1 Ω') :
    ∃ u : n → E → ℂ, (∀ i, ContDiff ℝ (⊤ : ℕ∞) (u i)) ∧
      ∀ i x, K x∈Ω' → fderiv ℝ (u i) x (J 1)+I*fderiv ℝ (u i) x (J I)+
        ∑ j, a i j x*u j x=f i x := by
  let P : E →L[ℝ] E := ContinuousLinearMap.id ℝ E-J.comp K
  have hPJ (z : ℂ) : P (J z)=0 := by
    change J z-J (K (J z))=0
    rw [hK z,sub_self]
  have hrec (x : E) : P x+J (K x)=x := sub_add_cancel x (J (K x))
  let B : n → n → E × ℂ → ℂ := fun i j w => g w.2*a i j (w.1+J w.2)
  let F : n → E × ℂ → ℂ := fun i w => g w.2*f i (w.1+J w.2)
  have hB (i j) : ContDiff ℝ (⊤ : ℕ∞) (B i j) :=
    (hg.comp contDiff_snd).mul ((ha i j).comp (contDiff_fst.add (J.contDiff.comp contDiff_snd)))
  have hF (i) : ContDiff ℝ (⊤ : ℕ∞) (F i) :=
    (hg.comp contDiff_snd).mul ((hf i).comp (contDiff_fst.add (J.contDiff.comp contDiff_snd)))
  have hBc (i j) (p : E) (z : ℂ) (hz : z∉tsupport g) : B i j (p,z)=0 := by
    simp only [B,image_eq_zero_of_notMem_tsupport hz,zero_mul]
  have hFc (i) (p : E) (z : ℂ) (hz : z∉tsupport g) : F i (p,z)=0 := by
    simp only [F,image_eq_zero_of_notMem_tsupport hz,zero_mul]
  obtain ⟨v,hv,he⟩ := exists_classical_variable hS hΩS hΩ' hsub hc B hB hBc F hF hFc hg hc hs h1
  let W : n → E × ℂ → ℂ := fun i w => v w.1 i w.2
  let L := P.prod K
  let u : n → E → ℂ := fun i => W i ∘ L
  have hu (i) : ContDiff ℝ (⊤ : ℕ∞) (u i) := (hv i).comp L.contDiff
  refine ⟨u,hu,fun i x hx => ?_⟩
  have hd (z : ℂ) : fderiv ℝ (u i) x (J z)=fderiv ℝ (v (P x) i) (K x) z := by
    have hw := (((hv i).differentiable (by simp)) (L x)).hasFDerivAt.comp x L.hasFDerivAt
    have ht : HasFDerivAt (fun z : ℂ => (P x,z)) (ContinuousLinearMap.inr ℝ E ℂ) (K x) := by
      simpa only [ContinuousLinearMap.inr,id] using
        (hasFDerivAt_const (P x) (K x)).prodMk (hasFDerivAt_id (K x))
    have hw' := (((hv i).differentiable (by simp)) (L x)).hasFDerivAt.comp (K x) ht
    change HasFDerivAt (u i) _ x at hw
    change HasFDerivAt (v (P x) i) _ (K x) at hw'
    rw [hw.fderiv,hw'.fderiv]
    change fderiv ℝ (W i) (L x) (P (J z),K (J z))=fderiv ℝ (W i) (L x) (0,z)
    rw [hPJ z,hK z]
  rw [hd 1,hd I]
  have hh := he (P x) i hx
  simp only [B,F,hrec,h1 hx,Pi.one_apply,one_mul] at hh
  exact hh

theorem exists_spatial_transport (J : ℂ →L[ℝ] E) (hJ : Function.Injective J)
    (a : n → n → E → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (f : n → E → ℂ) (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    {C : Set E} (hC : IsCompact C) :
    ∃ u : n → E → ℂ, (∀ i, ContDiff ℝ (⊤ : ℕ∞) (u i)) ∧
      ∀ i x, x∈C → fderiv ℝ (u i) x (J 1)+I*fderiv ℝ (u i) x (J I)+
        ∑ j, a i j x*u j x=f i x := by
  obtain ⟨K,hK⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hJ
  obtain ⟨r,hr⟩ := (hC.image K.continuous).isBounded.subset_ball (0 : ℂ)
  have hbb : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball 0 (r+1) := by
    intro z hz
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith)
  obtain ⟨g,hg,hc,hs,h1,_⟩ := ElasticityBoundary.compact_smooth_cutoff
    (isCompact_closedBall (0 : ℂ) r) Metric.isOpen_ball hbb
  let g' : ℂ → ℂ := fun z => (g z : ℂ)
  have hg' : ContDiff ℝ (⊤ : ℕ∞) g' := Complex.ofRealCLM.contDiff.comp hg
  have hsupport : tsupport g'⊆tsupport g := by
    apply closure_mono
    intro z hz
    exact fun hh => hz (by simp only [g',hh,Complex.ofReal_zero])
  have hc' : HasCompactSupport g' := hc.of_isClosed_subset (isClosed_tsupport _) hsupport
  have h1' : Set.EqOn g' 1 (Metric.ball (0 : ℂ) r) := by
    intro z hz
    have hh := h1.self_of_nhdsSet z (Metric.ball_subset_closedBall hz)
    simp only [g',hh,Complex.ofReal_one,Pi.one_apply]
  obtain ⟨u,hu,he⟩ := spatial_transport_of_left_inverse J K hK
    (isCompact_closedBall (0 : ℂ) (r+1)) Metric.ball_subset_closedBall Metric.isOpen_ball
    (Metric.ball_subset_ball (by linarith : r≤r+1)) a ha f hf hg' hc' (hsupport.trans hs) h1'
  exact ⟨u,hu,fun i x hx => he i x (hr (Set.mem_image_of_mem K hx))⟩
end
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- Inhomogeneous spatial transport on an actual finite-dimensional complex
fiber, not a postulated planar inverse. -/
theorem exists_spatial_linear_transport (J : ℂ →L[ℝ] E) (hJ : Function.Injective J)
    (A : E → F →L[ℂ] F) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (f : E → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {C : Set E} (hC : IsCompact C) :
    ∃ u : E → F, ContDiff ℝ (⊤ : ℕ∞) u ∧
      ∀ x∈C, fderiv ℝ u x (J 1)+I • fderiv ℝ u x (J I)=A x (u x)+f x := by
  let q := Module.finBasis ℂ F
  let L : F ≃L[ℂ] (Fin (Module.finrank ℂ F) → ℂ) := q.equivFun.toContinuousLinearEquiv
  let c (i : Fin (Module.finrank ℂ F)) : F →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj i).comp L.toContinuousLinearMap
  let a := fun i j x => -c i (A x (q j))
  let g := fun i x => c i (f x)
  have ha (i j) : ContDiff ℝ (⊤ : ℕ∞) (a i j) :=
    (((c i).restrictScalars ℝ).contDiff.comp
      (((ContinuousLinearMap.apply ℂ F (q j)).restrictScalars ℝ).contDiff.comp hA)).neg
  have hg (i) : ContDiff ℝ (⊤ : ℕ∞) (g i) := ((c i).restrictScalars ℝ).contDiff.comp hf
  obtain ⟨v,hv,he⟩ := exists_spatial_transport J hJ a ha g hg hC
  let u : E → F := fun x => L.symm (fun i => v i x)
  have hu : ContDiff ℝ (⊤ : ℕ∞) u :=
    (L.symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp (contDiff_pi.mpr hv)
  have hcoord (i) : (fun x => c i (u x))=v i := by
    funext x
    change L (L.symm (fun i => v i x)) i=v i x
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hmat (x : E) (i) : c i (A x (u x))=∑ j,c i (A x (q j))*v j x := by
    have hex : u x=∑ j,L (u x) j • q j := (q.sum_equivFun _).symm
    conv_lhs => rw [hex]
    simp only [map_sum,map_smul,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    have hc : L (u x) j=v j x := congrFun (hcoord j) x
    rw [hc,mul_comm]
  refine ⟨u,hu,fun x hx => ?_⟩
  apply L.injective
  ext i
  change c i (fderiv ℝ u x (J 1)+I • fderiv ℝ u x (J I))=c i (A x (u x)+f x)
  have hd (z : ℂ) : c i (fderiv ℝ u x (J z))=fderiv ℝ (v i) x (J z) := by
    have hh := ((c i).restrictScalars ℝ).hasFDerivAt.comp x ((hu.differentiable (by simp)) x).hasFDerivAt
    change HasFDerivAt (fun x => c i (u x)) _ x at hh
    rw [hcoord] at hh
    rw [hh.fderiv]
    rfl
  rw [map_add,map_smul,hd 1,hd I,map_add,hmat]
  have hh := he i x hx
  simp only [a,g,neg_mul,Finset.sum_neg_distrib] at hh
  change _+I*_=_+_
  linear_combination hh
end ElasticityPlanar
section
open Set Complex Module
open scoped BigOperators
namespace ElasticityFrame

/-- Three genuine independent smooth columns for the null constrained system,
on an arbitrary compact physical region. -/
theorem exists_constraint_columns (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
    (t : X → ℂ) (q : Fin 3 → X → ℂ)
    (ht : ContDiff ℝ (⊤ : ℕ∞) t) (hq : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (q i))
    {C : Set X} (hC : IsCompact C) :
    ∃ B : X → Basis (Fin 3) ℂ (Fiber θ),
      (∀ ν, ContDiff ℝ (⊤ : ℕ∞) (fun x => B x ν)) ∧
      ∀ ν x, x∈C →
        fderiv ℝ (fun x => B x ν) x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ 1)+
          I • fderiv ℝ (fun x => B x ν) x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ I)=
          connection θ hθ (t x) (fun i => q i x) (B x ν) := by
  obtain ⟨V,hV,hu,he⟩ := exists_constraint_frame θ hθ hne t q ht hq hC
  let : CompleteSpace (Fiber θ) := FiniteDimensional.complete ℂ (Fiber θ)
  let b := Module.finBasisOfFinrankEq ℂ (Fiber θ) (finrank_fiber θ hne)
  let B : X → Basis (Fin 3) ℂ (Fiber θ) := fun x =>
    b.map (LinearEquiv.ofBijective (V x).toLinearMap (ContinuousLinearMap.isUnit_iff_bijective.mp (hu x)))
  have hB (ν) : ContDiff ℝ (⊤ : ℕ∞) (fun x => B x ν) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => V x (b ν))
    exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Fiber θ →L[ℂ] Fiber θ) (F := Fiber θ)
      ((ContinuousLinearMap.apply ℂ (Fiber θ) (b ν)).restrictScalars ℝ)).comp hV
  refine ⟨B,hB,fun ν x hx => ?_⟩
  have hd (v : X) : fderiv ℝ (fun x => B x ν) x v=fderiv ℝ V x v (b ν) := by
    have hh := ((ContinuousLinearMap.apply ℂ (Fiber θ) (b ν)).restrictScalars ℝ).hasFDerivAt.comp x
      ((hV.differentiable (by simp)) x).hasFDerivAt
    change HasFDerivAt (fun x => B x ν) _ x at hh
    rw [hh.fderiv]
    rfl
  rw [hd,hd]
  exact congrArg (fun L : Fiber θ →L[ℂ] Fiber θ => L (b ν)) (he x hx)

/-- Inhomogeneous constrained transport has actual smooth solutions as well. -/
theorem exists_constraint_transport (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
    (t : X → ℂ) (q : Fin 3 → X → ℂ)
    (ht : ContDiff ℝ (⊤ : ℕ∞) t) (hq : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (q i))
    (f : X → Fiber θ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {C : Set X} (hC : IsCompact C) :
    ∃ u : X → Fiber θ, ContDiff ℝ (⊤ : ℕ∞) u ∧
      ∀ x∈C, fderiv ℝ u x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ 1)+
        I • fderiv ℝ u x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ I)=
        connection θ hθ (t x) (fun i => q i x) (u x)+f x := by
  exact ElasticityPlanar.exists_spatial_linear_transport
    (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ)
    (ElasticityParameter.null_plane_injective θ hθ hne)
    (fun x => connection θ hθ (t x) (fun i => q i x)) (connection_smooth θ hθ t q ht hq) f hf hC
end ElasticityFrame

end
namespace ElasticityAugmented
open scoped BigOperators

def smoothInv (f : Smooth) (hf : ∀ x, (f : X → ℂ) x≠0) : Smooth :=
  ⟨fun x => ((f : X → ℂ) x)⁻¹,(smooth_coe f).inv hf⟩
lemma smoothInv_apply (f : Smooth) (hf : ∀ x, (f : X → ℂ) x≠0) (x : X) :
    (smoothInv f hf : X → ℂ) x=((f : X → ℂ) x)⁻¹ := rfl
lemma smoothInv_mul (f : Smooth) (hf : ∀ x, (f : X → ℂ) x≠0) : smoothInv f hf*f=1 := by
  apply Subtype.ext
  funext x
  exact inv_mul_cancel₀ (hf x)
lemma coord_inv (f : Smooth) (hf : ∀ x, (f : X → ℂ) x≠0) (i : Fin 3) :
    coord i (smoothInv f hf)=-(smoothInv f hf)^2*coord i f := by
  simpa only [smul_eq_mul] using (coord i).leibniz_of_mul_eq_one (smoothInv_mul f hf)

def thetaDerivation (θ : Fin 3 → ℂ) : Derivation ℂ Smooth Smooth := ∑ i, θ i • coord i
lemma thetaDerivation_apply (θ : Fin 3 → ℂ) (f : Smooth) :
    thetaDerivation θ f=direction (A := Smooth) coord θ f := by
  simp [thetaDerivation,direction,Fin.sum_univ_three]
lemma direction_mul (θ : Fin 3 → ℂ) (f g : Smooth) :
    direction (A := Smooth) coord θ (f*g)=direction (A := Smooth) coord θ f*g+f*direction (A := Smooth) coord θ g := by
  simpa only [thetaDerivation_apply,smul_eq_mul,mul_comm,add_comm] using (thetaDerivation θ).leibniz f g
lemma direction_add (θ : Fin 3 → ℂ) (f g : Smooth) :
    direction (A := Smooth) coord θ (f+g)=direction (A := Smooth) coord θ f+direction (A := Smooth) coord θ g := by
  exact (thetaDerivation θ).map_add f g
lemma direction_smul (θ : Fin 3 → ℂ) (c : ℂ) (f : Smooth) :
    direction (A := Smooth) coord θ (c • f)=c • direction (A := Smooth) coord θ f := by
  exact (thetaDerivation θ).map_smul c f

def changeP (r : Smooth) (a : Fin 3 → Smooth) : Fin 3 → Smooth := fun i => r*a i
def logarithmicGrad (r : Smooth) (hr : ∀ x, (r : X → ℂ) x≠0) : Fin 3 → Smooth :=
  fun i => 2*smoothInv r hr*coord i r
def changeS (k r : Smooth) (hr : ∀ x, (r : X → ℂ) x≠0)
    (a : Fin 3 → Smooth) (b : Smooth) : Smooth :=
  -(1/2 : ℂ) • (k*smoothInv r hr*b+
    ∑ i, logarithmicGrad r hr i*changeP r a i)

/-- The physical displacement change gives the literal upper transport row,
with actual coordinate derivations and no derivative identities postulated. -/
theorem normal_form_top (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x, (r : X → ℂ) x≠0) (a : Fin 3 → Smooth) (b : Smooth)
    (hR : leadingR coord θ (k-r*r) (r*r) a b=0) (i : Fin 3) :
    direction (A := Smooth) coord θ (changeP r a i)=θ i • changeS k r hr a b := by
  have he := congrFun hR i
  simp only [leadingR,sub_add_cancel,direction_mul] at he
  rw [changeP,direction_mul]
  apply Subtype.ext
  funext x
  have hh := congrArg (fun f : Smooth => (f : X → ℂ) x) he
  simp only [Pi.zero_apply] at hh
  change 2*((r : X → ℂ) x*(r : X → ℂ) x)*(direction (A := Smooth) coord θ (a i) : X → ℂ) x+
    ((direction (A := Smooth) coord θ r : X → ℂ) x*(r : X → ℂ) x+
      (r : X → ℂ) x*(direction (A := Smooth) coord θ r : X → ℂ) x)*(a i : X → ℂ) x+
      θ i*((k : X → ℂ) x*(b : X → ℂ) x+
        ((∑ j, coord j (r*r)*a j : Smooth) : X → ℂ) x)=0 at hh
  have hg : (∑ j, coord j (r*r)*a j : Smooth)=
      r*(∑ j, logarithmicGrad r hr j*changeP r a j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Subtype.ext
    funext y
    simp only [Derivation.leibniz,smul_eq_mul,logarithmicGrad,changeP,Subalgebra.coe_add,Subalgebra.coe_mul,
      Pi.add_apply,Pi.mul_apply,smoothInv_apply]
    change ((r : X → ℂ) y*(coord j r : X → ℂ) y+(r : X → ℂ) y*(coord j r : X → ℂ) y)*
      (a j : X → ℂ) y=(r : X → ℂ) y*(2*((r : X → ℂ) y)⁻¹*(coord j r : X → ℂ) y*((r : X → ℂ) y*(a j : X → ℂ) y))
    field_simp [hr y]
    ring
  rw [hg] at hh
  simp only [Subalgebra.coe_mul,Pi.mul_apply] at hh
  simp only [changeS,Subalgebra.coe_add,Subalgebra.coe_mul,Subalgebra.coe_smul,
    Pi.add_apply,Pi.mul_apply,Pi.smul_apply,smul_eq_mul,smoothInv_apply]
  field_simp [hr x]
  linear_combination hh
lemma direction_inv (θ : Fin 3 → ℂ) (f : Smooth) (hf : ∀ x, (f : X → ℂ) x≠0) :
    direction (A := Smooth) coord θ (smoothInv f hf)=
      -(smoothInv f hf)^2*direction (A := Smooth) coord θ f := by
  simpa only [thetaDerivation_apply,smul_eq_mul] using
    (thetaDerivation θ).leibniz_of_mul_eq_one (smoothInv_mul f hf)
lemma gradient_square (r : Smooth) (hr : ∀ x, (r : X → ℂ) x≠0) (i : Fin 3) :
    coord i (r*r)=r*r*logarithmicGrad r hr i := by
  apply Subtype.ext
  funext x
  simp only [Derivation.leibniz,smul_eq_mul,logarithmicGrad,Subalgebra.coe_add,Subalgebra.coe_mul,
    Pi.add_apply,Pi.mul_apply,smoothInv_apply]
  change (r : X → ℂ) x*(coord i r : X → ℂ) x+(r : X → ℂ) x*(coord i r : X → ℂ) x=
    (r : X → ℂ) x*(r : X → ℂ) x*(2*((r : X → ℂ) x)⁻¹*(coord i r : X → ℂ) x)
  field_simp [hr x]
  ring
lemma transformed_gradient (θ : Fin 3 → ℂ) (r : Smooth) (hr : ∀ x, (r : X → ℂ) x≠0)
    (a : Fin 3 → Smooth) (i : Fin 3) :
    2*coord i (r*r)*direction (A := Smooth) coord θ (a i)+
      direction (A := Smooth) coord θ (coord i (r*r))*a i =
      r*(2*logarithmicGrad r hr i*direction (A := Smooth) coord θ (changeP r a i)+
        direction (A := Smooth) coord θ (logarithmicGrad r hr i)*changeP r a i) := by
  rw [gradient_square r hr i]
  simp only [direction_mul,changeP]
  ring

def thetaGamma (θ : Fin 3 → ℂ) (r : Smooth) (hr : ∀ x, (r : X → ℂ) x≠0) : Smooth :=
  ∑ i, θ i • logarithmicGrad r hr i
lemma thetaGamma_eq (θ : Fin 3 → ℂ) (r : Smooth) (hr : ∀ x, (r : X → ℂ) x≠0) :
    thetaGamma θ r hr=2*smoothInv r hr*direction (A := Smooth) coord θ r := by
  simp only [thetaGamma,logarithmicGrad,direction,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Algebra.smul_def]
  ring

lemma transformed_scalar (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x, (r : X → ℂ) x≠0) (a : Fin 3 → Smooth) (b : Smooth)
    (hR : leadingR coord θ (k-r*r) (r*r) a b=0)
    (hS : leadingS coord θ (k-r*r) (r*r) a b=0) :
    (k+r*r)*direction (A := Smooth) coord θ b+direction (A := Smooth) coord θ k*b+
      r*(2*thetaGamma θ r hr*changeS k r hr a b+
        ∑ i, direction (A := Smooth) coord θ (logarithmicGrad r hr i)*changeP r a i)=0 := by
  have ht : (∑ i, (2*coord i (r*r)*direction (A := Smooth) coord θ (a i)+
      direction (A := Smooth) coord θ (coord i (r*r))*a i) : Smooth)=
      r*(2*thetaGamma θ r hr*changeS k r hr a b+
        ∑ i, direction (A := Smooth) coord θ (logarithmicGrad r hr i)*changeP r a i) := by
    simp_rw [transformed_gradient θ r hr a,normal_form_top θ k r hr a b hR]
    rw [← Finset.mul_sum,Finset.sum_add_distrib]
    congr 2
    simp only [thetaGamma,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Algebra.smul_def]
    ring
  rw [← ht]
  have hsum : (∑ i, (2*coord i (r*r)*direction (A := Smooth) coord θ (a i)+
      direction (A := Smooth) coord θ (coord i (r*r))*a i) : Smooth)=
      2*(∑ i, coord i (r*r)*direction (A := Smooth) coord θ (a i))+
        ∑ i, direction (A := Smooth) coord θ (coord i (r*r))*a i := by
    simp only [Finset.sum_add_distrib,Finset.mul_sum,mul_assoc]
  rw [hsum]
  apply Subtype.ext
  funext x
  have hh := congrArg (fun f : Smooth => (f : X → ℂ) x) hS
  simp only [leadingS,sub_add_cancel,Subalgebra.coe_add,Subalgebra.coe_mul,Subalgebra.coe_zero,
    Pi.add_apply,Pi.mul_apply,Pi.zero_apply] at hh
  simp only [Subalgebra.coe_add,Subalgebra.coe_mul,
    Pi.add_apply,Pi.mul_apply,Subalgebra.coe_zero,Pi.zero_apply]
  change ((k+r*r : Smooth) : X → ℂ) x*(direction (A := Smooth) coord θ b : X → ℂ) x+
    (direction (A := Smooth) coord θ k : X → ℂ) x*(b : X → ℂ) x+
    (2*((∑ i,coord i (r*r)*direction (A := Smooth) coord θ (a i) : Smooth) : X → ℂ) x+
      ((∑ i,direction (A := Smooth) coord θ (coord i (r*r))*a i : Smooth) : X → ℂ) x)=0
  simp only [Subalgebra.coe_add,Subalgebra.coe_mul,Pi.add_apply,Pi.mul_apply]
  have h2 : ((2 : Smooth) : X → ℂ) x=(2 : ℂ) := rfl
  have h4 : ((4 : Smooth) : X → ℂ) x=(4 : ℂ) := rfl
  rw [h2,h4] at hh
  linear_combination hh/2
lemma direction_sum (θ : Fin 3 → ℂ) (f : Fin 3 → Smooth) :
    direction (A := Smooth) coord θ (∑ i,f i)=∑ i,direction (A := Smooth) coord θ (f i) := by
  exact map_sum (thetaDerivation θ).toLinearMap f Finset.univ
lemma contraction_derivative (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x, (r : X → ℂ) x≠0) (a : Fin 3 → Smooth) (b : Smooth)
    (hR : leadingR coord θ (k-r*r) (r*r) a b=0) :
    direction (A := Smooth) coord θ (∑ i,logarithmicGrad r hr i*changeP r a i)=
      (∑ i,direction (A := Smooth) coord θ (logarithmicGrad r hr i)*changeP r a i)+
        thetaGamma θ r hr*changeS k r hr a b := by
  simp only [direction_sum,direction_mul,Finset.sum_add_distrib]
  congr 1
  simp only [normal_form_top θ k r hr a b hR,thetaGamma,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Algebra.smul_def]
  ring
lemma changeS_derivative (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x, (r : X → ℂ) x≠0) (a : Fin 3 → Smooth) (b : Smooth)
    (hR : leadingR coord θ (k-r*r) (r*r) a b=0) :
    direction (A := Smooth) coord θ (changeS k r hr a b)=
      -(1/2 : ℂ) • ((direction (A := Smooth) coord θ k*smoothInv r hr-
        k*(smoothInv r hr)^2*direction (A := Smooth) coord θ r)*b+
        k*smoothInv r hr*direction (A := Smooth) coord θ b+
        (∑ i,direction (A := Smooth) coord θ (logarithmicGrad r hr i)*changeP r a i)+
          thetaGamma θ r hr*changeS k r hr a b) := by
  conv_lhs => rw [changeS,direction_smul,direction_add]
  rw [contraction_derivative θ k r hr a b hR]
  simp only [direction_mul,direction_inv]
  congr 1
  ring

lemma normal_scalar_algebra (r k R K b db H J s : ℂ) (hr : r≠0) (hk : k≠0)
    (hl : k+r*r≠0) (hB : 2*r*s+k*b+r*H=0)
    (hS : (k+r*r)*db+K*b+r*(2*(2*R/r)*s+J)=0) :
    -(1/2 : ℂ)*((K/r-k*R/r^2)*b+k/r*db+J+(2*R/r)*s)=
      (r*r/(k+r*r))*(K/k-2*R/r)*s+
        (1/2 : ℂ)*(((r*r/(k+r*r))*(K/k)-(2*R/r)/2)*H-(r*r/(k+r*r))*J) := by
  apply sub_eq_zero.mp
  calc
    _ = (-k/(2*r*(k+r*r)))*((k+r*r)*db+K*b+r*(2*(2*R/r)*s+J))+
        (R/(2*r^2)-r*K/(2*k*(k+r*r)))*(2*r*s+k*b+r*H) := by
      have hp : k+r^2≠0 := by simpa only [pow_two] using hl
      field_simp [hr,hk,hl,hp]
      ring
    _ = 0 := by rw [hS,hB]; ring


def transportT (θ : Fin 3 → ℂ) (k r : Smooth) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) : Smooth :=
  smoothInv k hk*direction (A := Smooth) coord θ k-
    smoothInv (k+r*r) hl*direction (A := Smooth) coord θ (k+r*r)
def transportQ (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) : Fin 3 → Smooth := fun i =>
  (1/2 : ℂ) • ((r*r*smoothInv (k+r*r) hl*smoothInv k hk*direction (A := Smooth) coord θ k-
    (1/2 : ℂ) • thetaGamma θ r hr)*logarithmicGrad r hr i-
    r*r*smoothInv (k+r*r) hl*direction (A := Smooth) coord θ (logarithmicGrad r hr i))
lemma transportT_eq (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) :
    transportT θ k r hk hl=r*r*smoothInv (k+r*r) hl*
      (smoothInv k hk*direction (A := Smooth) coord θ k-thetaGamma θ r hr) := by
  apply Subtype.ext
  funext x
  simp only [transportT,thetaGamma_eq,direction_add,direction_mul,
    Subalgebra.coe_add,Subalgebra.coe_sub,Subalgebra.coe_mul,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,smoothInv_apply]
  have h2 : ((2 : Smooth) : X → ℂ) x=(2 : ℂ) := rfl
  rw [h2]
  have hh : (k : X → ℂ) x+(r : X → ℂ) x*(r : X → ℂ) x≠0 := hl x
  have hp : (k : X → ℂ) x+(r : X → ℂ) x^2≠0 := by simpa only [pow_two] using hh
  field_simp [hr x,hk x,hh,hp]
  ring
lemma transportQ_contract (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) (p : Fin 3 → Smooth) :
    (∑ i,transportQ θ k r hr hk hl i*p i)=
      (1/2 : ℂ) • ((r*r*smoothInv (k+r*r) hl*smoothInv k hk*direction (A := Smooth) coord θ k-
        (1/2 : ℂ) • thetaGamma θ r hr)*(∑ i,logarithmicGrad r hr i*p i)-
        r*r*smoothInv (k+r*r) hl*(∑ i,direction (A := Smooth) coord θ (logarithmicGrad r hr i)*p i)) := by
  simp only [transportQ,Fin.sum_univ_three,Algebra.smul_def]
  ring

/-- The exact bottom connection row follows from the physical leading equations,
not from a separately postulated transport system. -/
theorem normal_form_bottom (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) (a : Fin 3 → Smooth) (b : Smooth)
    (hR : leadingR coord θ (k-r*r) (r*r) a b=0)
    (hS : leadingS coord θ (k-r*r) (r*r) a b=0) :
    direction (A := Smooth) coord θ (changeS k r hr a b)=
      transportT θ k r hk hl*changeS k r hr a b+
        ∑ i,transportQ θ k r hr hk hl i*changeP r a i := by
  rw [changeS_derivative θ k r hr a b hR,transportT_eq θ k r hr hk hl,transportQ_contract]
  apply Subtype.ext
  funext x
  let R := (r : X → ℂ) x
  let K := (k : X → ℂ) x
  let DR := (direction (A := Smooth) coord θ r : X → ℂ) x
  let DK := (direction (A := Smooth) coord θ k : X → ℂ) x
  let B := (b : X → ℂ) x
  let DB := (direction (A := Smooth) coord θ b : X → ℂ) x
  let H := ((∑ i,logarithmicGrad r hr i*changeP r a i : Smooth) : X → ℂ) x
  let J := ((∑ i,direction (A := Smooth) coord θ (logarithmicGrad r hr i)*changeP r a i : Smooth) : X → ℂ) x
  let S := (changeS k r hr a b : X → ℂ) x
  have he : S=-(1/2 : ℂ)*(K*R⁻¹*B+H) := rfl
  have hB : 2*R*S+K*B+R*H=0 := by
    rw [he]
    have hn : R≠0 := hr x
    field_simp [hn]
    ring
  have hgamma : (thetaGamma θ r hr : X → ℂ) x=2*DR/R := by
    rw [thetaGamma_eq]
    change 2*R⁻¹*DR=2*DR/R
    ring
  have hvS := congrArg (fun f : Smooth => (f : X → ℂ) x) (transformed_scalar θ k r hr a b hR hS)
  simp only [Subalgebra.coe_add,Subalgebra.coe_mul,Subalgebra.coe_zero,Pi.add_apply,Pi.mul_apply,
    Pi.zero_apply,hgamma] at hvS
  change (K+R*R)*DB+DK*B+R*(2*(2*DR/R)*S+J)=0 at hvS
  have hL : K+R*R≠0 := hl x
  have ha := normal_scalar_algebra R K DR DK B DB H J S (hr x) (hk x) hL hB hvS
  simp only [Subalgebra.coe_add,Subalgebra.coe_sub,Subalgebra.coe_mul,Subalgebra.coe_pow,
    Subalgebra.coe_smul,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,Pi.smul_apply,
    smul_eq_mul,smoothInv_apply,hgamma]
  change -(1/2 : ℂ)*((DK*R⁻¹-K*(R⁻¹)^2*DR)*B+K*R⁻¹*DB+J+(2*DR/R)*S)=
    R*R*(K+R*R)⁻¹*(K⁻¹*DK-2*DR/R)*S+
      (1/2 : ℂ)*((R*R*(K+R*R)⁻¹*K⁻¹*DK-(1/2 : ℂ)*(2*DR/R))*H-R*R*(K+R*R)⁻¹*J)
  convert ha using 1 <;> simp only [div_eq_mul_inv,inv_pow] <;> ring

def inverseP (r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0) (p : Fin 3 → Smooth) : Fin 3 → Smooth :=
  fun i => smoothInv r hr*p i
def inverseS (k r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (p : Fin 3 → Smooth) (s : Smooth) : Smooth :=
  -r*smoothInv k hk*(2*s+∑ i,logarithmicGrad r hr i*p i)

lemma change_inverseP (r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0) (p : Fin 3 → Smooth) :
    changeP r (inverseP r hr p)=p := by
  funext i
  apply Subtype.ext
  funext x
  change (r : X → ℂ) x*(((r : X → ℂ) x)⁻¹*(p i : X → ℂ) x)=(p i : X → ℂ) x
  rw [← mul_assoc,mul_inv_cancel₀ (hr x),one_mul]
lemma inverse_changeP (r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0) (a : Fin 3 → Smooth) :
    inverseP r hr (changeP r a)=a := by
  funext i
  apply Subtype.ext
  funext x
  change ((r : X → ℂ) x)⁻¹*((r : X → ℂ) x*(a i : X → ℂ) x)=(a i : X → ℂ) x
  rw [← mul_assoc,inv_mul_cancel₀ (hr x),one_mul]
lemma change_inverseS (k r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (p : Fin 3 → Smooth) (s : Smooth) :
    changeS k r hr (inverseP r hr p) (inverseS k r hr hk p s)=s := by
  simp only [changeS,change_inverseP]
  apply Subtype.ext
  funext x
  simp only [inverseS,Subalgebra.coe_add,Subalgebra.coe_mul,Subalgebra.coe_neg,Subalgebra.coe_smul,
    Pi.add_apply,Pi.mul_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,smoothInv_apply]
  have h2 : ((2 : Smooth) : X → ℂ) x=(2 : ℂ) := rfl
  rw [h2]
  field_simp [hr x,hk x]
  ring
lemma inverse_changeS (k r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (a : Fin 3 → Smooth) (b : Smooth) :
    inverseS k r hr hk (changeP r a) (changeS k r hr a b)=b := by
  apply Subtype.ext
  funext x
  simp only [inverseS,changeS,Subalgebra.coe_add,Subalgebra.coe_mul,Subalgebra.coe_neg,Subalgebra.coe_smul,
    Pi.add_apply,Pi.mul_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,smoothInv_apply]
  have h2 : ((2 : Smooth) : X → ℂ) x=(2 : ℂ) := rfl
  rw [h2]
  field_simp [hr x,hk x]
  ring
lemma normal_changeP (θ : Fin 3 → ℂ) (r : Smooth) (a : Fin 3 → Smooth) :
    normal θ (changeP r a)=r*normal θ a := by
  simp only [normal,changeP,Finset.mul_sum,Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact intertwining of the vector leading equation, including nonzero source. -/
lemma leadingR_change (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (a : Fin 3 → Smooth) (b : Smooth) (i : Fin 3) :
    leadingR coord θ (k-r*r) (r*r) a b i=
      2*r*(direction (A := Smooth) coord θ (changeP r a i)-θ i • changeS k r hr a b) := by
  have hg : (∑ j,coord j (r*r)*a j : Smooth)=r*(∑ j,logarithmicGrad r hr j*changeP r a j) := by
    simp_rw [gradient_square r hr]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [changeP]
    ring
  simp only [leadingR,sub_add_cancel,hg,changeP,direction_mul,changeS]
  apply Subtype.ext
  funext x
  simp only [Subalgebra.coe_add,Subalgebra.coe_sub,Subalgebra.coe_mul,Subalgebra.coe_smul,
    Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.smul_apply,smul_eq_mul,smoothInv_apply]
  have h2 : ((2 : Smooth) : X → ℂ) x=(2 : ℂ) := rfl
  rw [h2]
  field_simp [hr x]
  ring

lemma leadingR_iff (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (a : Fin 3 → Smooth) (b : Smooth) :
    leadingR coord θ (k-r*r) (r*r) a b=0 ↔
      ∀ i, direction (A := Smooth) coord θ (changeP r a i)=θ i • changeS k r hr a b := by
  constructor
  · intro h
    exact normal_form_top θ k r hr a b h
  · intro h
    funext i
    rw [leadingR_change θ k r hr a b i,h i,sub_self,mul_zero]
    rfl
end ElasticityAugmented
namespace ElasticityFrame
open scoped BigOperators
open ElasticityAugmented

def smoothProjection {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : F →L[ℂ] ℂ) (u : X → F) (hu : ContDiff ℝ (⊤ : ℕ∞) u) : Smooth :=
  ⟨fun x => L (u x),(L.restrictScalars ℝ).contDiff.comp hu⟩

lemma projection_direction {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : F →L[ℂ] ℂ) (u : X → F) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (θ : Fin 3 → ℂ) (x : X) :
    (direction (A := Smooth) coord θ (smoothProjection L u hu) : X → ℂ) x=
      L (fderiv ℝ u x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ 1)+
        Complex.I • fderiv ℝ u x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ Complex.I)) := by
  have hd (v : X) :
      fderiv ℝ (smoothProjection L u hu : X → ℂ) x v=L (fderiv ℝ u x v) := by
    exact congrArg (fun M : X →L[ℝ] ℂ => M v)
      (((L.restrictScalars ℝ).hasFDerivAt.comp x
        ((hu.differentiable (by simp)) x).hasFDerivAt).fderiv)
  have he := ElasticityParameter.characteristicPlane_principal
    ElasticityParameter.basis θ (fderiv ℝ (smoothProjection L u hu : X → ℂ) x)
  have hb : ElasticityParameter.basis=ElasticityAugmented.e := rfl
  rw [hd,hd] at he
  rw [map_add,map_smul,smul_eq_mul,he]
  simp only [direction,Fin.sum_univ_three,Subalgebra.coe_add,Subalgebra.coe_smul,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,coord_apply,hb]

def vectorSmooth (θ : Fin 3 → ℂ) (u : X → Fiber θ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    Fin 3 → Smooth := fun i => smoothProjection (vectorPr θ i) u hu
def scalarSmooth (θ : Fin 3 → ℂ) (u : X → Fiber θ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    Smooth := smoothProjection (scalarPr θ) u hu

lemma smooth_normal (θ : Fin 3 → ℂ) (u : X → Fiber θ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ElasticityAugmented.normal θ (vectorSmooth θ u hu)=0 := by
  apply Subtype.ext
  funext x
  have h := (u x).property
  change (∑ i,θ i*((u x : Fiber θ) : Amp).1 i)=0 at h
  simp only [ElasticityAugmented.normal,Fin.sum_univ_three,Subalgebra.coe_add,
    Subalgebra.coe_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  change θ 0*((u x : Fiber θ) : Amp).1 0+θ 1*((u x : Fiber θ) : Amp).1 1+
    θ 2*((u x : Fiber θ) : Amp).1 2=0
  simpa only [Fin.sum_univ_three] using h

lemma smooth_vector_equation (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0)
    (u : X → Fiber θ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (t : Smooth) (qq : Fin 3 → Smooth)
    (x : X)
    (he : fderiv ℝ u x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ 1)+
        Complex.I • fderiv ℝ u x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ Complex.I)=
        connection θ hθ ((t : X → ℂ) x) (fun i => (qq i : X → ℂ) x) (u x)) :
    ∀ i,(direction (A := Smooth) coord θ (vectorSmooth θ u hu i) : X → ℂ) x=
      θ i*(scalarSmooth θ u hu : X → ℂ) x := by
  intro i
  rw [vectorSmooth,projection_direction,he]
  exact connection_vector θ hθ ((t : X → ℂ) x) (fun j => (qq j : X → ℂ) x) (u x) i
lemma smooth_scalar_equation (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0)
    (u : X → Fiber θ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (t : Smooth) (qq : Fin 3 → Smooth)
    (x : X)
    (he : fderiv ℝ u x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ 1)+
        Complex.I • fderiv ℝ u x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ Complex.I)=
        connection θ hθ ((t : X → ℂ) x) (fun i => (qq i : X → ℂ) x) (u x)) :
    (direction (A := Smooth) coord θ (scalarSmooth θ u hu) : X → ℂ) x=
      ((t*scalarSmooth θ u hu+∑ i,qq i*vectorSmooth θ u hu i : Smooth) : X → ℂ) x := by
  rw [scalarSmooth,projection_direction,he]
  have h := connection_scalar θ hθ ((t : X → ℂ) x) (fun i => (qq i : X → ℂ) x) (u x)
  simp only [Fin.sum_univ_three,Subalgebra.coe_add,Subalgebra.coe_mul,Pi.add_apply,Pi.mul_apply]
  change ((connection θ hθ ((t : X → ℂ) x) (fun i => (qq i : X → ℂ) x) (u x) : Fiber θ) : Amp).2=
    (t : X → ℂ) x*((u x : Fiber θ) : Amp).2+
      ((qq 0 : X → ℂ) x*((u x : Fiber θ) : Amp).1 0+
      (qq 1 : X → ℂ) x*((u x : Fiber θ) : Amp).1 1+
      (qq 2 : X → ℂ) x*((u x : Fiber θ) : Amp).1 2)
  simpa only [Fin.sum_univ_three] using h
end ElasticityFrame

end

end OAI
