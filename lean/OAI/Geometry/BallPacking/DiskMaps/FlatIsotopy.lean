import Mathlib
import OAI.Geometry.BallPacking.DiskMaps.SmoothInverse

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open MeasureTheory
open scoped ComplexConjugate
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
 theorem flat_isotopy_stationary {f : ℝ × E → E} (hf : ContDiff ℝ ∞ f)
    (t : ℝ) (ht : t ∉ Ioo (0:ℝ) 1) (x : E) :
    fderiv ℝ (fun p : ℝ × E => f (Real.smoothTransition p.1,p.2)) (t,x) (1,0) = 0 := by
  have hst : deriv Real.smoothTransition t = 0 :=
    smoothTransition_deriv_eq_zero (by simpa only [mem_Ioo,not_and_or,not_lt] using ht)
  have hsm : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hs := (hsm.differentiable (by simp) t).hasDerivAt
  have hi := (hs.hasFDerivAt.comp (t,x)
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (t,x)))).prodMk
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (t,x)))
  have hd := ((hf.differentiable (by simp) _).hasFDerivAt.comp (t,x) hi).fderiv
  simp only [Function.comp_def] at hd
  rw [hd]
  simp [hst]
  exact map_zero _

theorem exists_flat_embedding_extension
    (f : ℝ × E → E) (hf : ContDiff ℝ ∞ f)
    (U W : Set E) (hU : IsOpen U) (hW : IsOpen W)
    (hinj : ∀ t ∈ Icc (0:ℝ) 1, InjOn (fun x => f (t,x)) U)
    (hi : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ U,
      (fderiv ℝ (fun x => f (t,x)) x).IsInvertible)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U)
    (htrack : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ K, f (t,x) ∈ W) :
    ∃ (S : Set E) (Φ : ℝ → E ≃ₜ E), IsCompact S ∧ S ⊆ W ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (Φ p.1).symm p.2) ∧
      Φ 0 = Homeomorph.refl E ∧
      (∀ t x, x ∉ S → Φ t x = x) ∧
      (∀ x ∈ K, Φ 1 (f (0,x)) = f (1,x)) := by
  let F : ℝ × E → E := fun p => f (Real.smoothTransition p.1,p.2)
  have hF : ContDiff ℝ ∞ F :=
    hf.comp ((Real.smoothTransition.contDiff.comp contDiff_fst).prodMk contDiff_snd)
  let D : Set (ℝ × E) := Prod.snd ⁻¹' U ∩ F ⁻¹' W
  have hD : IsOpen D := (hU.preimage continuous_snd).inter (hW.preimage hF.continuous)
  have hstep (t : ℝ) : Real.smoothTransition t ∈ Icc (0:ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg t,Real.smoothTransition.le_one t⟩
  obtain ⟨S,Φ,hS,hSW,hΦ,hΦi,hΦ0,hΦs,hΦf⟩ :=
    exists_embedding_isotopy_extension F hF D hD
      (fun t => (hinj _ (hstep t)).mono (fun _ hx => hx.1))
      (fun p hp => hi _ (hstep p.1) _ hp.1) K hK W (fun _ hp => hp.2)
      (fun p hp => ⟨hKU hp.2,htrack _ (hstep p.1) _ hp.2⟩)
      (flat_isotopy_stationary hf)
  refine ⟨S,Φ,hS,hSW,hΦ,hΦi,hΦ0,hΦs,?_⟩
  intro x hx
  simpa only [F,Real.smoothTransition.zero_of_nonpos (le_refl 0),
    Real.smoothTransition.one_of_one_le (le_refl 1)] using hΦf 1 x hx

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure SupportedSmoothIsotopy (W : Set E) where
  map : ℝ → E ≃ₜ E
  smooth : ContDiff ℝ ∞ (fun p : ℝ × E => map p.1 p.2)
  inverse_smooth : ContDiff ℝ ∞ (fun p : ℝ × E => (map p.1).symm p.2)
  zero : map 0 = Homeomorph.refl E
  support : Set E
  compact_support : IsCompact support
  support_subset : support ⊆ W
  fixed : ∀ t x, x ∉ support → map t x = x

namespace SupportedSmoothIsotopy

 def refl (W : Set E) : SupportedSmoothIsotopy W where
  map := fun _ => Homeomorph.refl E
  smooth := contDiff_snd
  inverse_smooth := contDiff_snd
  zero := rfl
  support := ∅
  compact_support := isCompact_empty
  support_subset := empty_subset _
  fixed := fun _ _ _ => rfl

 def trans {W : Set E} (Φ Ψ : SupportedSmoothIsotopy W) : SupportedSmoothIsotopy W where
  map := fun t => (Φ.map t).trans (Ψ.map t)
  smooth := Ψ.smooth.comp (contDiff_fst.prodMk Φ.smooth)
  inverse_smooth := Φ.inverse_smooth.comp (contDiff_fst.prodMk Ψ.inverse_smooth)
  zero := by rw [Φ.zero,Ψ.zero]; rfl
  support := Φ.support ∪ Ψ.support
  compact_support := Φ.compact_support.union Ψ.compact_support
  support_subset := union_subset Φ.support_subset Ψ.support_subset
  fixed := by
    intro t x hx
    have hx' : x ∉ Φ.support ∧ x ∉ Ψ.support := by simpa only [mem_union,not_or] using hx
    change Ψ.map t (Φ.map t x) = x
    rw [Φ.fixed t x hx'.1,Ψ.fixed t x hx'.2]

 def symm {W : Set E} (Φ : SupportedSmoothIsotopy W) : SupportedSmoothIsotopy W where
  map := fun t => (Φ.map t).symm
  smooth := Φ.inverse_smooth
  inverse_smooth := Φ.smooth
  zero := by rw [Φ.zero]; rfl
  support := Φ.support
  compact_support := Φ.compact_support
  support_subset := Φ.support_subset
  fixed := by
    intro t x hx
    apply (Φ.map t).injective
    rw [(Φ.map t).apply_symm_apply,Φ.fixed t x hx]

 theorem mapsTo {W : Set E} (Φ : SupportedSmoothIsotopy W) (t : ℝ) :
    MapsTo (Φ.map t) W W := by
  intro x hx
  by_contra hn
  have hn' : Φ.map t x ∉ Φ.support := fun h => hn (Φ.support_subset h)
  have he := Φ.fixed t (Φ.map t x) hn'
  exact hn (((Φ.map t).injective he).symm ▸ hx)

 theorem mapsTo_compl {W : Set E} (Φ : SupportedSmoothIsotopy W) (t : ℝ) :
    MapsTo (Φ.map t) Wᶜ Wᶜ := by
  intro x hx
  rwa [Φ.fixed t x (fun h => hx (Φ.support_subset h))]

end SupportedSmoothIsotopy

def SmoothlyAmbientRelated (W K : Set E) (f g : E → E) : Prop :=
  ∃ Φ : SupportedSmoothIsotopy W, ∀ x ∈ K, Φ.map 1 (f x) = g x

namespace SmoothlyAmbientRelated
 theorem refl (W K : Set E) (f : E → E) : SmoothlyAmbientRelated W K f f :=
  ⟨SupportedSmoothIsotopy.refl W,fun _ _ => rfl⟩

 theorem trans {W K : Set E} {f g h : E → E}
    (hfg : SmoothlyAmbientRelated W K f g) (hgh : SmoothlyAmbientRelated W K g h) :
    SmoothlyAmbientRelated W K f h := by
  obtain ⟨Φ,hΦ⟩ := hfg
  obtain ⟨Ψ,hΨ⟩ := hgh
  refine ⟨Φ.trans Ψ,?_⟩
  intro x hx
  change Ψ.map 1 (Φ.map 1 (f x)) = h x
  rw [hΦ x hx,hΨ x hx]

 theorem symm {W K : Set E} {f g : E → E} (hfg : SmoothlyAmbientRelated W K f g) :
    SmoothlyAmbientRelated W K g f := by
  obtain ⟨Φ,hΦ⟩ := hfg
  refine ⟨Φ.symm,?_⟩
  intro x hx
  change (Φ.map 1).symm (g x) = f x
  rw [← hΦ x hx,(Φ.map 1).symm_apply_apply]

 theorem mono {W K J : Set E} {f g : E → E} (hfg : SmoothlyAmbientRelated W K f g)
    (hJK : J ⊆ K) : SmoothlyAmbientRelated W J f g := by
  obtain ⟨Φ,hΦ⟩ := hfg
  exact ⟨Φ,fun x hx => hΦ x (hJK hx)⟩

end SmoothlyAmbientRelated

variable [CompleteSpace E] [FiniteDimensional ℝ E]

 theorem smoothlyAmbientRelated_of_path
    (f : ℝ × E → E) (hf : ContDiff ℝ ∞ f)
    (U W : Set E) (hU : IsOpen U) (hW : IsOpen W)
    (hinj : ∀ t ∈ Icc (0:ℝ) 1, InjOn (fun x => f (t,x)) U)
    (hi : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ U,
      (fderiv ℝ (fun x => f (t,x)) x).IsInvertible)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U)
    (htrack : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ K, f (t,x) ∈ W) :
    SmoothlyAmbientRelated W K (fun x => f (0,x)) (fun x => f (1,x)) := by
  obtain ⟨S,Φ,hS,hSW,hΦ,hΦi,hΦ0,hΦs,hΦf⟩ :=
    exists_flat_embedding_extension f hf U W hU hW hinj hi K hK hKU htrack
  exact ⟨⟨Φ,hΦ,hΦi,hΦ0,S,hS,hSW,hΦs⟩,hΦf⟩

end
section

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem parametric_flat_isotopy_stationary {f : (P × ℝ) × E → E} (hf : ContDiff ℝ ∞ f)
    (y : P) (t : ℝ) (ht : t ∉ Ioo (0:ℝ) 1) (x : E) :
    fderiv ℝ (fun p : (P × ℝ) × E => f ((p.1.1,Real.smoothTransition p.1.2),p.2))
      ((y,t),x) ((0,1),0) = 0 := by
  have hst : deriv Real.smoothTransition t = 0 :=
    smoothTransition_deriv_eq_zero (by simpa only [mem_Ioo,not_and_or,not_lt] using ht)
  have hsm : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hs := (hsm.differentiable (by simp) t).hasDerivAt
  have hp := hasFDerivAt_fst (𝕜 := ℝ) (p := ((y,t),x))
  have hy := (hasFDerivAt_fst (𝕜 := ℝ) (p := (y,t))).comp ((y,t),x) hp
  have ht' := (hasFDerivAt_snd (𝕜 := ℝ) (p := (y,t))).comp ((y,t),x) hp
  have hi := (hy.prodMk (hs.hasFDerivAt.comp ((y,t),x) ht')).prodMk
    (hasFDerivAt_snd (𝕜 := ℝ) (p := ((y,t),x)))
  have hd := ((hf.differentiable (by simp) _).hasFDerivAt.comp ((y,t),x) hi).fderiv
  simp only [Function.comp_def] at hd
  rw [hd]
  simp [hst]
  exact map_zero _

variable [CompleteSpace P] [FiniteDimensional ℝ P]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem exists_parametric_flat_embedding_extension
    (f : (P × ℝ) × E → E) (hf : ContDiff ℝ ∞ f)
    (O : Set P) (hO : IsOpen O) (U W : Set E) (hU : IsOpen U) (hW : IsOpen W)
    (hinj : ∀ y ∈ O, ∀ t ∈ Icc (0:ℝ) 1, InjOn (fun x => f ((y,t),x)) U)
    (hi : ∀ y ∈ O, ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ U,
      (fderiv ℝ (fun x => f ((y,t),x)) x).IsInvertible)
    (Y : Set P) (hY : IsCompact Y) (hYO : Y ⊆ O)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U)
    (htrack : ∀ y ∈ Y, ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ K, f ((y,t),x) ∈ W) :
    ∃ (S : Set E) (Φ : P → ℝ → E ≃ₜ E), IsCompact S ∧ S ⊆ W ∧
      ContDiff ℝ ∞ (fun p : (P × ℝ) × E => Φ p.1.1 p.1.2 p.2) ∧
      ContDiff ℝ ∞ (fun p : (P × ℝ) × E => (Φ p.1.1 p.1.2).symm p.2) ∧
      (∀ y, Φ y 0 = Homeomorph.refl E) ∧
      (∀ y t x, x ∉ S → Φ y t x = x) ∧
      (∀ y ∈ Y, ∀ x ∈ K, Φ y 1 (f ((y,0),x)) = f ((y,1),x)) := by
  let F : (P × ℝ) × E → E := fun p => f ((p.1.1,Real.smoothTransition p.1.2),p.2)
  have hF : ContDiff ℝ ∞ F := hf.comp
    ((contDiff_fst.fst.prodMk (Real.smoothTransition.contDiff.comp contDiff_fst.snd)).prodMk contDiff_snd)
  let D : Set ((P × ℝ) × E) := (fun p => p.1.1) ⁻¹' O ∩ (Prod.snd ⁻¹' U ∩ F ⁻¹' W)
  have hD : IsOpen D := (hO.preimage continuous_fst.fst).inter
    ((hU.preimage continuous_snd).inter (hW.preimage hF.continuous))
  have hstep (t : ℝ) : Real.smoothTransition t ∈ Icc (0:ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg t,Real.smoothTransition.le_one t⟩
  obtain ⟨S,Φ,hS,hSW,hΦ,hΦi,hΦ0,hΦs,hΦf⟩ :=
    exists_parametric_embedding_isotopy_extension F hF D hD
      (fun q => by
        intro x hx z hz he
        exact hinj q.1 hx.1 _ (hstep q.2) hx.2.1 hz.2.1 he)
      (fun p hp => hi _ hp.1 _ (hstep p.1.2) _ hp.2.1) Y hY K hK W (fun _ hp => hp.2.2)
      (fun p hp => ⟨hYO hp.1.1,hKU hp.2,htrack _ hp.1.1 _ (hstep p.1.2) _ hp.2⟩)
      (parametric_flat_isotopy_stationary hf)
  refine ⟨S,Φ,hS,hSW,hΦ,hΦi,hΦ0,hΦs,?_⟩
  intro y hy x hx
  simpa only [F,Real.smoothTransition.zero_of_nonpos (le_refl 0),
    Real.smoothTransition.one_of_one_le (le_refl 1)] using hΦf y hy 1 x hx

end
section

universe u
variable {P E F : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem contDiff_fixed_integral {f : ℝ × P → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p => ∫ t in (0:ℝ)..1, f (t,p)) := by
  let τ : C(Time,ℝ × P) := ⟨fun t => ((t:ℝ),0),continuous_subtype_val.prodMk continuous_const⟩
  let v : P → C(Time,ℝ × P) := fun p => τ + constantPath (0,p)
  have hv : ContDiff ℝ ∞ v := contDiff_const.add
    ((constantPath (E := ℝ × P)).contDiff.comp (contDiff_const.prodMk contDiff_id))
  let I : C(Time,F) →L[ℝ] F := (ContinuousMap.evalCLM ℝ (⟨1,by simp⟩ : Time)).comp pathIntegral
  have he : (fun p => ∫ t in (0:ℝ)..1, f (t,p)) =
      fun p => I ((⟨f,hf.continuous⟩ : C(ℝ × P,F)).comp (v p)) := by
    funext p
    change _ = ∫ t in (0:ℝ)..1, extendPath ((⟨f,hf.continuous⟩ : C(ℝ × P,F)).comp (v p)) t
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    rw [show extendPath ((⟨f,hf.continuous⟩ : C(ℝ × P,F)).comp (v p)) t =
      ((⟨f,hf.continuous⟩ : C(ℝ × P,F)).comp (v p)) ⟨t,ht⟩ from extendPath_coe _ ⟨t,ht⟩]
    change f (t,p) = f ((t,0)+(0,p))
    simp
  rw [he]
  exact I.contDiff.comp ((postcomp_contDiff hf).comp hv)

def smoothBlowup (f : E → F) (p : ℝ × E) : F :=
  ∫ s in (0:ℝ)..1, fderiv ℝ f ((s*p.1) • p.2) p.2

 theorem smoothBlowup_contDiff {f : E → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (smoothBlowup f) := by
  unfold smoothBlowup
  apply contDiff_fixed_integral (f := fun q : ℝ × (ℝ × E) =>
    fderiv ℝ f ((q.1*q.2.1) • q.2.2) q.2.2)
  exact ((hf.fderiv_right (by simp)).comp
    ((contDiff_fst.mul contDiff_snd.fst).smul contDiff_snd.snd)).clm_apply contDiff_snd.snd

omit [FiniteDimensional ℝ E] in
 theorem smoothBlowup_zero (f : E → F) (x : E) :
    smoothBlowup f (0,x) = fderiv ℝ f 0 x := by
  simp [smoothBlowup]

omit [FiniteDimensional ℝ E] in
 theorem smul_smoothBlowup {f : E → F} (hf : ContDiff ℝ ∞ f) (t : ℝ) (x : E) :
    t • smoothBlowup f (t,x) = f (t • x)-f 0 := by
  have hd (s : ℝ) : HasDerivAt (fun r : ℝ => f ((r*t) • x))
      (t • fderiv ℝ f ((s*t) • x) x) s := by
    simpa only [Function.comp_def,id_eq,one_mul,map_smul] using
      (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s
        (((hasDerivAt_id s).mul_const t).smul_const x)
  have hc : Continuous (fun s : ℝ => t • fderiv ℝ f ((s*t) • x) x) :=
    continuous_const.smul (((hf.fderiv_right (m := ∞) (by simp)).continuous.comp
      ((continuous_id.mul continuous_const).smul continuous_const)).clm_apply continuous_const)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (hc.intervalIntegrable 0 1)
  simpa only [intervalIntegral.integral_smul,one_mul,zero_mul,zero_smul,smoothBlowup] using hi

omit [FiniteDimensional ℝ E] in
 theorem smoothBlowup_eq {f : E → F} (hf : ContDiff ℝ ∞ f) {t : ℝ} (ht : t ≠ 0) (x : E) :
    smoothBlowup f (t,x) = t⁻¹ • (f (t • x)-f 0) := by
  rw [← smul_smoothBlowup hf t x,smul_smul,inv_mul_cancel₀ ht,one_smul]

omit [FiniteDimensional ℝ E] in
 theorem smoothBlowup_injOn {f : E → F} (hf : ContDiff ℝ ∞ f)
    {U : Set E} (hinj : InjOn f U) (hi0 : Injective (fderiv ℝ f 0)) (t : ℝ) :
    InjOn (fun x => smoothBlowup f (t,x)) {x | t • x ∈ U} := by
  intro x hx y hy he
  by_cases ht : t = 0
  · subst t
    simp only [smoothBlowup_zero] at he
    exact hi0 he
  · have h := congrArg (fun z : F => t • z) he
    rw [smul_smoothBlowup hf,smul_smoothBlowup hf,sub_left_inj] at h
    exact (smul_right_injective E ht) (hinj hx hy h)

omit [FiniteDimensional ℝ E] in
 theorem smoothBlowup_hasFDerivAt {f : E → F} (hf : ContDiff ℝ ∞ f) (t : ℝ) (x : E) :
    HasFDerivAt (fun x => smoothBlowup f (t,x)) (fderiv ℝ f (t • x)) x := by
  by_cases ht : t = 0
  · subst t
    simpa only [smoothBlowup_zero,zero_smul] using (fderiv ℝ f 0).hasFDerivAt
  · have he : (fun x => smoothBlowup f (t,x)) = fun x => t⁻¹ • (f (t • x)-f 0) :=
      funext (smoothBlowup_eq hf ht)
    rw [he]
    have hd := (((hf.differentiable (by simp) (t • x)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_smul t)).sub_const (f 0)).const_smul t⁻¹
    have hde : t⁻¹ • (fderiv ℝ f (t • x)).comp (t • ContinuousLinearMap.id ℝ E) =
        fderiv ℝ f (t • x) := by
      ext v
      change t⁻¹ • fderiv ℝ f (t • x) (t • v) = fderiv ℝ f (t • x) v
      rw [map_smul,smul_smul,inv_mul_cancel₀ ht,one_smul]
    convert hd using 1
    · rfl
    · exact hde.symm

end

def complexPair (a b : ℂ) : ℂ →L[ℝ] ℂ :=
  a • ContinuousLinearMap.id ℝ ℂ + b • Complex.conjCLE.toContinuousLinearMap

@[simp] theorem complexPair_apply (a b z : ℂ) : complexPair a b z = a*z+b*conj z := rfl

 theorem realLinear_complex_decomposition (A : ℂ →L[ℝ] ℂ) :
    A = complexPair ((A 1-Complex.I*A Complex.I)/2) ((A 1+Complex.I*A Complex.I)/2) := by
  ext z
  have hz : z = z.re • (1:ℂ) + z.im • Complex.I := by
    simpa only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_one,mul_one] using
      (Complex.re_add_im z).symm
  conv_lhs => rw [hz,map_add,map_smul,map_smul]
  simp only [complexPair_apply,Complex.real_smul]
  apply Complex.ext <;> simp [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im] <;> ring

 theorem complex_decomposition_orientation (A : ℂ →L[ℝ] ℂ) :
    Complex.normSq ((A 1-Complex.I*A Complex.I)/2) -
      Complex.normSq ((A 1+Complex.I*A Complex.I)/2) =
      (A 1).re * (A Complex.I).im - (A 1).im * (A Complex.I).re := by
  simp [Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  ring

 theorem complexPair_invertible {a b : ℂ} (h : ‖b‖ < ‖a‖) :
    (complexPair a b).IsInvertible := by
  have hi : Injective (complexPair a b) := by
    apply (injective_iff_map_eq_zero (complexPair a b)).mpr
    intro z hz
    change a*z+b*conj z = 0 at hz
    have hn := congrArg norm (eq_neg_of_add_eq_zero_left hz)
    rw [norm_mul,norm_neg,norm_mul,Complex.norm_conj] at hn
    have hz0 : ‖z‖ = 0 := by nlinarith [norm_nonneg z]
    exact norm_eq_zero.mp hz0
  have hs := (LinearMap.injective_iff_surjective (f := (complexPair a b).toLinearMap)).mp hi
  exact ⟨ContinuousLinearEquiv.ofBijective (complexPair a b)
    (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs),rfl⟩

theorem exists_positive_complex_linear_path (A : ℂ →L[ℝ] ℂ)
    (hA : 0 < (A 1).re * (A Complex.I).im - (A 1).im * (A Complex.I).re) :
    ∃ L : ℝ → ℂ →L[ℝ] ℂ, ContDiff ℝ ∞ L ∧
      (∀ t, (L t).IsInvertible) ∧ L 0 = ContinuousLinearMap.id ℝ ℂ ∧ L 1 = A ∧
      (∀ t ≤ 0, L t = ContinuousLinearMap.id ℝ ℂ) ∧ (∀ t, 1 ≤ t → L t = A) := by
  let a := (A 1-Complex.I*A Complex.I)/2
  let b := (A 1+Complex.I*A Complex.I)/2
  have hab : ‖b‖ < ‖a‖ := by
    have he := complex_decomposition_orientation A
    change Complex.normSq a-Complex.normSq b = _ at he
    rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq] at he
    nlinarith [norm_nonneg a,norm_nonneg b]
  have ha : a ≠ 0 := norm_pos_iff.mp ((norm_nonneg b).trans_lt hab)
  let s : ℝ → ℝ := fun t => Real.smoothTransition (2*t)
  let r : ℝ → ℝ := fun t => Real.smoothTransition (2*t-1)
  let α : ℝ → ℂ := fun t => Complex.exp (s t • Complex.log a)
  let β : ℝ → ℂ := fun t => r t • b
  let L : ℝ → ℂ →L[ℝ] ℂ := fun t => complexPair (α t) (β t)
  have hs : ContDiff ℝ ∞ s := Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id)
  have hr : ContDiff ℝ ∞ r := Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hα : ContDiff ℝ ∞ α := (hs.smul contDiff_const).cexp
  have hβ : ContDiff ℝ ∞ β := hr.smul contDiff_const
  have hL : ContDiff ℝ ∞ L := (hα.smul contDiff_const).add (hβ.smul contDiff_const)
  have hαa (t : ℝ) (ht : 1 ≤ 2*t) : α t = a := by
    dsimp [α,s]
    simp only [Real.smoothTransition.one_of_one_le ht,Complex.ofReal_one,one_mul,Complex.exp_log ha]
  have hL0 (t : ℝ) (ht : t ≤ 0) : L t = ContinuousLinearMap.id ℝ ℂ := by
    have ht0 : 2*t ≤ 0 := by linarith
    have ht1 : 2*t-1 ≤ 0 := by linarith
    ext z
    simp [L,α,β,s,r,Real.smoothTransition.zero_of_nonpos ht0,
      Real.smoothTransition.zero_of_nonpos ht1]
  have hL1 (t : ℝ) (ht : 1 ≤ t) : L t = A := by
    have ht1 : 1 ≤ 2*t-1 := by linarith
    have ht0 : 1 ≤ 2*t := by linarith
    change complexPair (α t) (r t • b) = A
    rw [hαa t ht0,show r t = 1 from Real.smoothTransition.one_of_one_le ht1,one_smul]
    exact (realLinear_complex_decomposition A).symm
  refine ⟨L,hL,?_,hL0 0 le_rfl,hL1 1 le_rfl,hL0,hL1⟩
  intro t
  apply complexPair_invertible
  by_cases ht : 2*t-1 ≤ 0
  · have hr0 : r t = 0 := Real.smoothTransition.zero_of_nonpos ht
    change ‖r t • b‖ < ‖Complex.exp (s t • Complex.log a)‖
    rw [hr0,zero_smul,norm_zero]
    exact norm_pos_iff.mpr (Complex.exp_ne_zero _)
  · have ht0 : 1 ≤ 2*t := by linarith
    change ‖r t • b‖ < ‖α t‖
    rw [hαa t ht0,norm_smul,Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
    exact (mul_le_of_le_one_left (norm_nonneg b) (Real.smoothTransition.le_one _)).trans_lt hab

variable {P E : Type*} [TopologicalSpace P] [TopologicalSpace E]

theorem exists_small_positive_perturbation {K : Set P} (hK : IsCompact K)
    {F : ℝ × P → E} (hF : Continuous F) {W : Set E} (hW : IsOpen W)
    (h0 : ∀ p ∈ K, F (0,p) ∈ W) :
    ∃ δ > 0, ∀ ε : ℝ, |ε| < δ → ∀ p ∈ K, F (ε,p) ∈ W := by
  have hsub : ({0} : Set ℝ) ×ˢ K ⊆ F ⁻¹' W := by
    rintro ⟨ε,p⟩ ⟨hε,hp⟩
    have he : ε = 0 := hε
    subst ε
    exact h0 p hp
  obtain ⟨U,V,hU,_,h0U,hKV,hUV⟩ :=
    generalized_tube_lemma isCompact_singleton hK (hW.preimage hF) hsub
  obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (h0U (mem_singleton 0)))
  refine ⟨δ,hδ,?_⟩
  intro ε hε p hp
  exact hUV ⟨hδU (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hε),hKV hp⟩

end PackingSufficiencySupport.Hamiltonian
end

end OAI
