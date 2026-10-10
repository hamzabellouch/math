import Mathlib
import OAI.Geometry.BallPacking.Holder.MarkedFrame

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open Set Function
open scoped LinearMap.FiniteRangeSetoid
variable {E F G T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]

lemma fredholm_comp (A : E →L[ℝ] F) (B : F →L[ℝ] G) (hA : A.IsFredholm) (hB : B.IsFredholm) :
    (B.comp A).IsFredholm := by
  obtain ⟨S,hS⟩ := hA.exists_isQuasiInverse
  obtain ⟨U,hU⟩ := hB.exists_isQuasiInverse
  exact ContinuousLinearMap.IsFredholm.of_isQuasiInverse (v := S.comp U) (hS.comp hU)

lemma fredholm_snd_finite : (ContinuousLinearMap.snd ℝ T E).IsFredholm := by
  apply ContinuousLinearMap.IsFredholm.of_isQuasiInverse (v := ContinuousLinearMap.inr ℝ T E)
  constructor
  · change (LinearMap.inr ℝ T E ∘ₗ LinearMap.snd ℝ T E) ≈ LinearMap.id
    apply LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mpr
    have he : (LinearMap.inr ℝ T E ∘ₗ LinearMap.snd ℝ T E)-LinearMap.id =
        -(LinearMap.inl ℝ T E ∘ₗ LinearMap.fst ℝ T E) := by ext x <;> simp
    rw [he]
    exact (LinearMap.HasFiniteRange.of_finite_dom (f := LinearMap.inl ℝ T E)).comp_right _ |>.neg
  · change (LinearMap.snd ℝ T E ∘ₗ LinearMap.inr ℝ T E) ≈ LinearMap.id
    simp

lemma fredholm_add_finite (D : E →L[ℝ] F) (hD : D.IsFredholm) (Q : E →L[ℝ] F)
    (hQ : Q.toLinearMap.HasFiniteRange) : (D+Q).IsFredholm := by
  obtain ⟨S,hS⟩ := hD.exists_isQuasiInverse
  apply ContinuousLinearMap.IsFredholm.of_isQuasiInverse (v := S)
  apply hS.congr (Setoid.refl _) ?_
  apply LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mpr
  simpa only [ContinuousLinearMap.toLinearMap_add,add_sub_cancel_left] using hQ

lemma fredholm_finite_extension (D : E →L[ℝ] F) (hD : D.IsFredholm) (Q : T →L[ℝ] F) :
    (D.comp (ContinuousLinearMap.snd ℝ T E)+Q.comp (ContinuousLinearMap.fst ℝ T E)).IsFredholm :=
  fredholm_add_finite _ (fredholm_comp _ D fredholm_snd_finite hD) _
    ((LinearMap.HasFiniteRange.of_finite_dom (f := Q.toLinearMap)).comp_right _)


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HolderCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [completeSpaceE : CompleteSpace E]
local instance freeInst1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance freeInst2 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance freeInst3 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance freeInst4 : NormedSpace ℝ (HMap ℂ E) := inferInstance

def freeModel (K : Set ℂ) : Submodule ℝ (COne ℂ E) :=
  (supportedHolder K).comap standardJetCR.toLinearMap

omit completeSpaceE in
lemma freeModel_closed [CompleteSpace E] (K : Set ℂ) :
    IsClosed (freeModel (E := E) K : Set (COne ℂ E)) :=
  (supportedHolder_closed K).preimage standardJetCR.continuous

instance (K : Set ℂ) : CompleteSpace (freeModel (E := E) K) :=
  (freeModel_closed K).completeSpace_coe

variable {K : Set ℂ}
local instance freeInst5 : NormedAddCommGroup (freeModel (E := E) K) := inferInstance
local instance freeInst6 : NormedSpace ℝ (freeModel (E := E) K) := inferInstance
local instance freeInst7 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance freeInst8 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance freeInst9 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance freeInst10 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance

def freeCR : freeModel (E := E) K →L[ℝ] supportedHolder (E := E) K :=
  standardJetCR.restrict (fun _ hu => hu)

def markedToFree : markedModel (E := E) K →L[ℝ] freeModel (E := E) K :=
  (markedModel (E := E) K).subtypeL.codRestrict _ (fun u => u.property.2)

def freeConst : E →L[ℝ] freeModel (E := E) K :=
  (constJetCLM (E := E)).codRestrict _ (fun c => by
    change standardJetCR (constJet c) ∈ supportedHolder K
    apply (mem_supportedHolder _ _).mpr
    intro z _
    simp only [standardJetCR_value,constJet_deriv,zero_apply,smul_zero,sub_zero])

def freeNormalize : freeModel (E := E) K →L[ℝ] markedModel (E := E) K :=
  (zeroNormalize.comp (freeModel (E := E) K).subtypeL).codRestrict _ (fun u => by
    apply (mem_markedModel K _).mpr
    refine ⟨?_,?_⟩
    · change cValue u.val 0-cValue u.val 0=0
      exact sub_self _
    · change standardJetCR (zeroNormalize u.val) ∈ supportedHolder K
      rw [standardJetCR_zeroNormalize]
      exact u.property)

def freeCoordinates : freeModel (E := E) K →L[ℝ] E × markedModel (E := E) K :=
  ((jetEval 0).comp (freeModel (E := E) K).subtypeL).prod freeNormalize

def freeSum : E × markedModel (E := E) K →L[ℝ] freeModel (E := E) K :=
  (freeConst (E := E) (K := K)).comp (ContinuousLinearMap.fst ℝ E (markedModel (E := E) K)) +
    (markedToFree (E := E) (K := K)).comp (ContinuousLinearMap.snd ℝ E (markedModel (E := E) K))

omit completeSpaceE in
@[simp] lemma freeSum_value [CompleteSpace E] (v : E × markedModel (E := E) K) (z : ℂ) :
    cValue (freeSum (E := E) (K := K) v).val z = v.1+cValue v.2.val z := rfl

omit completeSpaceE in
@[simp] lemma freeSum_deriv [CompleteSpace E] (v : E × markedModel (E := E) K) (z : ℂ) :
    cDeriv (freeSum (E := E) (K := K) v).val z = cDeriv v.2.val z := by
  change (0 : ℂ →L[ℝ] E)+cDeriv v.2.val z = _
  exact zero_add _

def freeEquiv : freeModel (E := E) K ≃L[ℝ] E × markedModel (E := E) K :=
  ContinuousLinearEquiv.equivOfInverse freeCoordinates freeSum
    (by
      intro v
      apply Subtype.ext
      apply cValue_ext
      intro z
      change cValue v.val 0+(cValue v.val z-cValue v.val 0)=cValue v.val z
      abel)
    (by
      intro v
      apply Prod.ext
      · change v.1+cValue v.2.val 0=v.1
        have hz : cValue v.2.val 0=0 := v.2.property.1
        rw [hz,add_zero]
      · apply Subtype.ext
        apply cValue_ext
        intro z
        change (v.1+cValue v.2.val z)-(v.1+cValue v.2.val 0)=cValue v.2.val z
        have hz : cValue v.2.val 0=0 := v.2.property.1
        rw [hz,add_zero]
        abel)

omit completeSpaceE in
lemma free_model_injective [CompleteSpace E] :
    Injective (fun u : freeModel (E := E) K => cValue u.val) := by
  intro u v h
  apply Subtype.ext
  apply cValue_ext
  intro z
  exact congrArg (fun f : ℂ →ᵇ E => f z) h

end HolderCompletion

end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
namespace HolderCompletion
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
local instance jetSuperInst1 : NormedAddCommGroup (E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance jetSuperInst2 : NormedSpace ℝ (E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
local instance jetSuperInst3 : NormedAddCommGroup (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance jetSuperInst4 : NormedSpace ℝ (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance jetSuperInst5 : NormedAddCommGroup (ℂ →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance jetSuperInst6 : NormedSpace ℝ (ℂ →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
local instance jetSuperInst7 : NormedAddCommGroup (HMap ℂ F) := inferInstance
local instance jetSuperInst8 : NormedSpace ℝ (HMap ℂ F) := inferInstance
local instance jetSuperInst9 : NormedAddCommGroup (HMap ℂ (ℂ →L[ℝ] F)) := inferInstance
local instance jetSuperInst10 : NormedSpace ℝ (HMap ℂ (ℂ →L[ℝ] F)) := inferInstance

variable {P : E → F} (hP : BoundedCThree P) (hDP : BoundedCThree (fderiv ℝ P))
    (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E)

def affineJetValue : HMap ℂ F :=
  superpose hP (affine_differentiable p a) (norm_nonneg a) (affine_fderiv_bound p a) u

def affineJetDeriv : HMap ℂ (ℂ →L[ℝ] F) :=
  bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.compL ℝ ℂ E F)
    (superpose hDP (affine_differentiable p a) (norm_nonneg a) (affine_fderiv_bound p a) u)
    (const _ a+jetDerivCLM _ u)

@[simp] lemma affineJetValue_value (z : ℂ) :
    valueCLM _ (affineJetValue hP p a u) z = P (affineCurve p a u z) := rfl

@[simp] lemma affineJetDeriv_value (z : ℂ) :
    valueCLM _ (affineJetDeriv hDP p a u) z =
      (fderiv ℝ P (affineCurve p a u z)).comp (a+cDeriv u z) := rfl

def affineJetSuperpose : COne ℂ F :=
  ⟨(affineJetValue hP p a u,affineJetDeriv hDP p a u), by
    intro z
    exact ((hP.smooth.differentiable (by simp) (affineCurve p a u z)).hasFDerivAt.comp z
      (affineCurve_hasFDerivAt p a u z))⟩

@[simp] lemma affineJetSuperpose_value (z : ℂ) :
    cValue (affineJetSuperpose hP hDP p a u) z = P (affineCurve p a u z) := rfl

def compactPerturbationJet {P : E → F} (hP : ContDiff ℝ ∞ P) (c : F)
    (hc : HasCompactSupport (fun x => P x-c)) (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) : COne ℂ F :=
  affineJetSuperpose (boundedCThree_of_compactPerturbation hP c hc)
    (boundedCThree_of_compactSupport (hP.fderiv_right (by simp))
      (by
        have he : fderiv ℝ (fun x => P x-c) = fderiv ℝ P := funext fun x => fderiv_sub_const c
        rw [←he]
        exact hc.fderiv ℝ)) p a u

@[simp] lemma compactPerturbationJet_value {P : E → F} (hP : ContDiff ℝ ∞ P) (c : F)
    (hc : HasCompactSupport (fun x => P x-c)) (p : E) (a : ℂ →L[ℝ] E) (u : COne ℂ E) (z : ℂ) :
    cValue (compactPerturbationJet hP c hc p a u) z = P (affineCurve p a u z) := rfl

end HolderCompletion

end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
namespace HolderCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [completeSpaceE : CompleteSpace E]
local instance zeroOrderInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance zeroOrderInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance zeroOrderInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance zeroOrderInst4 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance zeroOrderInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance zeroOrderInst6 : NormedSpace ℝ (HMap ℂ E) := inferInstance

def jetZeroOrder (C : HMap ℂ (E →L[ℝ] E)) : COne ℂ E →L[ℝ] HMap ℂ E :=
  (holderCoefficientAction C).comp (jetValueCLM _)

omit completeSpaceE in
@[simp] lemma jetZeroOrder_value [CompleteSpace E]
    (C : HMap ℂ (E →L[ℝ] E)) (u : COne ℂ E) (z : ℂ) :
    valueCLM _ (jetZeroOrder C u) z = valueCLM _ C z (cValue u z) := rfl

omit completeSpaceE in
lemma jetZeroOrder_eq_localized [CompleteSpace E]
    (C : HMap ℂ (E →L[ℝ] E)) (b : ContDiffBump (0:ℂ))
    (hC : ∀ z ∉ Metric.closedBall (0:ℂ) b.rIn, valueCLM _ C z = 0) :
    jetZeroOrder C = (holderCoefficientAction C).comp (localizedJetValue b) := by
  apply ContinuousLinearMap.ext
  intro u
  apply value_ext
  intro z
  change valueCLM _ C z (cValue u z) = valueCLM _ C z (b z • cValue u z)
  by_cases hz : z ∈ Metric.closedBall (0:ℂ) b.rIn
  · rw [b.one_of_mem_closedBall hz,one_smul]
  · rw [hC z hz,zero_apply,zero_apply]

lemma jetZeroOrder_isCompact [ProperSpace E] (C : HMap ℂ (E →L[ℝ] E))
    (b : ContDiffBump (0:ℂ))
    (hC : ∀ z ∉ Metric.closedBall (0:ℂ) b.rIn, valueCLM _ C z = 0) :
    IsCompactOperator (jetZeroOrder C) := by
  rw [jetZeroOrder_eq_localized C b hC]
  exact (localizedJetValue_isCompact (E := E) b).clm_comp (holderCoefficientAction C)

variable {K : Set ℂ}
local instance zeroOrderInst7 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance zeroOrderInst8 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance zeroOrderInst9 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance zeroOrderInst10 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance

def markedZeroOrder (C : HMap ℂ (E →L[ℝ] E))
    (hC : ∀ z ∉ K, valueCLM _ C z = 0) :
    markedModel (E := E) K →L[ℝ] supportedHolder (E := E) K :=
  ((jetZeroOrder C).comp (markedModel K).subtypeL).codRestrict _ (fun u => by
    apply (mem_supportedHolder _ K).mpr
    intro z hz
    change valueCLM _ C z (cValue u.val z) = 0
    rw [hC z hz,zero_apply])

omit completeSpaceE in
@[simp] lemma markedZeroOrder_value [CompleteSpace E] (C : HMap ℂ (E →L[ℝ] E))
    (hC : ∀ z ∉ K, valueCLM _ C z = 0) (u : markedModel (E := E) K) (z : ℂ) :
    valueCLM _ (markedZeroOrder C hC u).val z = valueCLM _ C z (cValue u.val z) := rfl

lemma markedZeroOrder_isCompact [ProperSpace E] (C : HMap ℂ (E →L[ℝ] E))
    (hC : ∀ z ∉ K, valueCLM _ C z = 0) (b : ContDiffBump (0:ℂ))
    (hCb : ∀ z ∉ Metric.closedBall (0:ℂ) b.rIn, valueCLM _ C z = 0) :
    IsCompactOperator (markedZeroOrder C hC) := by
  have hc := (jetZeroOrder_isCompact C b hCb).comp_clm (markedModel (E := E) K).subtypeL
  exact hc.codRestrict (fun u => by
    apply (mem_supportedHolder _ K).mpr
    intro z hz
    change valueCLM _ C z (cValue u.val z) = 0
    rw [hC z hz,zero_apply]) (supportedHolder_closed K)

end HolderCompletion

end
section
open Set Function Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem compactPerturbation_finite_kernel (T : E →L[ℝ] E) (hT : IsCompactOperator T) :
    FiniteDimensional ℝ (ContinuousLinearMap.id ℝ E+T).ker := by
  let S := ContinuousLinearMap.id ℝ E+T
  have h : ∀ x : S.ker, T x=-(x:E) := by
    intro x
    have hx := x.property
    change (x:E)+T x=0 at hx
    exact eq_neg_of_add_eq_zero_right hx
  have hc := (hT.comp_clm S.ker.subtypeL).neg
  have hm : ∀ x : S.ker, -(T (x:E))∈S.ker := by
    intro x
    rw [h,neg_neg]
    exact x.property
  have hk := hc.codRestrict hm S.isClosed_ker
  have he : Set.codRestrict (fun x : S.ker => -(T (x:E))) S.ker hm=id := by
    funext x
    apply Subtype.ext
    change -(T (x:E))=(x:E)
    rw [h,neg_neg]
  change IsCompactOperator (Set.codRestrict (fun x : S.ker => -(T (x:E))) S.ker hm) at hk
  rw [he] at hk
  exact FiniteDimensional.of_isCompactOperator_id hk


end
section
open Set Function Filter Topology
open scoped NNReal
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

 theorem compactPerturbation_antilipschitz
    (P T : E →L[ℝ] F) {K : ℝ≥0} (hP : AntilipschitzWith K P)
    (hT : IsCompactOperator T) (hi : Injective (P+T)) :
    ∃ C, AntilipschitzWith C (P+T) := by
  rw [antilipschitzWith_iff_exists_mul_le_norm]
  by_contra! h
  obtain ⟨φ, _, hφpos, hφ⟩ := exists_seq_strictAnti_tendsto (0:ℝ)
  have hx : ∀ n : ℕ, ∃ x : E, ‖x‖=1 ∧ ‖(P+T) x‖<φ n := by
    intro n
    obtain ⟨x,hx⟩ := h (φ n) (hφpos n)
    have hn : 0<‖x‖ := by
      by_contra! hh
      have hx0 : x=0 := norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))
      subst x
      simp at hx
    refine ⟨‖x‖⁻¹ • x, ?_, ?_⟩
    · rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hn.le),inv_mul_cancel₀ hn.ne']
    · rw [map_smul,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hn.le)]
      calc
        ‖x‖⁻¹ * ‖(P+T) x‖ < ‖x‖⁻¹ * (φ n * ‖x‖) := mul_lt_mul_of_pos_left hx (inv_pos.mpr hn)
        _=φ n := by field_simp
  choose x hxn hxb using hx
  have hxlim : Tendsto (fun n => (P+T) (x n)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => (hxb n).le) hφ
  obtain ⟨A,hA,hAT⟩ := hT.image_closedBall_subset_compact 1
  obtain ⟨y,_,ψ,hψ,hy⟩ := hA.tendsto_subseq
    (fun n => hAT ⟨x n, by simp only [Metric.mem_closedBall,dist_zero_right,hxn,le_refl],rfl⟩)
  have hp : Tendsto (fun n => P (x (ψ n))) atTop (𝓝 (-y)) := by
    have hh := (hxlim.comp hψ.tendsto_atTop).sub hy
    simpa only [comp_apply,add_apply,ContinuousLinearMap.coe_coe,add_sub_cancel_right,zero_sub] using hh
  have hc : CauchySeq (x ∘ ψ) := by
    have hh := hp.cauchySeq
    change Cauchy (Filter.map P (Filter.map (x ∘ ψ) atTop)) at hh
    exact (hP.isUniformInducing P.uniformContinuous).cauchy_map_iff.mp hh
  obtain ⟨z,hz⟩ := cauchySeq_tendsto_of_complete hc
  have hs : (P+T) z=0 :=
    tendsto_nhds_unique ((P+T).continuous.continuousAt.tendsto.comp hz)
      (hxlim.comp hψ.tendsto_atTop)
  have hz0 : z=0 := hi (hs.trans (map_zero (P+T)).symm)
  have hn : ‖z‖=1 := tendsto_nhds_unique (hz.norm)
    (by simpa only [comp_apply,hxn] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)))
  simp only [hz0,norm_zero,zero_ne_one] at hn


end
section
open scoped NNReal
open Set Function Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 theorem compactPerturbation_closed_range (T : E →L[ℝ] E) (hT : IsCompactOperator T) :
    IsClosed ((ContinuousLinearMap.id ℝ E+T).range : Set E) := by
  let S := ContinuousLinearMap.id ℝ E+T
  have : FiniteDimensional ℝ S.ker := compactPerturbation_finite_kernel T hT
  obtain ⟨N,hNc,hN⟩ :=
    (Submodule.ClosedComplemented.of_finiteDimensional S.ker).exists_isClosed_isCompl
  let : IsClosed (N : Set E) := hNc
  have hp : AntilipschitzWith 1 N.subtypeL :=
    (isometry_subtype_coe : Isometry (Subtype.val : N → E)).antilipschitzWith
  have hi : Injective (N.subtypeL+T.comp N.subtypeL) := by
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    have hh : (x:E)-(y:E)∈S.ker := by
      change S ((x:E)-(y:E))=0
      rw [map_sub]
      exact sub_eq_zero.mpr hxy
    have hh' : (x:E)-(y:E)∈(⊥ : Submodule ℝ E) :=
      hN.disjoint.le_bot ⟨hh,N.sub_mem x.property y.property⟩
    exact hh'
  obtain ⟨C,hC⟩ := compactPerturbation_antilipschitz N.subtypeL (T.comp N.subtypeL)
    hp (hT.comp_clm N.subtypeL) hi
  have hc := hC.isClosed_range (N.subtypeL+T.comp N.subtypeL).uniformContinuous
  have he : Set.range (N.subtypeL+T.comp N.subtypeL)=(S.range : Set E) := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨(x:E),rfl⟩
    · rintro ⟨x,rfl⟩
      have hx : x∈S.ker⊔N := by rw [hN.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp hx
      refine ⟨⟨b,hb⟩,?_⟩
      change S b=S x
      rw [←hab,map_add,show S a=0 from ha,zero_add]
  rwa [he] at hc

 theorem compactPerturbation_strict (T : E →L[ℝ] E) (hT : IsCompactOperator T) :
    IsStrictMap (ContinuousLinearMap.id ℝ E+T) := by
  let S := ContinuousLinearMap.id ℝ E+T
  let : IsClosed (S.range : Set E) := compactPerturbation_closed_range T hT
  let F : E →L[ℝ] S.range := S.codRestrict S.range (fun x => ⟨x,rfl⟩)
  have hf : Surjective F := by
    rintro ⟨y,x,hx⟩
    exact ⟨x,Subtype.ext hx⟩
  exact F.isQuotientMap hf


end
section
open Set Function Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem compactPerturbation_finite_cokernel (T : E →L[ℝ] E) (hT : IsCompactOperator T)
    (hc : IsClosed ((ContinuousLinearMap.id ℝ E+T).range : Set E)) :
    FiniteDimensional ℝ (E ⧸ (ContinuousLinearMap.id ℝ E+T).range) := by
  let S := ContinuousLinearMap.id ℝ E+T
  let Q := S.range.mkQL
  have he : ∀ x, -(Q (T x))=Q x := by
    intro x
    have hh : Q (S x)=0 := (Submodule.Quotient.mk_eq_zero _).mpr ⟨x,rfl⟩
    change Q (x+T x)=0 at hh
    rw [map_add] at hh
    exact (eq_neg_of_add_eq_zero_left hh).symm
  have hQ : IsCompactOperator Q := by
    have hh := (hT.clm_comp Q).neg
    have he' : -(Q ∘ T)=Q := by funext x; exact he x
    rwa [he'] at hh
  obtain ⟨K,hK,hKQ⟩ := hQ
  have hK0 : K∈𝓝 (0 : E ⧸ S.range) := by
    have hm := S.range.isOpenMap_mkQ.map_nhds_eq (x := 0)
      S.range.continuous_mkQ.continuousAt
    rw [map_zero] at hm
    rw [←hm]
    exact hKQ
  let : IsClosed (S.range : Set E) := hc
  exact FiniteDimensional.of_isCompactOperator_id ⟨K,hK,hK0⟩


end
section
open Set Function Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 theorem compactPerturbation_fredholm (T : E →L[ℝ] E) (hT : IsCompactOperator T) :
    (ContinuousLinearMap.id ℝ E+T).IsFredholm := by
  have : FiniteDimensional ℝ (ContinuousLinearMap.id ℝ E+T).ker :=
    compactPerturbation_finite_kernel T hT
  exact {
    isStrictMap := compactPerturbation_strict T hT
    isClosed_range := compactPerturbation_closed_range T hT
    finite_ker := this
    finite_coker := compactPerturbation_finite_cokernel T hT (compactPerturbation_closed_range T hT)
    closedComplemented_ker := Submodule.ClosedComplemented.of_finiteDimensional _ }


end
section
open Set Function Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem compactPerturbation_filtration_stops (T : E →L[ℝ] E) (hT : IsCompactOperator T)
    (V : ℕ → Submodule ℝ E) (hmono : Monotone V)
    (hclosed : ∀ n, IsClosed (V n : Set E))
    (hstep : ∀ n x, x∈V (n+1) → x+T x∈V n) :
    ∃ n, V n=V (n+1) := by
  by_contra! hne
  have hx (n : ℕ) : ∃ x∈V (n+1), ‖x‖≤3 ∧ ∀ y∈V n, 1≤‖x-y‖ := by
    have hn : ¬ V (n+1) ≤ V n := fun h => hne n (le_antisymm (hmono (Nat.le_succ n)) h)
    obtain ⟨x,hxs,hxn⟩ := Set.not_subset.mp hn
    have hc : IsClosed ((V n).comap (V (n+1)).subtype : Set (V (n+1))) :=
      (hclosed n).preimage continuous_subtype_val
    have hh : ∃ x : V (n+1), x∉(V n).comap (V (n+1)).subtype := ⟨⟨x,hxs⟩,hxn⟩
    obtain ⟨⟨x,hx⟩,hxn,hxy⟩ := riesz_lemma_of_norm_lt
      (c := (2:ℝ)) (by norm_num) (R := 3) (by norm_num) hc hh
    refine ⟨x,hx,hxn,fun y hy => ?_⟩
    exact hxy ⟨y,hmono (Nat.le_succ n) hy⟩ hy
  choose x hxv hxn hxy using hx
  have hTx {n m : ℕ} (hnm : n+1 ≤ m) : T (x n)∈V m := by
    have hs : x n+T (x n) ∈ V m := hmono (by omega) (hstep n (x n) (hxv n))
    have hz : x n∈V m := hmono hnm (hxv n)
    simpa only [add_sub_cancel_left] using (V m).sub_mem hs hz
  have hp : Pairwise (fun m n : ℕ => 1≤‖T (x m)-T (x n)‖) := by
    have : Std.Symm (fun m n : ℕ => 1≤‖T (x m)-T (x n)‖) :=
      ⟨fun _ _ h => by rwa [norm_sub_rev]⟩
    apply Pairwise.of_lt
    intro m n hmn
    let y := x n+T (x n)-T (x m)
    have hy : y∈V n := (V n).sub_mem (hstep n (x n) (hxv n)) (hTx (by omega))
    have he : x n-y=T (x m)-T (x n) := by dsimp [y]; abel
    simpa only [he] using hxy n y hy
  obtain ⟨K,hK,hTK⟩ := hT.image_closedBall_subset_compact 3
  obtain ⟨y,_,φ,hφ,hφy⟩ := hK.tendsto_subseq (fun n => hTK ⟨x n,by simpa using hxn n,rfl⟩)
  have hh := hφy.cauchySeq
  rw [Metric.cauchySeq_iff'] at hh
  obtain ⟨N,hN⟩ := hh 1 (by norm_num)
  have hlt : ‖T (x (φ (N+1)))-T (x (φ N))‖<1 := by
    simpa only [Function.comp_apply,dist_eq_norm_sub,ContinuousLinearMap.coe_coe] using hN (N+1) (by omega)
  exact hlt.not_ge (hp (hφ.injective.ne (by omega)))

 theorem compactPerturbation_kernel_stabilizes (T : E →L[ℝ] E) (hT : IsCompactOperator T) :
    ∃ n, ((ContinuousLinearMap.id ℝ E+T : E →L[ℝ] E).toLinearMap^n).ker=
      ((ContinuousLinearMap.id ℝ E+T : E →L[ℝ] E).toLinearMap^(n+1)).ker := by
  let P : E →L[ℝ] E := ContinuousLinearMap.id ℝ E+T
  apply compactPerturbation_filtration_stops T hT (fun n => (P.toLinearMap^n).ker)
    P.toLinearMap.iterateKer.monotone
  · intro n
    rw [←ContinuousLinearMap.toLinearMap_pow]
    exact (P^n).isClosed_ker
  · intro n x hx
    change (P.toLinearMap^n) (P.toLinearMap x)=0
    change (P.toLinearMap^(n+1)) x=0 at hx
    simpa only [pow_succ,Module.End.mul_apply] using hx

 theorem compactPerturbation_injective_of_surjective (T : E →L[ℝ] E) (hT : IsCompactOperator T)
    (hs : Surjective (ContinuousLinearMap.id ℝ E+T)) :
    Injective (ContinuousLinearMap.id ℝ E+T) := by
  let P : E →L[ℝ] E := ContinuousLinearMap.id ℝ E+T
  obtain ⟨n,hn⟩ := compactPerturbation_kernel_stabilizes T hT
  change (P.toLinearMap^n).ker=(P.toLinearMap^(n+1)).ker at hn
  apply (LinearMap.ker_eq_bot (f := P.toLinearMap)).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hp : ∀ n : ℕ, Surjective (P.toLinearMap^n) := by
    intro m
    induction m with
    | zero => exact fun y => ⟨y,rfl⟩
    | succ m hm =>
      intro y
      obtain ⟨z,hz⟩ := hm y
      obtain ⟨x,hx⟩ := hs z
      refine ⟨x,?_⟩
      rw [pow_succ,Module.End.mul_apply]
      exact (congrArg (P.toLinearMap^m) hx).trans hz
  obtain ⟨y,rfl⟩ := hp n x
  have hy : y∈(P.toLinearMap^(n+1)).ker := by
    change (P.toLinearMap^(n+1)) y=0
    simpa only [pow_succ',Module.End.mul_apply] using hx
  rw [←hn] at hy
  exact hy


end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
