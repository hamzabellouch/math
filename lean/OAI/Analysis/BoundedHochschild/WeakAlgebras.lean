import Mathlib
import OAI.Analysis.BoundedHochschild.WeakSubspaces

namespace OAI

/-! Weak-star algebra closures, inherited traces and generated finite-path primitives. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open Filter Topology
namespace BoundedHochschild
namespace WeakAlgebra
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def weakEquiv : WeakDual ℂ X ≃ₗ⋆[ℂ] M :=
  WeakDual.toStrongDual.trans e.toLinearEquiv

lemma weakEquiv_symm_continuous : Continuous (weakEquiv e).symm :=
  NormedSpace.Dual.toWeakDual_continuous.comp e.symm.continuous

lemma normal_continuous (A : M →L[ℂ] M) (hA : HasPreadjoint e A) :
    Continuous (fun f : WeakDual ℂ X => (weakEquiv e).symm (A (weakEquiv e f))) := by
  apply WeakBilin.continuous_of_continuous_eval (topDualPairing ℂ X)
  intro z
  obtain ⟨w,hw⟩ := hA z
  change Continuous (fun f : WeakDual ℂ X => e.symm (A (weakEquiv e f)) z)
  simp_rw [hw]
  simpa [weakEquiv] using WeakDual.eval_continuous (𝕜 := ℂ) w

lemma star_continuous (P : X →L⋆[ℂ] X)
    (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z))) :
    Continuous (fun f : WeakDual ℂ X => (weakEquiv e).symm (star (weakEquiv e f))) := by
  apply WeakBilin.continuous_of_continuous_eval (topDualPairing ℂ X)
  intro z
  change Continuous (fun f : WeakDual ℂ X => e.symm (star (weakEquiv e f)) z)
  simp_rw [hP]
  simpa [weakEquiv] using (WeakDual.eval_continuous (𝕜 := ℂ) (P z)).star

def linearClosure (A : StarSubalgebra ℂ M) : Submodule ℂ (WeakDual ℂ X) :=
  (A.toSubalgebra.toSubmodule.map (weakEquiv e).symm.toLinearMap).topologicalClosure

lemma linearClosure_closed (A : StarSubalgebra ℂ M) :
    IsClosed (linearClosure e A : Set (WeakDual ℂ X)) :=
  Submodule.isClosed_topologicalClosure _

lemma mem_linearClosure (A : StarSubalgebra ℂ M) {a : M} (ha : a ∈ A) :
    (weakEquiv e).symm a ∈ linearClosure e A :=
  Submodule.le_topologicalClosure _ ⟨a,ha,rfl⟩

lemma closure_stable (A : StarSubalgebra ℂ M) (T : WeakDual ℂ X → WeakDual ℂ X)
    (hT : Continuous T)
    (h : ∀ a ∈ A, T ((weakEquiv e).symm a) ∈ linearClosure e A) :
    ∀ f ∈ linearClosure e A, T f ∈ linearClosure e A := by
  apply closure_minimal _ ((linearClosure_closed e A).preimage hT)
  rintro f ⟨a,ha,rfl⟩
  exact h a ha

lemma mul_mem (A : StarSubalgebra ℂ M)
    (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
    (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
    {a b : M} (ha : (weakEquiv e).symm a ∈ linearClosure e A)
    (hb : (weakEquiv e).symm b ∈ linearClosure e A) :
    (weakEquiv e).symm (a*b) ∈ linearClosure e A := by
  have hleft (c : M) (hc : c ∈ A) :
      (weakEquiv e).symm (c*b) ∈ linearClosure e A := by
    have hs := closure_stable e A _ (normal_continuous e _ (hL c))
      (fun d hd => by
        simpa using mem_linearClosure e A (A.mul_mem hc hd))
      ((weakEquiv e).symm b) hb
    simpa using hs
  have hs := closure_stable e A _ (normal_continuous e _ (hR b))
    (fun c hc => by simpa using hleft c hc) ((weakEquiv e).symm a) ha
  simpa using hs

lemma star_mem (A : StarSubalgebra ℂ M)
    (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))
    {a : M} (ha : (weakEquiv e).symm a ∈ linearClosure e A) :
    (weakEquiv e).symm (star a) ∈ linearClosure e A := by
  have hs := closure_stable e A _ (star_continuous e P hP)
    (fun c hc => by simpa using mem_linearClosure e A (A.star_mem' hc))
    ((weakEquiv e).symm a) ha
  simpa using hs

 
def closure (A : StarSubalgebra ℂ M)
    (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
    (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
    (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z))) :
    StarSubalgebra ℂ M where
  carrier := {a | (weakEquiv e).symm a ∈ linearClosure e A}
  zero_mem' := by simp [map_zero]
  one_mem' := mem_linearClosure e A A.one_mem
  add_mem' := by intro a b ha hb; simpa using (linearClosure e A).add_mem ha hb
  mul_mem' := mul_mem e A hL hR
  algebraMap_mem' c := mem_linearClosure e A (A.algebraMap_mem c)
  star_mem' := star_mem e A P hP

instance closure_closed (A : StarSubalgebra ℂ M)
    (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
    (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
    (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z))) :
    IsClosed (closure e A hL hR P hP : Set M) :=
  (linearClosure_closed e A).preimage (weakEquiv_symm_continuous e)

variable (A : StarSubalgebra ℂ M)
    (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
    (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
    (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))

def strongEquiv : WeakSubspace.strong (linearClosure e A) ≃ₗᵢ⋆[ℂ]
    closure e A hL hR P hP where
  toFun f := ⟨e f.val, by
    change (weakEquiv e).symm (e f.val) ∈ linearClosure e A
    simpa [weakEquiv] using (WeakSubspace.mem_strong (linearClosure e A) f.val).mp f.property⟩
  invFun a := ⟨e.symm a.val, by
    rw [WeakSubspace.mem_strong]
    exact a.property⟩
  left_inv f := by apply Subtype.ext; exact e.symm_apply_apply f.val
  right_inv a := by apply Subtype.ext; exact e.apply_symm_apply a.val
  map_add' f g := by apply Subtype.ext; exact map_add e f.val g.val
  map_smul' c f := by apply Subtype.ext; exact e.map_smulₛₗ c f.val
  norm_map' f := e.norm_map f.val

 
def predualEquiv :
    StrongDual ℂ (X ⧸ WeakSubspace.preannihilator (linearClosure e A)) ≃ₗᵢ⋆[ℂ]
      closure e A hL hR P hP :=
  (WeakSubspace.quotientDualEquiv (linearClosure e A) (linearClosure_closed e A)).trans
    (strongEquiv e A hL hR P hP)

instance closure_wstar [CompleteSpace X] : WStarAlgebra (closure e A hL hR P hP) :=
  ⟨⟨X ⧸ WeakSubspace.preannihilator (linearClosure e A),inferInstance,inferInstance,
    inferInstance,⟨predualEquiv e A hL hR P hP⟩⟩⟩

lemma predualEquiv_apply (F : StrongDual ℂ
      (X ⧸ WeakSubspace.preannihilator (linearClosure e A))) (z : X) :
    e.symm ((predualEquiv e A hL hR P hP F : closure e A hL hR P hP) : M) z=
      F (Submodule.Quotient.mk z) := by
  change e.symm (e (F.comp (WeakSubspace.preannihilator (linearClosure e A)).mkQL)) z=_
  rw [e.symm_apply_apply]
  rfl

lemma predualEquiv_symm_apply_mk (a : closure e A hL hR P hP) (z : X) :
    (predualEquiv e A hL hR P hP).symm a (Submodule.Quotient.mk z)=e.symm a.val z := by
  have hs := predualEquiv_apply e A hL hR P hP
    ((predualEquiv e A hL hR P hP).symm a) z
  rw [LinearIsometryEquiv.apply_symm_apply] at hs
  exact hs.symm

lemma inherited_left_normal (b : closure e A hL hR P hP) :
    HasPreadjoint (predualEquiv e A hL hR P hP)
      (ContinuousLinearMap.mul ℂ (closure e A hL hR P hP) b) := by
  intro q
  obtain ⟨z,rfl⟩ := (WeakSubspace.preannihilator (linearClosure e A)).mkQ_surjective q
  obtain ⟨w,hw⟩ := hL b.val z
  refine ⟨Submodule.Quotient.mk w,fun a => ?_⟩
  change (predualEquiv e A hL hR P hP).symm _ (Submodule.Quotient.mk z)=_
  rw [predualEquiv_symm_apply_mk,predualEquiv_symm_apply_mk]
  exact hw a.val

lemma inherited_right_normal (b : closure e A hL hR P hP) :
    HasPreadjoint (predualEquiv e A hL hR P hP)
      ((ContinuousLinearMap.mul ℂ (closure e A hL hR P hP)).flip b) := by
  intro q
  obtain ⟨z,rfl⟩ := (WeakSubspace.preannihilator (linearClosure e A)).mkQ_surjective q
  obtain ⟨w,hw⟩ := hR b.val z
  refine ⟨Submodule.Quotient.mk w,fun a => ?_⟩
  change (predualEquiv e A hL hR P hP).symm _ (Submodule.Quotient.mk z)=_
  rw [predualEquiv_symm_apply_mk,predualEquiv_symm_apply_mk]
  exact hw a.val

end WeakAlgebra
end BoundedHochschild

 

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
namespace WeakAlgebra
open HochschildTraceNorm
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (A : StarSubalgebra ℂ M)
  (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
  (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
  (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))
  (hτ : TraceInPredual e τ)

lemma traceVector_norm_bound (b : M) :
    ‖traceVectorLinear e τ hL hτ b‖ ≤ ‖traceCLM τ‖*‖b‖ := by
  rw [traceVectorLinear_apply,norm_traceVector]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro a
  calc
    ‖tracePair τ (star b) a‖ ≤ ‖traceCLM τ‖*‖star b*a‖ := (traceCLM τ).le_opNorm _
    _ ≤ ‖traceCLM τ‖*(‖b‖*‖a‖) := mul_le_mul_of_nonneg_left
      (by simpa using norm_mul_le (star b) a) (norm_nonneg _)
    _ = (‖traceCLM τ‖*‖b‖)*‖a‖ := (mul_assoc _ _ _).symm

def traceRestriction : A →L[ℂ] (X ⧸ WeakSubspace.preannihilator (linearClosure e A)) :=
  (WeakSubspace.preannihilator (linearClosure e A)).mkQL.comp
    (((traceVectorLinear e τ hL hτ).mkContinuous ‖traceCLM τ‖
      (traceVector_norm_bound e τ hL hτ)).comp
      { toLinearMap := A.toSubalgebra.toSubmodule.subtype
        cont := continuous_subtype_val })

@[simp] lemma traceRestriction_apply (a : A) :
    traceRestriction e τ A hL hτ a=
      Submodule.Quotient.mk (traceVectorLinear e τ hL hτ (a:M)) := rfl

include hR P hP in
 

lemma denseRange_traceRestriction (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) :
    DenseRange (traceRestriction e τ A hL hτ) := by
  let Y := X ⧸ WeakSubspace.preannihilator (linearClosure e A)
  let J := traceRestriction e τ A hL hτ
  let S := (LinearMap.range J.toLinearMap).topologicalClosure
  let : IsClosed (S : Set Y) := (LinearMap.range J.toLinearMap).isClosed_topologicalClosure
  have hzero (F : StrongDual ℂ Y) (hF : ∀ a : A, F (J a)=0) : F=0 := by
    let b := predualEquiv e A hL hR P hP F
    have ha (a : M) (ha : a ∈ A) :
        (weakEquiv e).symm a (traceVector e τ hL hτ b.val)=0 := by
      have hs := hF ⟨a,ha⟩
      change F (Submodule.Quotient.mk (traceVector e τ hL hτ a))=0 at hs
      rw [← predualEquiv_apply e A hL hR P hP,traceVector_spec] at hs
      have ht : τ (star a*b.val)=0 := star_eq_zero.mp hs
      change e.symm a (traceVector e τ hL hτ b.val)=0
      rw [traceVector_spec]
      apply star_eq_zero.mpr
      have hh := congrArg star ht
      simpa only [← map_star,star_mul,star_star,star_zero] using hh
    have heval : ∀ f ∈ linearClosure e A,
        f (traceVector e τ hL hτ b.val)=0 := by
      apply closure_minimal _ (isClosed_eq
        (WeakDual.eval_continuous (𝕜 := ℂ) _) continuous_const)
      rintro f ⟨a,ha0,rfl⟩
      exact ha a ha0
    have hz : b.val=0 := by
      apply hfaith
      apply star_eq_zero.mp
      rw [← traceVector_spec e τ hL hτ b.val b.val]
      exact heval ((weakEquiv e).symm b.val) b.property
    ext q
    obtain ⟨z,rfl⟩ := (WeakSubspace.preannihilator (linearClosure e A)).mkQ_surjective q
    change F (Submodule.Quotient.mk z)=0
    rw [← predualEquiv_apply e A hL hR P hP]
    change e.symm b.val z=0
    rw [hz,map_zero]
    rfl
  change Dense (Set.range J.toLinearMap)
  rw [← LinearMap.coe_range]
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply top_unique
  intro z _
  apply (Submodule.Quotient.mk_eq_zero S).mp
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ)
  intro f
  have hf : f.comp S.mkQL=0 := by
    apply hzero
    intro a
    have ha : J a ∈ S := (LinearMap.range J.toLinearMap).le_topologicalClosure ⟨a,rfl⟩
    change f (Submodule.Quotient.mk (J a))=0
    rw [(Submodule.Quotient.mk_eq_zero S).mpr ha,map_zero]
  exact congrArg (fun F : StrongDual ℂ Y => F z) hf

include hL hR P hP hτ in
 

theorem separablePredual_of_separable [TopologicalSpace.SeparableSpace A]
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) :
    TopologicalSpace.SeparableSpace
      (X ⧸ WeakSubspace.preannihilator (linearClosure e A)) :=
  (denseRange_traceRestriction e τ A hL hR P hP hτ hfaith).separableSpace
    (traceRestriction e τ A hL hτ).continuous

end WeakAlgebra
end BoundedHochschild

 

namespace BoundedHochschild
open TopologicalSpace
variable {M : Type*}

lemma countable_submonoidClosure [Monoid M] (s : Set M) (hs : s.Countable) :
    (Submonoid.closure s : Set M).Countable := by
  let : Countable s := hs.to_subtype
  apply (Set.countable_range (fun l : List s => (l.map Subtype.val).prod)).mono
  intro x hx
  induction hx using Submonoid.closure_induction with
  | mem a ha => exact ⟨[⟨a,ha⟩],by simp⟩
  | one => exact ⟨[],rfl⟩
  | mul a b _ _ ha hb =>
    obtain ⟨l,rfl⟩ := ha
    obtain ⟨k,rfl⟩ := hb
    exact ⟨l++k,by simp⟩

 

lemma separable_starAdjoin [CStarAlgebra M] (s : Set M) (hs : s.Countable) :
    SeparableSpace (StarAlgebra.adjoin ℂ s) := by
  have hstar : (star s).Countable := by simpa only [Set.image_star] using hs.image star
  have hcount := countable_submonoidClosure (s ∪ star s) (hs.union hstar)
  have hspan : IsSeparable
      (Submodule.span ℂ (Submonoid.closure (s ∪ star s) : Set M) : Set M) :=
    hcount.isSeparable.span
  rw [← StarAlgebra.adjoin_eq_span (R := ℂ) s] at hspan
  exact hspan.separableSpace

end BoundedHochschild

 

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
namespace WeakAlgebra
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
 

instance closedSubalgebra_starOrderedRing (B : StarSubalgebra ℂ M)
    [IsClosed (B : Set M)] [StarOrderedRing M] : StarOrderedRing B := by
  apply StarOrderedRing.of_nonneg_iff'
  · intro x y h z
    change (z:M)+(x:M) ≤ (z:M)+(y:M)
    simpa only [add_comm] using add_le_add_left (show (x:M) ≤ (y:M) from h) (z:M)
  · intro a
    constructor
    · intro ha
      have hmem : CFC.sqrt (a:M) ∈ B := by
        rw [CFC.sqrt_eq_real_sqrt (a:M) (show 0 ≤ (a:M) from ha)]
        exact cfcₙ_mem (𝕜' := ℂ) Real.sqrt a.property
      refine ⟨⟨CFC.sqrt (a:M),hmem⟩,Subtype.ext ?_⟩
      change (a:M)=star (CFC.sqrt (a:M))*CFC.sqrt (a:M)
      rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (a:M))).star_eq]
      exact (CFC.sqrt_mul_sqrt_self (a:M) ha).symm
    · rintro ⟨b,rfl⟩
      exact star_mul_self_nonneg (b:M)

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (A : StarSubalgebra ℂ M)
  (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
  (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
  (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))

 

def inheritedTrace : closure e A hL hR P hP →ₚ[ℂ] ℂ where
  toLinearMap := τ.toLinearMap.comp (closure e A hL hR P hP).subtype.toLinearMap
  monotone' := fun _ _ h => OrderHomClass.mono τ h

@[simp] lemma inheritedTrace_apply (a : closure e A hL hR P hP) :
    inheritedTrace e τ A hL hR P hP a=τ (a:M) := rfl

include hL hR P hP in
lemma inheritedTrace_normal (hτ : TraceInPredual e τ) :
    TraceInPredual (predualEquiv e A hL hR P hP) (inheritedTrace e τ A hL hR P hP) := by
  obtain ⟨z,hz⟩ := hτ
  refine ⟨Submodule.Quotient.mk z,fun a => ?_⟩
  rw [predualEquiv_symm_apply_mk]
  exact hz a.val

lemma inheritedTrace_faithful (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (a : closure e A hL hR P hP)
    (ha : inheritedTrace e τ A hL hR P hP (star a*a)=0) : a=0 := by
  apply Subtype.ext
  exact hfaith a.val ha

lemma inheritedTrace_tracial (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (a b : closure e A hL hR P hP) :
    inheritedTrace e τ A hL hR P hP (a*b)=inheritedTrace e τ A hL hR P hP (b*a) :=
  htr a.val b.val

lemma inheritedTrace_one (h1 : τ 1=1) : inheritedTrace e τ A hL hR P hP 1=1 := h1

end WeakAlgebra
end BoundedHochschild
 

 

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
  (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
  (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))

 

theorem primitive_of_generated_finite_paths
    (h1 : τ 1=1) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hτ : TraceInPredual e τ) (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (D : Set M) (hD : D.Countable)
    (hpaths : ∀ S : Set M, S.Countable → D ⊆ S →
      HochschildRare.FinitePathTests
        (WeakAlgebra.inheritedTrace e τ (StarAlgebra.adjoin ℂ S) hL hR P hP))
    {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ x, differentialValue f x=0)
    (hnormal : ∀ a : Fin n → M, HasPreadjoint e (f.curryRight a)) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x=f x := by
  classical
  apply primitive_of_finite_exactness e hL hR f ‖f‖ (norm_nonneg _)
  intro E
  let images : Finset M := Finset.univ.image (fun x : Fin (n+1) → E => f (fun i => x i))
  let S : Set M := D ∪ (E : Set M) ∪ (images : Set M)
  have hS : S.Countable := (hD.union E.countable_toSet).union images.countable_toSet
  have hDS : D ⊆ S := fun a ha => Or.inl (Or.inl ha)
  let A : StarSubalgebra ℂ M := StarAlgebra.adjoin ℂ S
  let N : StarSubalgebra ℂ M := WeakAlgebra.closure e A hL hR P hP
  let Y := X ⧸ WeakSubspace.preannihilator (WeakAlgebra.linearClosure e A)
  let eN : StrongDual ℂ Y ≃ₗᵢ⋆[ℂ] N := WeakAlgebra.predualEquiv e A hL hR P hP
  let τN : N →ₚ[ℂ] ℂ := WeakAlgebra.inheritedTrace e τ A hL hR P hP
  let : TopologicalSpace.SeparableSpace A := separable_starAdjoin S hS
  let : TopologicalSpace.SeparableSpace Y :=
    WeakAlgebra.separablePredual_of_separable e τ A hL hR P hP hτ hfaith
  have h1N : τN 1=1 := h1
  have htrN : ∀ a b : N, τN (a*b)=τN (b*a) := fun a b => htr a.val b.val
  have hLN : ∀ a : N, HasPreadjoint eN (ContinuousLinearMap.mul ℂ N a) :=
    WeakAlgebra.inherited_left_normal e A hL hR P hP
  have hτN : TraceInPredual eN τN :=
    WeakAlgebra.inheritedTrace_normal e τ A hL hR P hP hτ
  have hfaithN : ∀ a : N, τN (star a*a)=0 → a=0 :=
    WeakAlgebra.inheritedTrace_faithful e τ A hL hR P hP hfaith
  have hmem (a : M) (ha : a ∈ S) : a ∈ N :=
    WeakAlgebra.mem_linearClosure e A (StarAlgebra.subset_adjoin ℂ S ha)
  apply finite_exactness_of_separable_subalgebra e eN τ τN h1N htr htrN hL hLN
    hτ hτN hfaith hfaithN N.subtype (fun _ => rfl) (hpaths S hS hDS)
    f hf hnormal (E : Set M)
  · intro a ha
    exact ⟨⟨a,hmem a (Or.inl (Or.inr ha))⟩,rfl⟩
  · intro x hx
    have hm : f x ∈ images := by
      apply Finset.mem_image.mpr
      refine ⟨fun i => ⟨x i,hx i⟩,Finset.mem_univ _,?_⟩
      rfl
    exact ⟨⟨f x,hmem (f x) (Or.inr hm)⟩,rfl⟩

end BoundedHochschild
end

end OAI
