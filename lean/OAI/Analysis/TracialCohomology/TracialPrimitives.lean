import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.FinitePaths

namespace OAI

/-! Tracial primitives for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder
namespace BoundedHochschild
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [TopologicalSpace.SeparableSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hII : PopaTypeII.NoAbelianCorners M)

include e τ hτ htr hfaith h1 hII

theorem typeII_last_normal_primitive {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ v, differentialValue f v=0)
    (hn : ∀ a : Fin n → M, HasPreadjoint e (f.curryRight a)) :
    ∃ g : Cochain M n, ‖g‖≤‖f‖ ∧ ∀ v, differentialValue g v=f v := by
  obtain ⟨hL,hR⟩ := HochschildSakai.abstract_multiplication_normal e
  exact primitive_of_separable_normal_finite_paths e τ h1 htr hfaith hL hR hτ
    (PopaCenter.produced_finite_paths e τ hτ htr hfaith h1 hII) f hf hn

theorem typeII_ordinary_primitive {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ v, differentialValue f v=0) :
    ∃ g : Cochain M n, ‖g‖≤12*‖f‖ ∧ ∀ v, differentialValue g v=f v := by
  obtain ⟨g,hg,hgf⟩ := typeII_last_normal_primitive e τ hτ htr hfaith h1 hII
    (reducedNormalCocycle e f) (reducedNormalCocycle_cocycle e f hf)
    (reducedNormalCocycle_normal e f)
  refine ⟨g+normalCorrection e f, ?_, ?_⟩
  · have hF := reducedNormalCocycle_norm e f
    have hh := normalCorrection_norm e f
    exact (norm_add_le _ _).trans (by linarith)
  · intro v
    rw [differentialValue_add,hgf]
    exact (normal_correction_identity e f hf v).symm
end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace PopaSeparable
open BoundedHochschild PopaCenter PopaTypeII PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
variable (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
  (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
  (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))

include hτ htr hfaith h1 in

theorem typeII_seed (hII : NoAbelianCorners M) (S : Set M) (hS : S.Countable) :
    ∃ R : Set M, R.Countable ∧ S ⊆ R ∧
      NoAbelianCorners (WeakAlgebra.closure e (StarAlgebra.adjoin ℂ R) hL hR P hP) := by
  classical
  have hE1 : Homogeneous e τ hτ htr hfaith (1:M) := by
    change average e τ hτ htr hfaith 1=(τ 1).re • (1:M)
    rw [average_id e τ hτ htr hfaith h1 (fun x => Commute.one_left x),h1,Complex.one_re,one_smul]
  have hm (k : ℕ) := exists_homogeneous_system e τ hτ htr hfaith h1 hII
    (2^(k+1)) (pow_pos (by decide) _) (IsStarProjection.one M) hE1
  let s (k : ℕ) : System (2^(k+1)) (1:M) := Classical.choice (hm k)
  let T (k : ℕ) : Set M := Set.range (fun ij : Fin (2^(k+1)) × Fin (2^(k+1)) => (s k).entry ij.1 ij.2)
  let R := S ∪ ⋃ k, T k
  have hRcount : R.Countable := hS.union (Set.countable_iUnion (fun k => Set.countable_range _))
  refine ⟨R,hRcount,Set.subset_union_left,?_⟩
  let A := StarAlgebra.adjoin ℂ R
  let N := WeakAlgebra.closure e A hL hR P hP
  let eN := WeakAlgebra.predualEquiv e A hL hR P hP
  let τN := WeakAlgebra.inheritedTrace e τ A hL hR P hP
  apply noAbelianCorners_of_matrices eN τN
    (WeakAlgebra.inheritedTrace_normal e τ A hL hR P hP hτ)
    (WeakAlgebra.inheritedTrace_tracial e τ A hL hR P hP htr)
    (WeakAlgebra.inheritedTrace_faithful e τ A hL hR P hP hfaith)
    (WeakAlgebra.inheritedTrace_one e τ A hL hR P hP h1)
  intro k
  have hmem (i j : Fin (2^(k+1))) : (s k).entry i j ∈ N :=
    WeakAlgebra.mem_linearClosure e A (StarAlgebra.subset_adjoin ℂ R
      (Or.inr (Set.mem_iUnion.mpr ⟨k,⟨(i,j),rfl⟩⟩)))
  let sN : System (2^(k+1)) (1:N) := {
    entry := fun i j => ⟨(s k).entry i j,hmem i j⟩
    star_entry := fun i j => Subtype.ext ((s k).star_entry i j)
    mul_entry := fun i j a b => by
      apply Subtype.ext
      change (s k).entry i j*(s k).entry a b=(↑(if j=a then (⟨(s k).entry i b,hmem i b⟩:N) else 0):M)
      split <;> simp_all only [(s k).mul_entry,ite_true,ite_false]
      rfl
    sum_diag := by
      apply Subtype.ext
      change (N.subtype (∑ i, (⟨(s k).entry i i,hmem i i⟩:N)))=(1:M)
      rw [map_sum]
      exact (s k).sum_diag }
  exact ⟨sN⟩
end PopaSeparable

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hII : PopaTypeII.NoAbelianCorners M)
include e hτ htr hfaith h1 hII

theorem arbitrary_typeII_last_normal_primitive {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ v, differentialValue f v=0)
    (hn : ∀ a : Fin n → M, HasPreadjoint e (f.curryRight a)) :
    ∃ g : Cochain M n, ‖g‖≤‖f‖ ∧ ∀ v, differentialValue g v=f v := by
  classical
  obtain ⟨hL,hR⟩ := HochschildSakai.abstract_multiplication_normal e
  obtain ⟨P,_,hP⟩ := exists_star_preadjoint e τ hL hτ hfaith htr
  apply primitive_of_finite_exactness e hL hR f ‖f‖ (norm_nonneg _)
  intro E
  let images : Finset M := Finset.univ.image (fun x : Fin (n+1) → E => f (fun i => x i))
  let S : Set M := (E : Set M) ∪ (images : Set M)
  have hS : S.Countable := E.countable_toSet.union images.countable_toSet
  obtain ⟨R,hRcount,hSR,hIIN⟩ := PopaSeparable.typeII_seed
    e τ hτ htr hfaith h1 hL hR P hP hII S hS
  let A := StarAlgebra.adjoin ℂ R
  let N := WeakAlgebra.closure e A hL hR P hP
  let Y := X ⧸ WeakSubspace.preannihilator (WeakAlgebra.linearClosure e A)
  let eN : StrongDual ℂ Y ≃ₗᵢ⋆[ℂ] N := WeakAlgebra.predualEquiv e A hL hR P hP
  let τN : N →ₚ[ℂ] ℂ := WeakAlgebra.inheritedTrace e τ A hL hR P hP
  let : TopologicalSpace.SeparableSpace A := separable_starAdjoin R hRcount
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
    WeakAlgebra.mem_linearClosure e A (StarAlgebra.subset_adjoin ℂ R (hSR ha))
  have hpaths := PopaCenter.produced_finite_paths eN τN hτN htrN hfaithN h1N hIIN
  apply finite_exactness_of_separable_subalgebra e eN τ τN h1N htr htrN hL hLN
    hτ hτN hfaith hfaithN N.subtype (fun _ => rfl) hpaths f hf hn (E : Set M)
  · intro a ha
    exact ⟨⟨a,hmem a (Or.inl ha)⟩,rfl⟩
  · intro x hx
    have hm : f x ∈ images := by
      apply Finset.mem_image.mpr
      exact ⟨fun i => ⟨x i,hx i⟩,Finset.mem_univ _,rfl⟩
    exact ⟨⟨f x,hmem (f x) (Or.inr hm)⟩,rfl⟩

theorem arbitrary_typeII_ordinary_primitive {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ v, differentialValue f v=0) :
    ∃ g : Cochain M n, ‖g‖≤12*‖f‖ ∧ ∀ v, differentialValue g v=f v := by
  obtain ⟨g,hg,hgf⟩ := arbitrary_typeII_last_normal_primitive e τ hτ htr hfaith h1 hII
    (reducedNormalCocycle e f) (reducedNormalCocycle_cocycle e f hf)
    (reducedNormalCocycle_normal e f)
  refine ⟨g+normalCorrection e f, ?_, ?_⟩
  · have hF := reducedNormalCocycle_norm e f
    have hh := normalCorrection_norm e f
    exact (norm_add_le _ _).trans (by linarith)
  · intro v
    rw [differentialValue_add,hgf]
    exact (normal_correction_identity e f hf v).symm
end BoundedHochschild

open scoped ComplexOrder
namespace PopaTypeII
open BoundedHochschild PopaCenter PopaCorner PopaCorners
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def AbelianProjection {p : M} (hp : IsStarProjection p) : Prop :=
  ∀ a b : algebra hp, Commute a b

def TypeICorner {z : M} (_hz : IsStarProjection z) : Prop :=
  ∀ p : M, ∀ _hp : IsStarProjection p, p ≤ z → p ≠ 0 →
    ∃ q : M, ∃ hq : IsStarProjection q, q ≤ p ∧ q ≠ 0 ∧ AbelianProjection hq

def NoTypeICentralPart (M : Type*) [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] : Prop :=
  ∀ z : M, ∀ hz : IsStarProjection z, Central z → z ≠ 0 → ¬ TypeICorner hz

lemma abelian_transfer {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (v : CornerIso p q) (hv : v.final=q) (hab : AbelianProjection hp) :
    AbelianProjection hq := by
  have hvp : (v:M)*p=(v:M) := by
    calc (v:M)*p=((v:M)*v.initial)*p := by rw [v.mul_initial]
         _=(v:M)*(v.initial*p) := mul_assoc _ _ _
         _=(v:M) := by rw [(v.initial_proj.le_iff_mul_eq_left hp).mp v.init_le,v.mul_initial]
  have hpv : p*star (v:M)=star (v:M) := by
    simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hvp
  let F (a : algebra hq) : algebra hp := ⟨star (v:M)*(a:M)*(v:M),by
    constructor
    · rw [←mul_assoc,←mul_assoc,hpv]
    · rw [mul_assoc,mul_assoc,hvp,mul_assoc]⟩
  have hF (a b : algebra hq) : (F a:M)*(F b:M)=star (v:M)*((a:M)*(b:M))*(v:M) := by
    change (star (v:M)*(a:M)*(v:M))*(star (v:M)*(b:M)*(v:M))=_
    have hq' : (v:M)*star (v:M)=q := hv
    calc
      _=(star (v:M)*(a:M))*((v:M)*star (v:M))*(b:M)*(v:M) := by simp only [mul_assoc]
      _=star (v:M)*((a:M)*(b:M))*(v:M) := by rw [hq']; simp only [mul_assoc,b.property.1]
  intro a b
  have hh := congrArg Subtype.val (hab (F a) (F b)).eq
  change (F a:M)*(F b:M)=(F b:M)*(F a:M) at hh
  rw [hF,hF] at hh
  have hback (c : algebra hq) : (v:M)*(star (v:M)*(c:M)*(v:M))*star (v:M)=(c:M) := by
    have hq' : (v:M)*star (v:M)=q := hv
    calc _=((v:M)*star (v:M))*(c:M)*((v:M)*star (v:M)) := by simp only [mul_assoc]
         _=(c:M) := by rw [hq',c.property.1,c.property.2]
  apply Subtype.ext
  exact (hback (a*b)).symm.trans ((congrArg (fun x : M => (v:M)*x*star (v:M)) hh).trans (hback (b*a)))

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include e hτ htr hfaith h1 in

theorem abelian_has_typeI_central_support {p : M} (hp : IsStarProjection p)
    (hp0 : p ≠ 0) (hab : AbelianProjection hp) :
    ∃ z : M, ∃ hz : IsStarProjection z, Central z ∧ z ≠ 0 ∧ TypeICorner hz := by
  obtain ⟨z,hz,hzc,hpz,hann⟩ := exists_central_support e τ hτ htr hfaith h1 hp
  have hz0 : z ≠ 0 := by
    intro he; exact hp0 (le_antisymm (by simpa [he] using hpz) hp.nonneg)
  refine ⟨z,hz,hzc,hz0,?_⟩
  intro r hr hrz hr0
  have hex : ∃ a : M, r*a*p ≠ 0 := by
    by_contra hn
    push Not at hn
    have hh := hann r hn
    rw [(hr.le_iff_mul_eq_left hz).mp hrz] at hh
    exact hr0 hh
  obtain ⟨a,ha⟩ := hex
  obtain ⟨v,s,t,hs,ht,hsp,htr',hvi,hvf,hvs,htv,hvp⟩ := corner_polar e hp hr
    (show (r*a*p)*p=r*a*p by rw [mul_assoc,hp.isIdempotentElem.eq])
    (show r*(r*a*p)=r*a*p by rw [←mul_assoc,←mul_assoc,hr.isIdempotentElem.eq])
  have hv0 : v ≠ 0 := by intro hv; exact ha (by simpa [hv] using hvp)
  have ht0 : t ≠ 0 := by
    intro ht0
    have hh := htv
    rw [ht0,zero_mul] at hh
    exact hv0 hh.symm
  let V : CornerIso p t := ⟨v,by rwa [hvi],by rwa [hvi],by rwa [hvi],by rw [hvf]⟩
  exact ⟨t,ht,htr',ht0,abelian_transfer hp ht V hvf hab⟩

include e hτ htr hfaith h1 in
theorem noTypeICentralPart_iff : NoTypeICentralPart M ↔ NoAbelianCorners M := by
  classical
  constructor
  · intro h p hp hp0
    by_contra hn
    push Not at hn
    have hab : AbelianProjection hp := fun a b => hn a b
    obtain ⟨z,hz,hzc,hz0,hI⟩ := abelian_has_typeI_central_support e τ hτ htr hfaith h1 hp hp0 hab
    exact h z hz hzc hz0 hI
  · intro h z hz hzc hz0 hI
    obtain ⟨q,hq,hqz,hq0,hqa⟩ := hI z hz le_rfl hz0
    obtain ⟨a,b,hab⟩ := h q hq hq0
    exact hab (hqa a b)
end PopaTypeII

open scoped ComplexOrder
namespace BoundedHochschild
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def TracialSeparatelyNormal {n : ℕ} (f : Cochain M n) : Prop :=
  ∀ (v : Fin n → M) (i : Fin n), HasPreadjoint e (f.toContinuousLinearMap v i)

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace X] in
lemma TracialSeparatelyNormal.last {n : ℕ} {f : Cochain M (n+1)}
    (hn : TracialSeparatelyNormal e f) (a : Fin n → M) :
    HasPreadjoint e (f.curryRight a) := by
  have he : f.curryRight a=f.toContinuousLinearMap (Fin.snoc a 0) (Fin.last n) := by
    ext x
    simp only [ContinuousMultilinearMap.curryRight_apply,
      ContinuousMultilinearMap.toContinuousLinearMap_apply]
    congr 1
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp
  rw [he]
  exact hn _ _

variable (τ : M →ₚ[ℂ] ℂ) (hτ : TraceInPredual e τ)
  (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hII : PopaTypeII.NoTypeICentralPart M)
include e τ hτ htr hfaith h1 hII

theorem source_tracial_primitive {n : ℕ} (f : Cochain M (n+2))
    (hf : ∀ v, differentialValue f v=0) (hn : TracialSeparatelyNormal e f) :
    ∃ g : Cochain M (n+1), ‖g‖≤‖f‖ ∧ ∀ v, differentialValue g v=f v := by
  exact arbitrary_typeII_last_normal_primitive e τ hτ htr hfaith h1
    ((PopaTypeII.noTypeICentralPart_iff e τ hτ htr hfaith h1).mp hII)
    f hf (hn.last e)

theorem source_tracial_ordinary_primitive {n : ℕ} (f : Cochain M (n+2))
    (hf : ∀ v, differentialValue f v=0) :
    ∃ g : Cochain M (n+1), ‖g‖≤12*‖f‖ ∧ ∀ v, differentialValue g v=f v := by
  exact arbitrary_typeII_ordinary_primitive e τ hτ htr hfaith h1
    ((PopaTypeII.noTypeICentralPart_iff e τ hτ htr hfaith h1).mp hII) f hf
end BoundedHochschild

end

end OAI
