import Mathlib
import OAI.Analysis.BoundedHochschild.MatrixSystems
import OAI.Analysis.BoundedHochschild.NormalVectors
import OAI.Analysis.BoundedHochschild.WeakAlgebras

namespace OAI

/-! Matrix coefficients, commutant algebras and their preduals. -/

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
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder
namespace HochschildMatrixSystems
namespace MatrixSystem
variable {M : Type*} [CStarAlgebra M]
variable {n : ℕ} (E : MatrixSystem M n)

 
def commutant : StarSubalgebra ℂ M where
  carrier := {x | ∀ i j, Commute x (E.entry i j)}
  zero_mem' := fun i j => Commute.zero_left _
  one_mem' := fun i j => Commute.one_left _
  add_mem' := fun hx hy i j => (hx i j).add_left (hy i j)
  mul_mem' := fun hx hy i j => (hx i j).mul_left (hy i j)
  algebraMap_mem' c := fun i j => Algebra.commutes c (E.entry i j)
  star_mem' := fun hx i j => by
    have hh := congrArg star (hx j i).eq
    change _ * _ = _ * _
    simpa only [star_mul,E.star_entry] using hh.symm

lemma mem_commutant {x : M} : x ∈ E.commutant ↔ ∀ i j, Commute x (E.entry i j) := Iff.rfl

instance commutant_closed : IsClosed (E.commutant : Set M) := by
  change IsClosed {x : M | ∀ i j, x*E.entry i j = E.entry i j*x}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)

 
def coefficient (i j : Fin n) (x : M) : M := ∑ k, E.entry k i*x*E.entry j k

lemma entry_mul_coefficient (a b i j : Fin n) (x : M) :
    E.entry a b*E.coefficient i j x=E.entry a i*x*E.entry j b := by
  classical
  simp only [coefficient,Finset.mul_sum,← mul_assoc,E.entry_mul,ite_mul,zero_mul]
  simp

lemma coefficient_mul_entry (a b i j : Fin n) (x : M) :
    E.coefficient i j x*E.entry a b=E.entry a i*x*E.entry j b := by
  classical
  simp only [coefficient,Finset.sum_mul,mul_assoc,E.entry_mul,mul_ite,mul_zero]
  simp [← mul_assoc]

lemma coefficient_mem (i j : Fin n) (x : M) : E.coefficient i j x ∈ E.commutant := by
  intro a b
  exact (E.coefficient_mul_entry a b i j x).trans (E.entry_mul_coefficient a b i j x).symm

lemma reconstruct (x : M) : ∑ i, ∑ j, E.entry i j*E.coefficient i j x=x := by
  simp only [E.entry_mul_coefficient,← Finset.mul_sum,← Finset.sum_mul,E.sum_diagonal,one_mul,mul_one]

lemma factor_of_commutant (A : StarSubalgebra ℂ M) (hA : A=E.commutant)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M)) :
    ∀ b : A, (∀ x : A, Commute b x) → ∃ c : ℂ, b=c • (1 : A) := by
  subst A
  intro b hb
  have hc : ∀ x : M, Commute (b:M) x := by
    intro x
    rw [← E.reconstruct x]
    apply Commute.sum_right
    intro i hi
    apply Commute.sum_right
    intro j hj
    exact (b.property i j).mul_right (show Commute (b:M) (E.coefficient i j x) from
      congrArg (fun z : E.commutant => (z:M)) (hb ⟨_,E.coefficient_mem i j x⟩).eq)
  obtain ⟨c,hc⟩ := hfactor b hc
  exact ⟨c,Subtype.ext hc⟩

lemma coefficient_star (i j : Fin n) (x : M) :
    star (E.coefficient i j x)=E.coefficient j i (star x) := by
  simp only [coefficient,star_sum,star_mul,E.star_entry,mul_assoc]

lemma coefficient_nil (i j : Fin n) : E.coefficient i j (0:M)=0 := by
  simp [coefficient]

lemma coefficient_diagonal_base (i : Fin n) : E.coefficient i i (E.entry i i)=1 := by
  simp only [coefficient,E.entry_mul,ite_true,E.sum_diagonal]

lemma coefficient_corner (i : Fin n) (x : M) :
    E.entry i i*E.coefficient i i x*E.entry i i = E.entry i i*x*E.entry i i := by
  rw [E.entry_mul_coefficient,mul_assoc,E.entry_mul,ite_eq_left rfl]

lemma coefficient_mul (i : Fin n) (x y : M) :
    E.coefficient i i x*E.coefficient i i y = E.coefficient i i (x*E.entry i i*y) := by
  classical
  simp only [coefficient,Finset.sum_mul,Finset.mul_sum]
  congr 1
  ext j
  have hterm (k : Fin n) :
      (E.entry k i*x*E.entry i k)*(E.entry j i*y*E.entry i j)=
        if k=j then E.entry j i*(x*E.entry i i*y)*E.entry i j else 0 := by
    by_cases h : k=j
    · subst k
      rw [ite_eq_left rfl]
      calc
        (E.entry j i*x*E.entry i j)*(E.entry j i*y*E.entry i j) =
            E.entry j i*x*(E.entry i j*E.entry j i)*y*E.entry i j := by noncomm_ring
        _ = _ := by rw [E.entry_mul,ite_eq_left rfl]; noncomm_ring
    · rw [ite_eq_right h]
      calc
        (E.entry k i*x*E.entry i k)*(E.entry j i*y*E.entry i j) =
            E.entry k i*x*(E.entry i k*E.entry j i)*y*E.entry i j := by noncomm_ring
        _ = 0 := by rw [E.entry_mul,ite_eq_right h,mul_zero,zero_mul,zero_mul]
  simp only [hterm]
  simp

lemma diagonal_proj (i : Fin n) : IsStarProjection (E.entry i i) := by
  exact ⟨by change E.entry i i*E.entry i i=E.entry i i; rw [E.entry_mul,ite_eq_left rfl],
    by change star (E.entry i i)=E.entry i i; exact E.star_entry i i⟩

variable [PartialOrder M] [StarOrderedRing M]

lemma inflate_projection (i : Fin n) {p : M} (hp : IsStarProjection p)
    (hle : p ≤ E.entry i i) : IsStarProjection (E.coefficient i i p) := by
  refine ⟨?_,?_⟩
  · change E.coefficient i i p*E.coefficient i i p=E.coefficient i i p
    rw [E.coefficient_mul,(hp.le_iff_mul_eq_left (E.diagonal_proj i)).mp hle,hp.isIdempotentElem.eq]
  · change star (E.coefficient i i p)=E.coefficient i i p
    rw [E.coefficient_star,hp.isSelfAdjoint.star_eq]

lemma coefficient_recover (i : Fin n) {p : M} (hp : IsStarProjection p)
    (hle : p ≤ E.entry i i) :
    E.entry i i*E.coefficient i i p*E.entry i i=p := by
  rw [E.coefficient_corner,(hp.le_iff_mul_eq_right (E.diagonal_proj i)).mp hle,
    (hp.le_iff_mul_eq_left (E.diagonal_proj i)).mp hle]

omit [PartialOrder M] [StarOrderedRing M] in
lemma coefficient_of_commutant (i : Fin n) {x : M} (hx : x ∈ E.commutant) :
    E.coefficient i i (E.entry i i*x)=x := by
  classical
  calc
    E.coefficient i i (E.entry i i*x) = ∑ k, (E.entry k k)*x := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        E.entry k i*(E.entry i i*x)*E.entry i k = (E.entry k i*E.entry i i)*(x*E.entry i k) := by
          noncomm_ring
        _ = (E.entry k i*E.entry i i)*(E.entry i k*x) := by rw [(hx i k).eq]
        _ = E.entry k k*x := by rw [E.entry_mul,ite_eq_left rfl,← mul_assoc,E.entry_mul,ite_eq_left rfl]
    _ = x := by rw [← Finset.sum_mul,E.sum_diagonal,one_mul]

end MatrixSystem
end HochschildMatrixSystems

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildMatrixSystems
namespace MatrixSystem
open BoundedHochschild
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n : ℕ} (E : MatrixSystem M n)

lemma commutant_no_minimal (i : Fin n) (hdiff : HochschildDiffuse.NoMinimalProjections M) :
    HochschildDiffuse.NoMinimalProjections E.commutant := by
  intro q hq hq0
  have hqM : IsStarProjection (q:M) :=
    ⟨congrArg (fun z : E.commutant => (z:M)) hq.isIdempotentElem.eq,
      congrArg (fun z : E.commutant => (z:M)) hq.isSelfAdjoint.star_eq⟩
  let p := E.entry i i*(q:M)
  have hp : IsStarProjection p := (E.diagonal_proj i).mul hqM (q.property i i).symm
  have hpe : p ≤ E.entry i i := (hp.le_iff_mul_eq_right (E.diagonal_proj i)).mpr
    (by dsimp [p]; rw [← mul_assoc,(E.diagonal_proj i).isIdempotentElem.eq])
  have hp0 : p ≠ 0 := by
    intro hz
    have hh := E.coefficient_of_commutant i q.property
    change E.coefficient i i p=(q:M) at hh
    rw [hz,E.coefficient_nil] at hh
    exact hq0 (Subtype.ext hh.symm)
  obtain ⟨r,hr,hrp,hr0,hrne⟩ := hdiff p hp hp0
  have hre := hrp.trans hpe
  have hs := E.inflate_projection i hr hre
  let s : E.commutant := ⟨E.coefficient i i r,E.coefficient_mem i i r⟩
  have hsN : IsStarProjection s := ⟨Subtype.ext hs.isIdempotentElem.eq,
    Subtype.ext hs.isSelfAdjoint.star_eq⟩
  refine ⟨s,hsN,?_,?_,?_⟩
  · apply (hsN.le_iff_mul_eq_left hq).mpr
    apply Subtype.ext
    change E.coefficient i i r*(q:M)=E.coefficient i i r
    rw [← E.coefficient_of_commutant i q.property,E.coefficient_mul]
    congr 1
    rw [(hr.le_iff_mul_eq_left (E.diagonal_proj i)).mp hre]
    exact (hr.le_iff_mul_eq_left hp).mp hrp
  · intro hz
    have hzM : E.coefficient i i r=0 := congrArg (fun x : E.commutant => (x:M)) hz
    have hh := E.coefficient_recover i hr hre
    rw [hzM,mul_zero,zero_mul] at hh
    exact hr0 hh.symm
  · intro he
    have heM : E.coefficient i i r=(q:M) := congrArg (fun x : E.commutant => (x:M)) he
    have hh := E.coefficient_recover i hr hre
    rw [heM,mul_assoc, (q.property i i).eq,← mul_assoc,(E.diagonal_proj i).isIdempotentElem.eq] at hh
    exact hrne hh.symm

end MatrixSystem

universe u
namespace MatrixSystem
open BoundedHochschild BoundedHochschild.WeakAlgebra
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {n : ℕ} (E : MatrixSystem M n)
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
  (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
  (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
  (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))

lemma commutantClosure_eq : WeakAlgebra.closure e E.commutant hL hR P hP=E.commutant := by
  apply le_antisymm
  · intro x hx i j
    have hclosed : IsClosed {f : WeakDual ℂ X |
        (weakEquiv e).symm (E.entry i j*weakEquiv e f)=
        (weakEquiv e).symm (weakEquiv e f*E.entry i j)} :=
      isClosed_eq (normal_continuous e _ (hL _)) (normal_continuous e _ (hR _))
    have hs : (linearClosure e E.commutant : Set (WeakDual ℂ X)) ⊆
        {f | (weakEquiv e).symm (E.entry i j*weakEquiv e f)=
             (weakEquiv e).symm (weakEquiv e f*E.entry i j)} := by
      apply closure_minimal _ hclosed
      rintro f ⟨a,ha,rfl⟩
      change (weakEquiv e).symm (E.entry i j*weakEquiv e ((weakEquiv e).symm a)) =
        (weakEquiv e).symm (weakEquiv e ((weakEquiv e).symm a)*E.entry i j)
      simpa only [LinearEquiv.apply_symm_apply] using congrArg (weakEquiv e).symm (ha i j).eq.symm
    have hh := (weakEquiv e).symm.injective (hs hx)
    change x*E.entry i j=E.entry i j*x
    simpa only [LinearEquiv.apply_symm_apply] using hh.symm
  · intro x hx
    exact mem_linearClosure e E.commutant hx

def commutantPredual := X ⧸ WeakSubspace.preannihilator (linearClosure e E.commutant)
instance : NormedAddCommGroup (E.commutantPredual e) := inferInstanceAs
  (NormedAddCommGroup (X ⧸ WeakSubspace.preannihilator (linearClosure e E.commutant)))
instance : NormedSpace ℂ (E.commutantPredual e) := inferInstanceAs
  (NormedSpace ℂ (X ⧸ WeakSubspace.preannihilator (linearClosure e E.commutant)))
instance [CompleteSpace X] : CompleteSpace (E.commutantPredual e) := inferInstanceAs
  (CompleteSpace (X ⧸ WeakSubspace.preannihilator (linearClosure e E.commutant)))

def subalgebraIsoOfEq (A B : StarSubalgebra ℂ M) (h : A=B) : A ≃ₗᵢ[ℂ] B := by
  subst B
  exact LinearIsometryEquiv.refl ℂ A

def commutantPredualEquiv : StrongDual ℂ (E.commutantPredual e) ≃ₗᵢ⋆[ℂ] E.commutant :=
  (predualEquiv e E.commutant hL hR P hP).trans
    (subalgebraIsoOfEq _ _ (E.commutantClosure_eq e hL hR P hP))

lemma subalgebraIsoOfEq_coe (A B : StarSubalgebra ℂ M) (h : A=B) (a : A) :
    (subalgebraIsoOfEq A B h a : M)=(a:M) := by
  subst B
  rfl

lemma subalgebraIsoOfEq_symm_coe (A B : StarSubalgebra ℂ M) (h : A=B) (a : B) :
    ((subalgebraIsoOfEq A B h).symm a : M)=(a:M) := by
  subst B
  rfl

lemma commutantPredualEquiv_symm_mk (a : E.commutant) (z : X) :
    (E.commutantPredualEquiv e hL hR P hP).symm a (Submodule.Quotient.mk z)=
      e.symm (a:M) z := by
  change (predualEquiv e E.commutant hL hR P hP).symm
    ((subalgebraIsoOfEq _ _ (E.commutantClosure_eq e hL hR P hP)).symm a)
    (Submodule.Quotient.mk z)=_
  rw [predualEquiv_symm_apply_mk,subalgebraIsoOfEq_symm_coe]

variable [PartialOrder M]

def commutantTrace (τ : M →ₚ[ℂ] ℂ) : E.commutant →ₚ[ℂ] ℂ where
  toLinearMap := τ.toLinearMap.comp E.commutant.subtype.toLinearMap
  monotone' := fun _ _ h => τ.monotone h

lemma commutantTrace_normal (τ : M →ₚ[ℂ] ℂ) (hτ : TraceInPredual e τ) :
    TraceInPredual (E.commutantPredualEquiv e hL hR P hP) (E.commutantTrace τ) := by
  obtain ⟨z,hz⟩ := hτ
  refine ⟨Submodule.Quotient.mk z,fun a => ?_⟩
  rw [E.commutantPredualEquiv_symm_mk]
  exact hz a.val

lemma commutantTrace_one (τ : M →ₚ[ℂ] ℂ) (h1 : τ 1=1) : E.commutantTrace τ 1=1 := h1
lemma commutantTrace_tracial (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (a b : E.commutant) : E.commutantTrace τ (a*b)=E.commutantTrace τ (b*a) := htr a.val b.val
lemma commutantTrace_faithful (τ : M →ₚ[ℂ] ℂ) (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (a : E.commutant) (ha : E.commutantTrace τ (star a*a)=0) : a=0 :=
  Subtype.ext (hfaith a.val ha)

end MatrixSystem
end HochschildMatrixSystems
end

end OAI
