import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.FactorPrimitive
import OAI.Analysis.BoundedHochschild.TypeIICorners
import OAI.Analysis.BoundedHochschild.CenterPowers

namespace OAI

/-! Central atoms and their factor corners. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace HochschildAtomic
open BoundedHochschild BoundedHochschild.WeakAlgebra HochschildSakai
open HochschildCorners HochschildMatrixSystems.MatrixSystem
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def center : StarSubalgebra ℂ M where
  carrier := {a | ∀ b : M, Commute a b}
  zero_mem' := fun _ => Commute.zero_left _
  one_mem' := fun _ => Commute.one_left _
  add_mem' := fun ha hb x => (ha x).add_left (hb x)
  mul_mem' := fun ha hb x => (ha x).mul_left (hb x)
  algebraMap_mem' c := fun x => Algebra.commutes c x
  star_mem' := fun ha x => by
    have h := congrArg star (ha (star x)).eq
    change star _*x=x*star _
    simpa only [star_mul,star_star] using h.symm

instance center_closed : IsClosed (center (M:=M) : Set M) := by
  change IsClosed {a : M | ∀ b : M, a*b=b*a}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun b => isClosed_eq
    (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma centerClosure_eq
    (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z))) :
    WeakAlgebra.closure e center (mul_hasPreadjoint e) (mul_right_hasPreadjoint e) P hP=center := by
  apply le_antisymm
  · intro x hx b
    have hclosed : IsClosed {f : WeakDual ℂ X |
        (weakEquiv e).symm (b*weakEquiv e f) = (weakEquiv e).symm (weakEquiv e f*b)} :=
      isClosed_eq (normal_continuous e _ (mul_hasPreadjoint e b))
        (normal_continuous e _ (mul_right_hasPreadjoint e b))
    have hs : (linearClosure e center : Set (WeakDual ℂ X)) ⊆
        {f | (weakEquiv e).symm (b*weakEquiv e f) = (weakEquiv e).symm (weakEquiv e f*b)} := by
      apply closure_minimal _ hclosed
      rintro f ⟨a,ha,rfl⟩
      change (weakEquiv e).symm (b*weakEquiv e ((weakEquiv e).symm a)) =
        (weakEquiv e).symm (weakEquiv e ((weakEquiv e).symm a)*b)
      simpa only [LinearEquiv.apply_symm_apply] using congrArg (weakEquiv e).symm (ha b).eq.symm
    have hh := (weakEquiv e).symm.injective (hs hx)
    change x*b=b*x
    simpa only [LinearEquiv.apply_symm_apply] using hh.symm
  · intro x hx
    exact mem_linearClosure e center hx

def CenterPredual := X ⧸ WeakSubspace.preannihilator (linearClosure e center)
instance : NormedAddCommGroup (CenterPredual e) := inferInstanceAs
  (NormedAddCommGroup (X ⧸ WeakSubspace.preannihilator (linearClosure e center)))
instance : NormedSpace ℂ (CenterPredual e) := inferInstanceAs
  (NormedSpace ℂ (X ⧸ WeakSubspace.preannihilator (linearClosure e center)))
instance : CompleteSpace (CenterPredual e) := inferInstanceAs
  (CompleteSpace (X ⧸ WeakSubspace.preannihilator (linearClosure e center)))

def centerPredualEquiv : StrongDual ℂ (CenterPredual e) ≃ₗᵢ⋆[ℂ] (center (M:=M)) := by
  let H := exists_abstract_star_preadjoint e
  let P := Classical.choose H
  have hP := (Classical.choose_spec H).2
  exact (predualEquiv e center (mul_hasPreadjoint e) (mul_right_hasPreadjoint e) P hP).trans
    (subalgebraIsoOfEq _ _ (centerClosure_eq e P hP))

include e in

theorem scalar_center_of_projections
    (hp : ∀ p : M, IsStarProjection p → (∀ b : M, Commute p b) → p=0 ∨ p=1) :
    ∀ a : M, (∀ b : M, Commute a b) → ∃ c : ℂ, a=c • (1:M) := by
  intro a ha
  let Z := center (M:=M)
  let S : Submodule ℂ Z := Submodule.span ℂ {(1:Z)}
  have hfinite : FiniteDimensional ℂ S := FiniteDimensional.span_singleton ℂ (1:Z)
  let := hfinite
  have hclosed : IsClosed (S : Set Z) := Submodule.closed_of_finiteDimensional S
  have hpro : Submodule.span ℂ {p : Z | IsStarProjection p} ≤ S := by
    apply Submodule.span_le.mpr
    intro p hpZ
    have hpM : IsStarProjection (p:M) := ⟨congrArg (fun z : Z => (z:M)) hpZ.isIdempotentElem.eq,
      congrArg (fun z : Z => (z:M)) hpZ.isSelfAdjoint.star_eq⟩
    rcases hp p hpM p.property with hz | ho
    · have he : p=0 := Subtype.ext hz
      rw [he]; exact S.zero_mem
    · have he : p=1 := Subtype.ext ho
      rw [he]; exact Submodule.subset_span (Set.mem_singleton _)
  have hall : (⊤ : Submodule ℂ Z) ≤ S := by
    rw [← projection_span_dense (centerPredualEquiv e)]
    exact Submodule.topologicalClosure_minimal _ hpro hclosed
  have had : (⟨a,ha⟩ : Z) ∈ S := hall (Submodule.mem_top)
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp had
  exact ⟨c,(congrArg (fun z : Z => (z:M)) hc).symm⟩

def CentralAtom (p : M) : Prop :=
  IsStarProjection p ∧ (∀ b : M, Commute p b) ∧ p ≠ 0 ∧
    ∀ q : M, IsStarProjection q → (∀ b : M, Commute q b) → q ≤ p → q=0 ∨ q=p

omit [PartialOrder M] [StarOrderedRing M] in
lemma corner_central_coe {p : M} (hp : IsStarProjection p)
    (hpc : ∀ b : M, Commute p b) (a : Corner p hp)
    (ha : ∀ b : Corner p hp, Commute a b) : ∀ b : M, Commute (a:M) b := by
  intro b
  have he := congrArg (fun z : Corner p hp => (z:M))
    (ha ⟨p*b*p,compress_mem_corner hp b⟩).eq
  change (a:M)*(p*b*p)=(p*b*p)*(a:M) at he
  have hl : (a:M)*(p*b*p)=(a:M)*b := by
    rw [← mul_assoc,← mul_assoc,a.property.2,mul_assoc,← (hpc b).eq,
      ← mul_assoc,a.property.2]
  have hr : (p*b*p)*(a:M)=b*(a:M) := by
    rw [mul_assoc,a.property.1,(hpc b).eq,mul_assoc,a.property.1]
  change (a:M)*b=b*(a:M)
  exact hl.symm.trans (he.trans hr)

include e in
theorem central_atom_corner_factor {p : M} (hp : CentralAtom p) :
    ∀ a : Corner p hp.1, (∀ b : Corner p hp.1, Commute a b) →
      ∃ c : ℂ, a=c • (1 : Corner p hp.1) := by
  apply scalar_center_of_projections (cornerPredualEquiv p hp.1 e)
  intro q hq hqc
  rcases hp.2.2.2 q (corner_projection_coe p hp.1 hq)
    (corner_central_coe hp.1 hp.2.1 q hqc) (corner_projection_le p hp.1 hq) with h0 | h1
  · exact Or.inl (Subtype.ext h0)
  · exact Or.inr (Subtype.ext h1)

end HochschildAtomic

end

end OAI
