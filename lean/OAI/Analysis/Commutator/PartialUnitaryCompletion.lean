import Mathlib
import OAI.Analysis.Commutator.PartialUnitaryOrder
import OAI.Analysis.Commutator.VonNeumannCStar

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching.PartialUnitary

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def ofUnitary (u : unitary A) : PartialUnitary A where
  val := u
  support := 1
  projection := IsStarProjection.one A
  star_mul := u.property.1
  mul_star := u.property.2
  mul_support := mul_one _
  support_mul := one_mul _

def complement (v : PartialUnitary A) : PartialUnitary A where
  val := 1-v.support
  support := 1-v.support
  projection := v.projection.one_sub
  star_mul := by rw [v.projection.one_sub.isSelfAdjoint.star_eq]; exact v.projection.one_sub.isIdempotentElem.eq
  mul_star := by rw [v.projection.one_sub.isSelfAdjoint.star_eq]; exact v.projection.one_sub.isIdempotentElem.eq
  mul_support := v.projection.one_sub.isIdempotentElem.eq
  support_mul := v.projection.one_sub.isIdempotentElem.eq

omit [PartialOrder A] [StarOrderedRing A] in
lemma support_complement_zero (v : PartialUnitary A) : v.support*v.complement.support=0 := by
  change v.support*(1-v.support)=0
  rw [mul_sub,mul_one,v.projection.isIdempotentElem.eq,sub_self]

def completed (v : PartialUnitary A) : PartialUnitary A := v.add v.complement v.support_complement_zero

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma completed_val (v : PartialUnitary A) : v.completed.val=v.val+(1-v.support) := rfl

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma completed_support (v : PartialUnitary A) : v.completed.support=1 := by
  change v.support+(1-v.support)=1
  abel

lemma le_completed (v : PartialUnitary A) : v ≤ v.completed := v.le_add _ _

def completion (v : PartialUnitary A) : unitary A :=
  ⟨v.completed.val,by constructor <;> simp only [v.completed.star_mul,v.completed.mul_star,completed_support]⟩

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma completion_val (v : PartialUnitary A) : (v.completion:A)=v.val+(1-v.support) := rfl

omit [PartialOrder A] [StarOrderedRing A] in
lemma ofUnitary_completion (v : PartialUnitary A) : ofUnitary v.completion=v.completed := by
  apply ext
  rfl

lemma completion_norm_sub (τ : A →ₚ[ℂ] ℂ) (hone : τ 1=1) (v : PartialUnitary A) :
    TracialL2.norm τ (v.completed.val-v.val)=Real.sqrt (1-(τ v.support).re) := by
  have hh := norm_sub_sq τ v.le_completed
  rw [completed_support,hone,Complex.one_re] at hh
  rw [←hh,Real.sqrt_sq (TracialL2.norm_nonneg τ _)]

lemma completed_mem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M R : VonNeumannAlgebra H) (v : PartialUnitary M) (hv : (v.val : H →L[ℂ] H)∈R) :
    (v.completed.val : H →L[ℂ] H)∈R := by
  have hs : (v.support : H →L[ℂ] H)∈R := by
    rw [←v.star_mul]
    exact R.mul_mem (R.star_mem' hv) hv
  exact R.add_mem hv (R.sub_mem R.one_mem hs)

end Kadison.FinitePatching.PartialUnitary

end

end
end

end OAI
