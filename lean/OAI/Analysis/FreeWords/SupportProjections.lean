import Mathlib
import OAI.Analysis.FreeWords.FactorBase
import OAI.Analysis.FreeWords.PolarBounds

namespace OAI

noncomputable section

namespace KKSpectralSupport

open KKTraceTransfer KKPolarSupport

open scoped InnerProductSpace ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def rangeProjection (a : H →L[ℂ] H) : H →L[ℂ] H := (closedRange a).starProjection

theorem rangeProjection_isProjection (a : H →L[ℂ] H) : IsStarProjection (rangeProjection a) :=
  isStarProjection_starProjection

theorem rangeProjection_mul (a : H →L[ℂ] H) : rangeProjection a*a=a := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr (Submodule.le_topologicalClosure _ ⟨x,rfl⟩)

theorem mul_rangeProjection {a : H →L[ℂ] H} (ha : IsSelfAdjoint a) : a*rangeProjection a=a := by
  simpa only [star_mul,ha.star_eq,(rangeProjection_isProjection a).isSelfAdjoint.star_eq]
    using congrArg star (rangeProjection_mul a)

theorem annihilate_rangeProjection {a b : H →L[ℂ] H} (hab : b*a=0) : b*rangeProjection a=0 := by
  have hb : ∀ z : closedRange a, b z=0 := by
    intro z
    refine (closedRangeMap_dense a).induction_on (p := fun z => b z=0) z ?_ ?_
    · exact isClosed_eq (by fun_prop) continuous_const
    · intro x
      exact congrArg (fun T : H →L[ℂ] H => T x) hab
  ext x
  exact hb ((closedRange a).orthogonalProjectionOnto x)

theorem rangeProjection_commute {a b : H →L[ℂ] H}
    (hba : Commute b a) (hbsa : Commute (star b) a) : Commute b (rangeProjection a) :=
  UniversalStrongKK.commute_projection_of_invariant _ _
    (closedRange_invariant a b hba) (closedRange_invariant a (star b) hbsa)

theorem rangeProjection_mem (M : VonNeumannAlgebra H) {a : H →L[ℂ] H} (ha : a ∈ M) :
    rangeProjection a ∈ M := by
  rw [← M.commutant_commutant,VonNeumannAlgebra.mem_commutant_iff]
  intro b hb
  exact (rangeProjection_commute
    (VonNeumannAlgebra.mem_commutant_iff.mp hb a ha).symm
    (VonNeumannAlgebra.mem_commutant_iff.mp (star_mem hb) a ha).symm).eq

local instance supportConcreteOrder (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) :=
  concreteOrder M

local instance supportConcretePreorder (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) :=
  (concreteOrder M).toPreorder

local instance supportConcreteLE (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) :=
  (concreteOrder M).toLE

local instance supportConcreteSOR (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) :=
  concreteSOR M

variable {M : VonNeumannAlgebra H}

def supportProjection (a : ConcreteAlgebra M) : ConcreteAlgebra M :=
  ⟨rangeProjection (a : H →L[ℂ] H),rangeProjection_mem M a.property⟩

theorem supportProjection_isProjection (a : ConcreteAlgebra M) : IsStarProjection (supportProjection a) := by
  constructor
  · exact Subtype.ext (rangeProjection_isProjection (a : H →L[ℂ] H)).isIdempotentElem.eq
  · exact Subtype.ext (rangeProjection_isProjection (a : H →L[ℂ] H)).isSelfAdjoint.star_eq

theorem supportProjection_mul (a : ConcreteAlgebra M) : supportProjection a*a=a :=
  Subtype.ext (rangeProjection_mul (a : H →L[ℂ] H))

theorem mul_supportProjection {a : ConcreteAlgebra M} (ha : IsSelfAdjoint a) :
    a*supportProjection a=a := by
  simpa only [star_mul,ha.star_eq,(supportProjection_isProjection a).isSelfAdjoint.star_eq]
    using congrArg star (supportProjection_mul a)

theorem annihilate_supportProjection {a b : ConcreteAlgebra M} (hab : b*a=0) :
    b*supportProjection a=0 := Subtype.ext (annihilate_rangeProjection (congrArg Subtype.val hab))

theorem supportProjection_commute {a b : ConcreteAlgebra M} (ha : IsSelfAdjoint a)
    (hba : Commute b a) : Commute b (supportProjection a) := by
  have hbsa : Commute (star b) a := by simpa only [ha.star_eq] using hba.star_star
  exact Subtype.ext (rangeProjection_commute (congrArg Subtype.val hba.eq)
    (congrArg Subtype.val hbsa.eq)).eq

@[simp] theorem supportProjection_zero : supportProjection (0 : ConcreteAlgebra M)=0 := by
  have h := annihilate_supportProjection (a := (0 : ConcreteAlgebra M)) (b := 1) (mul_zero 1)
  simpa only [one_mul] using h

@[simp] theorem supportProjection_one : supportProjection (1 : ConcreteAlgebra M)=1 := by
  simpa only [mul_one] using supportProjection_mul (1 : ConcreteAlgebra M)

theorem supportProjection_le {a : ConcreteAlgebra M} {p : ConcreteAlgebra M}
    (hp : IsStarProjection p) (hpa : p*a=a) : supportProjection a ≤ p := by
  have h : (1-p)*a=0 := by rw [sub_mul,one_mul,hpa,sub_self]
  have hh := annihilate_supportProjection h
  rw [sub_mul,one_mul] at hh
  exact ((supportProjection_isProjection a).le_iff_mul_eq_right hp).mpr (sub_eq_zero.mp hh).symm

end

end KKSpectralSupport
end

end OAI
