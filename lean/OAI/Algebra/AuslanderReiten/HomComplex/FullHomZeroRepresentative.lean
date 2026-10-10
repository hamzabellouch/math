import OAI.Algebra.AuslanderReiten.HomComplex.FullHomMapLinear
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomShiftedIdentity
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomHomotopyMaps

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
namespace ArExplicit
universe u v w
variable {C : Type w} [Category.{v} C] [Preadditive C]
variable {K L : CochainComplex C ℤ}

def fullHomZeroRepresentative (x : CohomologyClass K L 0) : K ⟶ L :=
  Cocycle.homOf (Classical.choose (CohomologyClass.mk_surjective x))

@[simp] theorem fullHomZeroRepresentative_class (x : CohomologyClass K L 0) :
    CohomologyClass.mk (Cocycle.ofHom (fullHomZeroRepresentative x)) = x := by
  rw [fullHomZeroRepresentative, Cocycle.ofHom_homOf_eq_self]
  exact Classical.choose_spec (CohomologyClass.mk_surjective x)

variable (k : Type u) [CommRing k] [Linear k C]

include k in
theorem fullHomZero_class_eq_iff (f g : K ⟶ L) :
    CohomologyClass.mk (Cocycle.ofHom f) = CohomologyClass.mk (Cocycle.ofHom g) ↔
      (HomotopyCategory.quotient C _).map f = (HomotopyCategory.quotient C _).map g := by
  constructor
  · intro h
    rw [← fullHomPrecomp_identity f, ← fullHomPrecomp_identity g] at h
    have hh := congrArg (fullHomShiftedHomotopyEquiv k K L 0) h
    rw [fullHomShiftedHomotopyEquiv_precomp, fullHomShiftedHomotopyEquiv_precomp] at hh
    change _ ≫ fullHomShiftedHomotopyEquiv k L L 0 (CompleteComparison.fullHomIdentity L) =
      _ ≫ fullHomShiftedHomotopyEquiv k L L 0 (CompleteComparison.fullHomIdentity L) at hh
    rw [fullHomShiftedHomotopyEquiv_identity] at hh
    exact (cancel_mono _).1 hh
  · intro h
    rw [← fullHomPrecomp_identity f, ← fullHomPrecomp_identity g]
    exact fullHomPrecomp_congr k 0 h _

end ArExplicit

end

end OAI
