import OAI.Algebra.AuslanderReiten.HomComplex.FullHomHomotopyMaps

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
namespace ArExplicit
universe u v w
variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable {K L M N P : CochainComplex C ℤ}
variable {a : L ⟶ M} {b : M ⟶ N} {c : L ⟶ P} {d : P ⟶ N}
include k

theorem fullHomPostcomp_square (n : ℤ)
    (h : (HomotopyCategory.quotient C _).map (a ≫ b) =
      (HomotopyCategory.quotient C _).map (c ≫ d))
    (x : CohomologyClass K L n) :
    fullHomPostcomp b n (fullHomPostcomp a n x) =
      fullHomPostcomp d n (fullHomPostcomp c n x) := by
  rw [fullHomPostcomp_comp, fullHomPostcomp_comp]
  exact fullHomPostcomp_congr k n h x

end ArExplicit

end

end OAI
