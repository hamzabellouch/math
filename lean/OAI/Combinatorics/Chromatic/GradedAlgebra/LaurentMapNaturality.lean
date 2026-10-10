import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentInfinity

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
variable {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
lemma mapRing_square (f : A →+* B) (g : C →+* D) (p : A →+* C) (q : B →+* D)
    (h : ∀ x,q (f x)=g (p x)) (x : LaurentSeries A) :
    mapRing q (mapRing f x)=mapRing g (mapRing p x) := by
  apply HahnSeries.ext
  funext k
  exact h (x.coeff k)
lemma mapUnit_square (f : A →+* B) (g : C →+* D) (p : A →+* C) (q : B →+* D)
    (h : ∀ x,q (f x)=g (p x)) (x : (LaurentSeries A)ˣ) :
    Units.map (mapRing q).toMonoidHom (Units.map (mapRing f).toMonoidHom x)=
      Units.map (mapRing g).toMonoidHom (Units.map (mapRing p).toMonoidHom x) := by
  apply Units.ext
  exact mapRing_square f g p q h x.val
end ElementaryPositivity.LaurentAtInfinity

end

end OAI
