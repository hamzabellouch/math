import Mathlib
import OAI.Combinatorics.Chromatic.Walls.CenterLineSpecialization

namespace OAI

section
namespace ElementaryPositivity.CenterCalculus
open MvPolynomial
variable {A B σ : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
lemma lineSpecialization_map (v h : σ → ℚ) (f : A →ₐ[ℚ] B) (p : MvPolynomial σ A) :
    lineSpecialization v h (map f.toRingHom p)=
      (lineSpecialization v h p).map f.toRingHom := by
  have hf (r : ℚ) : f.toRingHom (algebraMap ℚ A r)=algebraMap ℚ B r := f.commutes r
  induction p using MvPolynomial.induction_on with
  | C a => simp only [map_C,lineSpecialization_C,Polynomial.map_C]
  | add p q hp hq => simp only [map_add,Polynomial.map_add,hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,map_X,lineSpecialization_X,Polynomial.map_add,Polynomial.map_mul,
      Polynomial.map_C,Polynomial.map_X,hf,hp]

lemma lineSpecialization_map_algebra (v h : σ → ℚ) (p : MvPolynomial σ ℚ) :
    lineSpecialization (A:=A) v h (map (algebraMap ℚ A) p)=
      (lineSpecialization v h p).map (algebraMap ℚ A) :=
  lineSpecialization_map v h (Algebra.ofId ℚ A) p
end ElementaryPositivity.CenterCalculus

end

end OAI
