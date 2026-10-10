import OAI.AlgebraicGeometry.StableCoordinate.GradedDegeneration
import OAI.AlgebraicGeometry.StableCoordinate.LaurentPresentation
import OAI.AlgebraicGeometry.StableCoordinate.LaurentWeightedMap
import OAI.AlgebraicGeometry.StableCoordinate.LaurentLNDDescent

namespace OAI

/-!
# Homogeneity through the source's actual Laurent presentation

The integer grading on `G` is the quotient grading with generator weights
`(-1,0,0,1,1)`.  The canonical map into the Laurent algebra over the quadric
ring sends degree `n` to the single Laurent exponent `-n`.  In particular,
a homogeneous derivation of degree `m`, when intertwined with a derivation
on that Laurent algebra, satisfies the precise homogeneity hypothesis of
`LaurentDescent` with exponent `-m`.
-/

noncomputable section

namespace StableCoordinate.SourceLocalizedDerivation

open MvPolynomial LaurentPolynomial
open StableCoordinate.Obstruction
open scoped LaurentPolynomial

variable (k : Type*) [CommRing k]

/-- The coefficient part of the five canonical Laurent generator images. -/
def generatorCoefficients : Fin 5 → B k :=
  ![1, sB k, bX k 3, f0 k, g0 k]

/-- The canonical generator images have exactly the assigned integer weights. -/
theorem toLaurentBase_generator (i : Fin 5) :
    LaurentPresentation.toLaurentBase k (gX k i) =
      LaurentPolynomial.C (generatorCoefficients k i) *
        LaurentPolynomial.T (-presentationWeight i) := by
  fin_cases i <;>
    simp [LaurentPresentation.laurentValues, generatorCoefficients, presentationWeight]

/-- A homogeneous representative maps to its expected Laurent monomial. -/
theorem toLaurentBase_mk_homogeneous {p : P k 5} {n : ℤ}
    (hp : p.IsWeightedHomogeneous presentationWeight n) :
    LaurentPresentation.toLaurentBase k (Ideal.Quotient.mk (idealG k) p) =
      LaurentPolynomial.C (aeval (generatorCoefficients k) p) *
        LaurentPolynomial.T (-n) := by
  exact LaurentWeightedMap.map_homogeneous presentationWeight (generatorCoefficients k)
    ((LaurentPresentation.toLaurentBase k).comp (Ideal.Quotient.mkₐ k (idealG k)))
    (fun i => toLaurentBase_generator k i) hp

/-- The image of every homogeneous element has support at one Laurent exponent. -/
theorem toLaurentBase_coeff_eq_zero {r : G k} {n : ℤ}
    (hr : r ∈ gPiece k n) (j : ℤ) (hj : j ≠ -n) :
    (LaurentPresentation.toLaurentBase k r).coeff j = 0 := by
  obtain ⟨p, hp, rfl⟩ := hr
  change (LaurentPresentation.toLaurentBase k (Ideal.Quotient.mk (idealG k) p)).coeff j = 0
  rw [toLaurentBase_mk_homogeneous k hp, LaurentDescent.coeff_C_mul_T,
    ite_eq_right (Ne.symm hj)]

/-- The singleton-support statement in the exact normalization used by descent. -/
theorem toLaurentBase_homogeneous {r : G k} {n : ℤ}
    (hr : r ∈ gPiece k n) :
    LaurentPresentation.toLaurentBase k r =
      LaurentPolynomial.C ((LaurentPresentation.toLaurentBase k r).coeff (-n)) *
        LaurentPolynomial.T (-n) := by
  obtain ⟨p, hp, rfl⟩ := hr
  change LaurentPresentation.toLaurentBase k (Ideal.Quotient.mk (idealG k) p) =
    LaurentPolynomial.C
      ((LaurentPresentation.toLaurentBase k (Ideal.Quotient.mk (idealG k) p)).coeff (-n)) *
      LaurentPolynomial.T (-n)
  rw [toLaurentBase_mk_homogeneous k hp, LaurentDescent.coeff_C_mul_T, ite_eq_left rfl]

/-- The two constructions of the canonical quadric map agree. -/
theorem baseMap_eq_baseToDegeneration :
    LaurentPresentation.baseMap k = baseToDegeneration k := by
  apply Ideal.Quotient.algHom_ext k
  apply MvPolynomial.algHom_ext
  intro i
  change LaurentPresentation.baseMap k (bX k i) = baseToDegeneration k (bX k i)
  simp only [LaurentPresentation.baseMap_bX, baseToDegeneration_bX]
  rfl

/-- The existing Laurent-presentation base map has degree-zero image. -/
theorem baseMap_mem_piece (b : B k) :
    LaurentPresentation.baseMap k b ∈ gPiece k 0 := by
  rw [baseMap_eq_baseToDegeneration]
  exact baseToDegeneration_mem_piece k b

/-- Actual homogeneous-degree transport gives the hypothesis of Laurent descent.
The intertwining identity is supplied by the invariant-localization construction.
-/
theorem homogeneousOnConstants_of_intertwining
    (D : Derivation k (G k) (G k))
    (δ : Derivation k (LaurentPresentation.Laurent k) (LaurentPresentation.Laurent k))
    (m : ℤ)
    (hD : ∀ (n : ℤ) (r : G k), r ∈ gPiece k n → D r ∈ gPiece k (n + m))
    (hintertwine : ∀ r : G k,
      δ (LaurentPresentation.toLaurentBase k r) = LaurentPresentation.toLaurentBase k (D r)) :
    LaurentDescent.HomogeneousOnConstants δ (-m) := by
  intro b
  have hDb : D (LaurentPresentation.baseMap k b) ∈ gPiece k m := by
    simpa using hD 0 (LaurentPresentation.baseMap k b) (baseMap_mem_piece k b)
  have hcompat := hintertwine (LaurentPresentation.baseMap k b)
  rw [LaurentPresentation.toLaurentBase_baseMap] at hcompat
  rw [hcompat]
  exact toLaurentBase_homogeneous k hDb

end StableCoordinate.SourceLocalizedDerivation

end

end OAI
