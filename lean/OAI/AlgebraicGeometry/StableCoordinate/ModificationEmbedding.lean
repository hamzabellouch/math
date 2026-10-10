import OAI.AlgebraicGeometry.StableCoordinate.LaurentPresentation
import OAI.AlgebraicGeometry.StableCoordinate.ModificationPieces

namespace OAI

/-!
# The degeneration embeds into the affine-modification Laurent model

This file uses the canonical source map from `LaurentPresentation` and
identifies its image with the extended Rees algebra.  Injectivity is supplied
by the separate localization/domain argument; it is not assumed here.
-/

noncomputable section

namespace StableCoordinate.ModificationEmbedding

open MvPolynomial
open scoped LaurentPolynomial

namespace LP
abbrev C {R : Type*} [CommRing R] := LaurentPolynomial.C (R := R)
abbrev T {R : Type*} [CommRing R] := LaurentPolynomial.T (R := R)
end LP

open Obstruction

variable (k : Type*) [CommRing k]

/-- Alias for the canonical source-ordered Laurent coordinate values. -/
abbrev values := LaurentPresentation.laurentValues k

/-- Polynomial evaluation before taking the degeneration quotient. -/
def polynomialMap : P k 5 →ₐ[k] LaurentPolynomial (B k) :=
  MvPolynomial.aeval (values k)

@[simp]
theorem polynomialMap_X (i : Fin 5) :
    polynomialMap k (X i) = values k i :=
  MvPolynomial.aeval_X _ _

/-- Alias for the canonical map from `G` to `B[τ,τ⁻¹]`. -/
abbrev toLaurent := LaurentPresentation.toLaurentBase k

@[simp]
theorem toLaurent_mk (p : P k 5) :
    toLaurent k (Ideal.Quotient.mk (idealG k) p) = polynomialMap k p :=
  rfl

@[simp]
theorem toLaurent_gX (i : Fin 5) :
    toLaurent k (gX k i) = values k i :=
  LaurentPresentation.toLaurentBase_gX k i

theorem values_mem (i : Fin 5) :
    values k i ∈ ModificationPieces.modification (I k) := by
  fin_cases i
  · exact ModificationPieces.T_one_mem_modification _
  · exact (ModificationPieces.modification (I k)).algebraMap_mem _
  · exact (ModificationPieces.modification (I k)).algebraMap_mem _
  · apply ModificationPieces.numerator_mem_modification
    exact Ideal.subset_span (by simp)
  · apply ModificationPieces.numerator_mem_modification
    exact Ideal.subset_span (by simp)

theorem polynomialMap_mem (p : P k 5) :
    polynomialMap k p ∈ ModificationPieces.modification (I k) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp only [polynomialMap, MvPolynomial.aeval_C, LaurentPolynomial.algebraMap_apply]
      exact (ModificationPieces.modification (I k)).algebraMap_mem _
  | add p q hp hq =>
      rw [map_add]
      exact (ModificationPieces.modification (I k)).add_mem hp hq
  | mul_X p i hp =>
      rw [map_mul, polynomialMap_X]
      exact (ModificationPieces.modification (I k)).mul_mem hp (values_mem k i)

/-- Every element of the actual source degeneration lands in the affine modification. -/
theorem toLaurent_mem (a : G k) :
    toLaurent k a ∈ ModificationPieces.modification (I k) := by
  induction a using Quotient.inductionOn with
  | h p => exact polynomialMap_mem k p

/-- The source generator weights are exactly opposite their Laurent exponents. -/
theorem values_homogeneous (i : Fin 5) :
    ModificationPieces.Homogeneous (presentationWeight i) (values k i) := by
  fin_cases i
  · exact ModificationPieces.homogeneous_single (-1) (1 : B k)
  · exact ModificationPieces.homogeneous_C (sB k)
  · exact ModificationPieces.homogeneous_C (bX k 3)
  · change ModificationPieces.Homogeneous 1 (LP.C (f0 k) * LP.T (-1))
    rw [← LaurentPolynomial.single_eq_C_mul_T]
    exact ModificationPieces.homogeneous_single 1 (f0 k)
  · change ModificationPieces.Homogeneous 1 (LP.C (g0 k) * LP.T (-1))
    rw [← LaurentPolynomial.single_eq_C_mul_T]
    exact ModificationPieces.homogeneous_single 1 (g0 k)

/-- An actual weighted homogeneous representative maps to the corresponding
single Laurent degree; no grading of a quotient is postulated. -/
theorem polynomialMap_homogeneous {p : P k 5} {d : ℤ}
    (hp : p.IsWeightedHomogeneous presentationWeight d) :
    ModificationPieces.Homogeneous d (polynomialMap k p) :=
  ModificationPieces.homogeneous_aeval presentationWeight (values k)
    (values_homogeneous k) hp

/-- Positive-degree homogeneous representatives have numerators in the
appropriate power of the exact source ideal. -/
theorem polynomialMap_positive_piece {p : P k 5} {ℓ : ℕ}
    (hp : p.IsWeightedHomogeneous presentationWeight (ℓ : ℤ)) :
    ∃ h ∈ I k ^ ℓ, polynomialMap k p = LP.C h * LP.T (-(ℓ : ℤ)) :=
  ModificationPieces.homogeneous_numerator (polynomialMap_mem k p)
    (polynomialMap_homogeneous k hp)

/-- The extraction needed for the noncoordinate obstruction, stated directly
for nonzero Laurent images of homogeneous representatives. -/
theorem polynomialMap_positive_nonzero_numerator {p : P k 5} {ℓ : ℕ}
    (hℓ : 0 < ℓ) (hp : p.IsWeightedHomogeneous presentationWeight (ℓ : ℤ))
    (hne : polynomialMap k p ≠ 0) :
    ∃ h ∈ I k, h ≠ 0 ∧ polynomialMap k p = LP.C h * LP.T (-(ℓ : ℤ)) :=
  ModificationPieces.positive_nonzero_numerator hℓ (polynomialMap_mem k p)
    (polynomialMap_homogeneous k hp) hne

/-- The canonical map's image is a `B`-subalgebra, since the base map is a
section on constant Laurent polynomials. -/
def imageSubalgebra : Subalgebra (B k) (LaurentPolynomial (B k)) where
  carrier := Set.range (toLaurent k)
  zero_mem' := ⟨0, map_zero _⟩
  one_mem' := ⟨1, map_one _⟩
  add_mem' := by
    rintro p q ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, map_add _ _ _⟩
  mul_mem' := by
    rintro p q ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, map_mul _ _ _⟩
  algebraMap_mem' r :=
    ⟨LaurentPresentation.baseMap k r, LaurentPresentation.toLaurentBase_baseMap k r⟩

/-- Exact affine-modification image, with the actual source's two-generator center. -/
theorem image_eq_modification :
    imageSubalgebra k = ModificationPieces.modification (I k) := by
  apply le_antisymm
  · rintro p ⟨a, rfl⟩
    exact toLaurent_mem k a
  · rw [I, ModificationPieces.modification_pair_eq]
    apply Algebra.adjoin_le
    rintro p (rfl | rfl | rfl)
    · exact ⟨gX k 0, toLaurent_gX k 0⟩
    · exact ⟨gX k 3, toLaurent_gX k 3⟩
    · exact ⟨gX k 4, toLaurent_gX k 4⟩

theorem range_toLaurent :
    Set.range (toLaurent k) = (ModificationPieces.modification (I k) : Set _) := by
  change (imageSubalgebra k : Set (LaurentPolynomial (B k))) = _
  rw [image_eq_modification]

end StableCoordinate.ModificationEmbedding

end

end OAI
