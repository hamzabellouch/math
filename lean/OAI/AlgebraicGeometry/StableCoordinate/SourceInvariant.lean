import OAI.AlgebraicGeometry.StableCoordinate.LaurentDerivationTransport
import OAI.AlgebraicGeometry.StableCoordinate.SourceLocalizedDerivation
import OAI.AlgebraicGeometry.StableCoordinate.ModificationEmbedding

namespace OAI

/-!
# A homogeneous source invariant gives an invariant in the quadric center

This is the last passage in Section 3's coordinate obstruction.  Everything
here takes place in the literal source rings `G`, `B`, and `I`: the Laurent
extension is constructed, its homogeneity is proved from the source grading,
and its positive-degree invariant has a nonzero numerator in the actual center
ideal.  No domain or localization injectivity assumption is added to the
source data.
-/

noncomputable section

namespace StableCoordinate.SourceInvariant

open Obstruction
open LaurentPresentation

variable {k : Type*} [Field k]

/-- The final source-specific Laurent descent step.  A nonzero homogeneous
locally nilpotent derivation of the actual degeneration ring, fixing the
parameter and a nonzero positive-degree element, produces the nonzero
quadric derivation and center-ideal invariant required in the obstruction. -/
theorem exists_quadric_lnd_invariant
    (D : Derivation k (G k) (G k)) (m : ℤ)
    (hshift : ∀ (n : ℤ) (r : G k), r ∈ gPiece k n → D r ∈ gPiece k (n + m))
    (hD : IsLocallyNilpotent D) (hDne : D ≠ 0) (hp : D (gX k 0) = 0)
    {η : G k} {ℓ : ℤ} (hℓ : 0 < ℓ) (hη : η ∈ gPiece k ℓ)
    (hηne : η ≠ 0) (hDη : D η = 0) :
    ∃ E : Derivation k (B k) (B k),
      IsLocallyNilpotent E ∧ E ≠ 0 ∧
      ∃ h : B k, h ∈ I k ∧ h ≠ 0 ∧ E h = 0 := by
  let δ := LaurentDerivationTransport.lift D hp
  have hδhom : LaurentDescent.HomogeneousOnConstants δ (-m) :=
    SourceLocalizedDerivation.homogeneousOnConstants_of_intertwining k D δ m
      hshift (LaurentDerivationTransport.lift_intertwine D hp)
  have hδT : δ (LaurentPolynomial.T 1) = 0 :=
    LaurentDerivationTransport.lift_T_one D hp
  have hδ : IsLocallyNilpotent (k := k) (A := LaurentPolynomial (B k)) δ :=
    LaurentDerivationTransport.lift_locallyNilpotent D hp hD
  have hδne : δ ≠ 0 := LaurentDerivationTransport.lift_ne_zero D hp hDne
  obtain ⟨hηimage, hδη⟩ := LaurentDerivationTransport.lift_nonzero_invariant D hp η hηne hDη
  have hℓnat : (ℓ.toNat : ℤ) = ℓ := Int.toNat_of_nonneg (le_of_lt hℓ)
  have hℓpos : 0 < ℓ.toNat := by omega
  have hhom : ModificationPieces.Homogeneous (ℓ.toNat : ℤ) (toLaurentBase k η) := by
    rw [hℓnat]
    exact SourceLocalizedDerivation.toLaurentBase_coeff_eq_zero k hη
  obtain ⟨h, hhI, hhne, hηeq⟩ := ModificationPieces.positive_nonzero_numerator
    hℓpos (ModificationEmbedding.toLaurent_mem k η) hhom hηimage
  refine ⟨LaurentDescent.descend δ (-m) hδhom,
    LaurentDescent.descend_locallyNilpotent δ (-m) hδhom hδT hδ,
    LaurentDescent.descend_ne_zero δ (-m) hδhom hδT hδne, h, hhI, hhne, ?_⟩
  apply LaurentDescent.descend_invariant δ (-m) hδhom hδT
  rw [← hηeq]
  exact hδη

end StableCoordinate.SourceInvariant

end

end OAI
