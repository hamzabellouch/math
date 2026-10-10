import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import OAI.NumberTheory.SiegelZeros.Structure.Factorization

namespace OAI

noncomputable section
namespace SiegelZeros.W23
open Result.Workers.W57 WeightedTorusJets.W19 WeightedTorusJets.W18

variable {R L : Type*} [CommRing R] [CommRing L] [IsLocalRing L]
  [Algebra ℚ R] [Algebra ℚ L] [Algebra R L] [IsScalarTower ℚ R L]

def localResidueOnBase : R →+* IsLocalRing.ResidueField L :=
  (IsLocalRing.residue L).comp (algebraMap R L)

omit [Algebra ℚ R] [Algebra ℚ L] [IsScalarTower ℚ R L] in
theorem localResidueOnBase_unit (M : Submonoid R) [IsLocalization M L] (s : M) :
    IsUnit (localResidueOnBase (R := R) (L := L) s) :=
  (IsLocalization.map_units L s).map (IsLocalRing.residue L)

omit [Algebra ℚ R] [Algebra ℚ L] [IsScalarTower ℚ R L] in
theorem localResidueOnBase_lift (M : Submonoid R) [IsLocalization M L] :
    IsLocalization.lift (S := L) (localResidueOnBase_unit (L := L) M) =
      IsLocalRing.residue L := by
  apply IsLocalization.ringHom_ext M
  ext f
  simp only [RingHom.comp_apply, IsLocalization.lift_eq, localResidueOnBase]

def localResidueTaylorFactorization (M : Submonoid R) [IsLocalization M L]
    (D : Fin 3 → Derivation ℚ R R)
    (hD : ∀ i j, Commute (D i).toLinearMap (D j).toLinearMap)
    (t : Fin 3 → ℕ) (b : ℕ) (f : R)
    (hnext : ∀ g ∈ rectangleGenerators D t (b+1) f,
      algebraMap R L g ∈ IsLocalRing.maximalIdeal L) :
    L ⧸ localRectangleIdeal D t b f →+*
      RectangleJet (IsLocalRing.ResidueField L) (t 0+1) (t 1+1) (t 2+1) :=
  sourceTaylorFactorization M D hD (localResidueOnBase (L := L)) t b f
    (localResidueOnBase_unit (L := L) M)
    (fun g hg => (IsLocalRing.residue_eq_zero_iff _).mpr (hnext g hg))

theorem localizedRectangularJet_eq_residueTaylor (M : Submonoid R)
    [IsLocalization M L] (D₁ D₂ D₃ : Derivation ℚ R R) (a b c : ℕ) :
    localizedRectangularJet (L := L) M D₁ D₂ D₃ (localResidueOnBase (L := L))
      a b c (localResidueOnBase_unit (L := L) M) =
      rectangularJetHom (IsLocalRing.ResidueField L)
        (localizedDerivation (S := L) M D₁) (localizedDerivation (S := L) M D₂)
        (localizedDerivation (S := L) M D₃) (IsLocalRing.residue L) a b c := by
  rw [localizedRectangularJet_eq_localTaylor, localResidueOnBase_lift]

end SiegelZeros.W23

end

end OAI
