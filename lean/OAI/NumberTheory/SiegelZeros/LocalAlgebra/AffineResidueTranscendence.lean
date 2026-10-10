import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import OAI.NumberTheory.SiegelZeros.Intersection.AffineTranscendenceDimension

namespace OAI

namespace SiegelZeros

section

noncomputable section
namespace WeightedTorusJets.W24
open scoped nonZeroDivisors

theorem trdeg_lt_aleph0_of_algebraic_tower
    (k B C : Type*) [Field k] [CommRing B] [IsDomain B]
    [CommRing C] [IsDomain C] [Algebra k B] [Algebra k C] [Algebra B C]
    [IsScalarTower k B C] [FaithfulSMul B C] [Algebra.IsAlgebraic B C]
    (hB : Algebra.trdeg k B < Cardinal.aleph0) :
    Algebra.trdeg k C < Cardinal.aleph0 := by
  have ht := lift_trdeg_add_eq k B C
  simp only [trdeg_eq_zero, Cardinal.lift_zero, add_zero] at ht
  have hlt := Cardinal.lift_lt_aleph0.mpr hB
  rw [ht] at hlt
  exact Cardinal.lift_lt_aleph0.mp hlt

theorem affine_prime_quotient_dimension_eq_residue_trdeg
    (k A : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (Q : Ideal A) [Q.IsPrime] :
    ringKrullDim (A ⧸ Q) = ((Algebra.trdeg k Q.ResidueField).toNat : WithBot ℕ∞) := by
  have : FaithfulSMul (A ⧸ Q) Q.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      Q.injective_algebraMap_quotient_residueField
  rw [finiteType_domain_krullDim_eq_trdeg k (A ⧸ Q),
    localization_trdeg_toNat_eq k (A ⧸ Q) Q.ResidueField (nonZeroDivisors (A ⧸ Q))]

theorem affine_prime_quotient_dimension_eq_basis_card
    (k A β : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (Q : Ideal A) [Q.IsPrime]
    (b : β → Q.ResidueField) (hb : IsTranscendenceBasis k b) :
    ringKrullDim (A ⧸ Q) = (Nat.card β : WithBot ℕ∞) := by
  have ht := congrArg Cardinal.toNat hb.lift_cardinalMk_eq_trdeg
  simp only [Cardinal.toNat_lift] at ht
  rw [affine_prime_quotient_dimension_eq_residue_trdeg k A Q, ← ht]
  rfl

theorem rational_coefficient_trdeg_toNat (k β : Type*) [Field k] :
    (Algebra.trdeg k (FractionRing (MvPolynomial β k))).toNat = Nat.card β := by
  rw [← localization_trdeg_toNat_eq k (MvPolynomial β k)
    (FractionRing (MvPolynomial β k)) (nonZeroDivisors (MvPolynomial β k))]
  simp only [MvPolynomial.trdeg_of_isDomain, Cardinal.toNat_lift, Nat.card]

theorem rational_coefficient_trdeg_lt_aleph0
    (k β : Type*) [Field k] [Finite β] :
    Algebra.trdeg k (FractionRing (MvPolynomial β k)) < Cardinal.aleph0 := by
  have : Algebra.IsAlgebraic (MvPolynomial β k) (FractionRing (MvPolynomial β k)) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial β k))
  apply trdeg_lt_aleph0_of_algebraic_tower k (MvPolynomial β k)
    (FractionRing (MvPolynomial β k))
  simp only [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_lt_aleph0,
    Cardinal.mk_lt_aleph0]

theorem coefficient_trdeg_eq_prime_quotient_dimension
    (k A β : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (Q : Ideal A) [Q.IsPrime]
    (b : β → Q.ResidueField) (hb : IsTranscendenceBasis k b) :
    ((Algebra.trdeg k (FractionRing (MvPolynomial β k))).toNat : WithBot ℕ∞) =
      ringKrullDim (A ⧸ Q) := by
  rw [rational_coefficient_trdeg_toNat k β,
    affine_prime_quotient_dimension_eq_basis_card k A β Q b hb]

end WeightedTorusJets.W24

end

end

end SiegelZeros

end OAI
