import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.SetTheory.Cardinal.ToNat
import Mathlib.Tactic
import OAI.NumberTheory.SiegelZeros.Hilbert.PrimeHilbertDimension

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.W24

section Normalization

variable (k B : Type*) [Field k] [CommRing B] [IsDomain B] [Algebra k B]

theorem normalization_trdeg_toNat (s : ℕ)
    (g : MvPolynomial (Fin s) k →ₐ[k] B)
    (hg : Function.Injective g) (hi : g.IsIntegral) :
    (Algebra.trdeg k B).toNat = s := by
  let : Algebra (MvPolynomial (Fin s) k) B := g.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin s) k) B :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  have : FaithfulSMul (MvPolynomial (Fin s) k) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) B := ⟨hi⟩
  have : Algebra.IsAlgebraic (MvPolynomial (Fin s) k) B :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral x).isAlgebraic⟩
  have ht := congrArg Cardinal.toNat
    (lift_trdeg_add_eq k (MvPolynomial (Fin s) k) B)
  simpa [trdeg_eq_zero] using ht.symm

theorem finiteType_domain_krullDim_eq_trdeg [Algebra.FiniteType k B] :
    ringKrullDim B = ((Algebra.trdeg k B).toNat : WithBot ℕ∞) := by
  obtain ⟨s, g, hg, hfin, hdim⟩ := exists_finite_normalization_with_dimension k B
  rw [hdim, normalization_trdeg_toNat k B s g hg hfin.to_isIntegral]

end Normalization

section AlgebraicTower

variable (k B C : Type*) [Field k] [CommRing B] [IsDomain B]
  [CommRing C] [IsDomain C] [Algebra k B] [Algebra k C] [Algebra B C]
  [IsScalarTower k B C] [FaithfulSMul B C]

theorem trdeg_toNat_eq_of_algebraic_tower [Algebra.IsAlgebraic B C] :
    (Algebra.trdeg k B).toNat = (Algebra.trdeg k C).toNat := by
  have ht := congrArg Cardinal.toNat (lift_trdeg_add_eq k B C)
  simpa only [trdeg_eq_zero, Cardinal.lift_zero, add_zero, Cardinal.toNat_lift] using ht

theorem localization_trdeg_toNat_eq (M : Submonoid B) [IsLocalization M C] :
    (Algebra.trdeg k B).toNat = (Algebra.trdeg k C).toNat := by
  have : Algebra.IsAlgebraic B C := IsLocalization.isAlgebraic C M
  exact trdeg_toNat_eq_of_algebraic_tower k B C

end AlgebraicTower

section CoefficientField

variable (k F B C : Type*) [Field k] [Field F] [CommRing B] [IsDomain B]
  [CommRing C] [IsDomain C] [Algebra k F] [Algebra k B] [Algebra k C]
  [Algebra B C] [Algebra F C] [IsScalarTower k B C] [IsScalarTower k F C]
  [FaithfulSMul B C] [Algebra.FiniteType k B] [Algebra.FiniteType F C]

theorem coefficient_localization_dimension
    (M : Submonoid B) [IsLocalization M C]
    (hF : Algebra.trdeg k F < Cardinal.aleph0) :
    ringKrullDim C + ((Algebra.trdeg k F).toNat : WithBot ℕ∞) = ringKrullDim B := by
  have hFC : Algebra.trdeg F C < Cardinal.aleph0 :=
    trdeg_lt_aleph0_of_finiteType (R := F) (S := C)
  have ht := congrArg Cardinal.toNat (lift_trdeg_add_eq k F C)
  rw [Cardinal.toNat_lift_add_lift hF hFC, Cardinal.toNat_lift] at ht
  have hl := localization_trdeg_toNat_eq k B C M
  rw [finiteType_domain_krullDim_eq_trdeg F C,
    finiteType_domain_krullDim_eq_trdeg k B, hl, ← ht, Nat.cast_add]
  exact add_comm _ _

end CoefficientField

end WeightedTorusJets.W24

end

end SiegelZeros

end OAI
