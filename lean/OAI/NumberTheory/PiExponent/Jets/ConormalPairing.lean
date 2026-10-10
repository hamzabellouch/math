import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Cotangent

namespace OAI

noncomputable section
namespace PiExponentSiegel.W58

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
variable (I : Ideal R) (D : Derivation K R (R ⧸ I))

theorem ideal_smul_quotient_zero (x : I) (z : R ⧸ I) : (x : R) • z = 0 := by
  rw [Algebra.smul_def]
  change Ideal.Quotient.mk I (x : R) * z = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr x.property, zero_mul]

def normalRestriction : I →ₗ[R] R ⧸ I where
  toFun x := D x
  map_add' x y := D.map_add x y
  map_smul' r x := by
    change D (r * (x : R)) = r • D (x : R)
    rw [D.leibniz, ideal_smul_quotient_zero I x, add_zero]

theorem normalRestriction_product_zero (x y : I) : normalRestriction I D (x * y) = 0 := by
  change D ((x : R) * (y : R)) = 0
  rw [D.leibniz, ideal_smul_quotient_zero I x, ideal_smul_quotient_zero I y, add_zero]

def conormalPairing : I.Cotangent →ₗ[R] R ⧸ I :=
  Ideal.Cotangent.lift (normalRestriction I D) (normalRestriction_product_zero I D)

@[simp] theorem conormalPairing_toCotangent (x : I) :
    conormalPairing I D (I.toCotangent x) = D x := rfl

end PiExponentSiegel.W58

end

end OAI
