import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.PowerSeries.Trunc
import OAI.NumberTheory.SiegelZeros.Structure.RectangleGenerators

namespace OAI

namespace SiegelZeros

noncomputable section
namespace Result.Workers.W57
variable (K : Type*) [CommRing K]

def polynomialJetMap (n : ℕ) : Polynomial K →+* Jet K n :=
  (jetProjection K n).comp Polynomial.coeToPowerSeries.ringHom

theorem polynomialJetMap_surjective (n : ℕ) :
    Function.Surjective (polynomialJetMap K n) := by
  intro y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨PowerSeries.trunc n f, ?_⟩
  change Ideal.Quotient.mk (truncationIdeal K n)
    ((PowerSeries.trunc n f : Polynomial K) : PowerSeries K) =
      Ideal.Quotient.mk (truncationIdeal K n) f
  rw [Ideal.Quotient.eq, truncationIdeal, Ideal.mem_span_singleton,
    PowerSeries.X_pow_dvd_iff]
  intro i hi
  rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, ite_eq_left hi, sub_self]

theorem polynomialJetMap_ker (n : ℕ) :
    RingHom.ker (polynomialJetMap K n) =
      Ideal.span {(Polynomial.X : Polynomial K)^n} := by
  ext p
  change polynomialJetMap K n p = 0 ↔ _
  change Ideal.Quotient.mk (truncationIdeal K n) (p : PowerSeries K) = 0 ↔ _
  rw [truncation_eq_zero_iff, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff]
  simp only [Polynomial.coeff_coe]

def polynomialJetEquiv (n : ℕ) :
    (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K)^n}) ≃+* Jet K n :=
  (Ideal.quotEquivOfEq (polynomialJetMap_ker K n).symm).trans
    ((polynomialJetMap K n).quotientKerEquivOfSurjective (polynomialJetMap_surjective K n))

end Result.Workers.W57

end

end SiegelZeros

end OAI
