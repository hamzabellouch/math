import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialSubalgebraNilpotence
import OAI.GroupTheory.PolycyclicRecognition.Algebra.InvariantLinearLayer

namespace OAI

/-! # Additive coordinates on the polynomial group's lower-central layers -/

noncomputable section
namespace PolycyclicRecognition
open LieModule
attribute [local instance] polynomialSubalgebraGroup
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

def polynomialLowerCentralProjection (K : LieSubalgebra ℝ L) (k : ℕ) :
    polynomialLieIdealSubgroup K (lowerCentralSeries ℝ K K k) →*
      Multiplicative (InvariantLinearLayer (lowerCentralSeries ℝ K K k).toSubmodule
        (lowerCentralSeries ℝ K K (k + 1)).toSubmodule) where
  toFun x := Multiplicative.ofAdd (Submodule.Quotient.mk
    (⟨x.val, x.property⟩ : (lowerCentralSeries ℝ K K k).toSubmodule))
  map_one' := by
    apply Multiplicative.ext
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change (1 : K) ∈ lowerCentralSeries ℝ K K (k + 1)
    have hone : (1 : K) = 0 := Subtype.ext P.one_eq_zero
    rw [hone]
    exact LieSubmodule.zero_mem _
  map_mul' x y := by
    apply Multiplicative.ext
    change (Submodule.Quotient.mk ⟨(x : K) * y, _⟩ :
      InvariantLinearLayer (lowerCentralSeries ℝ K K k).toSubmodule
        (lowerCentralSeries ℝ K K (k + 1)).toSubmodule) =
      Submodule.Quotient.mk ⟨(x : K), x.property⟩ + Submodule.Quotient.mk ⟨(y : K), y.property⟩
    rw [← Submodule.Quotient.mk_add]
    apply (Submodule.Quotient.eq _).mpr
    change (x : K) * y - ((x : K) + y) ∈ (lowerCentralSeries ℝ K K (k + 1)).toSubmodule
    have hone : (1 : K) = 0 := Subtype.ext P.one_eq_zero
    have hx0 : (x : K) * 0 = x := by rw [← hone, mul_one]
    have hh := polynomialSubalgebra_mul_difference K k (x : K) y x 0 (by simp)
      (by rw [sub_zero]; exact y.property)
    rw [hx0] at hh
    convert hh using 1
    abel

theorem polynomialLowerCentralProjection_eq_one_iff (K : LieSubalgebra ℝ L) (k : ℕ)
    (x : polynomialLieIdealSubgroup K (lowerCentralSeries ℝ K K k)) :
    polynomialLowerCentralProjection K k x = 1 ↔
      (x : K) ∈ lowerCentralSeries ℝ K K (k + 1) := by
  let U := (lowerCentralSeries ℝ K K k).toSubmodule
  let W := (lowerCentralSeries ℝ K K (k + 1)).toSubmodule.comap U.subtype
  change Multiplicative.ofAdd (Submodule.Quotient.mk
    (⟨x.val, x.property⟩ : U) : U ⧸ W) =
      Multiplicative.ofAdd 0 ↔ _
  constructor
  · intro h
    exact (Submodule.Quotient.mk_eq_zero W).mp (congrArg Multiplicative.toAdd h)
  · intro h
    apply Multiplicative.ext
    exact (Submodule.Quotient.mk_eq_zero W).mpr h

end PolycyclicRecognition

end

end OAI
