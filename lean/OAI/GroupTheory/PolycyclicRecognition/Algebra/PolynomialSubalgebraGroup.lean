import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialModelExponential
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialDerivationAction

namespace OAI

/-! # Polynomial nilpotent group laws on Lie subalgebras

The finite BCH formula closes every Lie subalgebra under the group law. Lie
homomorphisms from such a subalgebra preserve that same finite formula.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

def polynomialSubalgebraSubgroup (K : LieSubalgebra ℝ L) : Subgroup L where
  carrier := K
  one_mem' := by rw [P.one_eq_zero]; exact K.zero_mem
  inv_mem' := by
    intro x hx
    rw [P.inv_eq_neg]
    exact K.neg_mem hx
  mul_mem' := by
    intro x y hx hy
    let a : K := ⟨x, hx⟩
    let b : K := ⟨y, hy⟩
    let z : K := finiteDynkinPolynomial P.coefficients ![a, b]
    have hz : (z : L) = x * y := by
      have hh := finiteDynkinPolynomial_map K.incl P.coefficients ![a, b]
      change (z : L) = _ at hh
      rw [P.mul_eq]
      convert hh using 1
      congr 1
      funext i
      fin_cases i <;> rfl
    rw [← hz]
    exact z.property

@[instance_reducible] def polynomialSubalgebraGroup (K : LieSubalgebra ℝ L) : Group K :=
  inferInstanceAs (Group (polynomialSubalgebraSubgroup K))

attribute [local instance] polynomialSubalgebraGroup

theorem polynomialSubalgebra_mul_eq (K : LieSubalgebra ℝ L) (x y : K) :
    x * y = finiteDynkinPolynomial P.coefficients ![x, y] := by
  apply Subtype.ext
  change (x : L) * (y : L) = _
  rw [P.mul_eq]
  have h := finiteDynkinPolynomial_map K.incl P.coefficients ![x, y]
  have he : (fun i : Fin 2 => K.incl (![x, y] i)) = ![(x : L), (y : L)] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at h
  exact h.symm

def polynomialSubalgebraHom (K : LieSubalgebra ℝ L) (f : K →ₗ⁅ℝ⁆ L) : K →* L where
  toFun := f
  map_one' := by
    have hzero : (1 : K) = 0 := Subtype.ext P.one_eq_zero
    rw [hzero, map_zero, P.one_eq_zero]
  map_mul' x y := by
    rw [polynomialSubalgebra_mul_eq, P.mul_eq]
    have h := finiteDynkinPolynomial_map f P.coefficients ![x, y]
    have he : (fun i : Fin 2 => f (![x, y] i)) = ![f x, f y] := by
      funext i
      fin_cases i <;> rfl
    rwa [he] at h

def polynomialSubalgebraMap (K J : LieSubalgebra ℝ L) (f : K →ₗ⁅ℝ⁆ L)
    (hf : ∀ x, f x ∈ J) : K →* J where
  toFun x := ⟨f x, hf x⟩
  map_one' := Subtype.ext ((polynomialSubalgebraHom K f).map_one)
  map_mul' x y := Subtype.ext ((polynomialSubalgebraHom K f).map_mul x y)

def polynomialSubalgebraEquiv (K J : LieSubalgebra ℝ L) (T : L ≃ₗ⁅ℝ⁆ L)
    (hT : ∀ x ∈ K, T x ∈ J) (hTi : ∀ x ∈ J, T.symm x ∈ K) : K ≃* J where
  toFun x := ⟨T x, hT x x.property⟩
  invFun x := ⟨T.symm x, hTi x x.property⟩
  left_inv x := Subtype.ext (T.symm_apply_apply x)
  right_inv x := Subtype.ext (T.apply_symm_apply x)
  map_mul' x y := Subtype.ext
    ((PolynomialExponentialCoordinates.groupAutomorphism (P := P) T).map_mul x y)

end PolycyclicRecognition

end

end OAI
