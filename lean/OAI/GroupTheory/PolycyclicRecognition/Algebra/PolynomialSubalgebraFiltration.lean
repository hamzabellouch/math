import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialSubalgebraGroup
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinFiniteDifference

namespace OAI

/-! # Intrinsic lower-central estimates on polynomial Lie subgroups

The restricted BCH law has the same normalized linear term. Its higher
terms raise the intrinsic lower central series of the subalgebra.
-/

noncomputable section
namespace PolycyclicRecognition
open LieModule
attribute [local instance] polynomialSubalgebraGroup
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

theorem polynomialSubalgebra_axis_normalized (K : LieSubalgebra ℝ L) (i : Fin 2) (v : K) :
    finiteDynkinPolynomial P.coefficients (Pi.single i v) = v := by
  classical
  apply Subtype.ext
  have hh := finiteDynkinPolynomial_map K.incl P.coefficients (Pi.single i v)
  have he : (fun j : Fin 2 => K.incl ((Pi.single i v : Fin 2 → K) j)) =
      Pi.single i (v : L) := by
    funext j
    by_cases h : j = i <;> simp [h]
  rw [he, PolynomialExponentialCoordinates.axis_normalized] at hh
  exact hh

theorem polynomialSubalgebra_mul_difference (K : LieSubalgebra ℝ L)
    (k : ℕ) (a b c d : K)
    (hac : a - c ∈ lowerCentralSeries ℝ K K k)
    (hbd : b - d ∈ lowerCentralSeries ℝ K K k) :
    ((a * b) - (c * d)) - ((a - c) + (b - d)) ∈
      (lowerCentralSeries ℝ K K (k + 1)).toSubmodule := by
  have h := finiteDynkinPolynomial_sub_linear_mem_succ P.coefficients ![a, b] ![c, d] k (by
    intro i
    fin_cases i
    · exact hac
    · exact hbd)
  have he : ![a, b] - ![c, d] = ![a - c, b - d] := by
    ext i
    fin_cases i <;> rfl
  rw [he, binaryDynkinLinearPart P.coefficients (polynomialSubalgebra_axis_normalized K),
    ← polynomialSubalgebra_mul_eq, ← polynomialSubalgebra_mul_eq] at h
  exact h

theorem polynomialSubalgebra_inner_difference (K : LieSubalgebra ℝ L)
    (v : K) (k : ℕ) (x : K) (hx : x ∈ lowerCentralSeries ℝ K K k) :
    v * x * v⁻¹ - x ∈ lowerCentralSeries ℝ K K (k + 1) := by
  let F : ℕ → Submodule ℝ K := fun k => (lowerCentralSeries ℝ K K k).toSubmodule
  have hone : (1 : K) = 0 := Subtype.ext P.one_eq_zero
  have hv0 : v * (0 : K) = v := by rw [← hone, mul_one]
  have h1 : (v * x - v) - x ∈ F (k + 1) := by
    simpa only [sub_self, sub_zero, zero_add, hv0] using
      polynomialSubalgebra_mul_difference K k v x v 0 (by simp) (by simpa using hx)
  have hd : v * x - v ∈ F k := by
    have hh := (F k).add_mem ((antitone_lowerCentralSeries ℝ K K (Nat.le_succ k)) h1) hx
    convert hh using 1
    abel
  have h2 : (v * x * v⁻¹ - 0) - (v * x - v) ∈ F (k + 1) := by
    simpa only [sub_self, add_zero, mul_inv_cancel, hone] using
      polynomialSubalgebra_mul_difference K k (v * x) v⁻¹ v v⁻¹ hd (by simp)
  have hh := (F (k + 1)).add_mem h2 h1
  change v * x * v⁻¹ - x ∈ F (k + 1)
  convert hh using 1
  abel

end PolycyclicRecognition

end

end OAI
