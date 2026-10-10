import OAI.Analysis.Cotype.CubeCoordinateProjections
import OAI.Analysis.Cotype.ProjectionEigenvectors

namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def walshVector {n : ℕ} (p : Cube n) (x : X) : PiLp 2 (fun _ : Cube n => X) :=
  toLp 2 (fun ε => character p ε • x)

theorem vectorWalsh_inversion {n : ℕ} (f : Cube n → X) (ε : Cube n) :
    (∑ p : Cube n, character p ε • vectorWalsh f p) = f ε := by
  classical
  have hc : (Fintype.card (Cube n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have ho η : (∑ p : Cube n, character p ε*character p η) =
      if ε=η then (Fintype.card (Cube n) : ℝ) else 0 := by
    simp_rw [character_symm _ ε, character_symm _ η]
    exact character_orthogonality ε η
  calc
    _ = ∑ η : Cube n, ((Fintype.card (Cube n) : ℝ)⁻¹ *
        ∑ p : Cube n, character p ε*character p η) • f η := by
      simp only [vectorWalsh, average, Finset.smul_sum, smul_smul,
        Finset.mul_sum, Finset.sum_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro η _
      apply Finset.sum_congr rfl
      intro p _
      congr 1
      ring
    _ = _ := by simp [ho]

theorem walshVector_inversion {n : ℕ} (f : PiLp 2 (fun _ : Cube n => X)) :
    (∑ p : Cube n, walshVector p (vectorWalsh (fun ε => f ε) p)) = f := by
  ext ε
  simpa [walshVector] using
    vectorWalsh_inversion (fun ε => f ε) ε

theorem coordinateExpectation_walshVector {n : ℕ} (i : Fin n) (p : Cube n) (x : X) :
    coordinateExpectation i (walshVector p x) =
      (if p i then (0 : ℝ) else 1) • walshVector p x := by
  ext ε
  have ht : character p (signCubeTwist (unitIndex i) ε) = sign (p i)*character p ε := by
    change character p (xorCube (unitIndex i) ε) = _
    rw [character_xor, character_symm p (unitIndex i), character_unitIndex]
  simp only [coordinateExpectation_apply, walshVector, PiLp.smul_apply, ht, smul_smul]
  cases hpi : p i <;> simp only [sign_false, sign_true, Bool.false_eq_true, ite_false, ite_true]
  all_goals module

theorem coordinate_firstCoefficient_eq_radProjection {n : ℕ} (f : Cube n → X) :
    projectionLinearCoefficient (coordinateExpectation (X := X) (n := n)) (toLp 2 f) =
      toLp 2 (radProjection X f) := by
  classical
  calc
    _ = projectionLinearCoefficient (coordinateExpectation (X := X) (n := n))
        (∑ p : Cube n, walshVector p (vectorWalsh f p)) := by
      rw [walshVector_inversion (toLp 2 f)]
    _ = ∑ p : Cube n, ∑ i : Fin n,
        if p = unitIndex i then walshVector p (vectorWalsh f p) else 0 := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro p _
      exact projectionLinearCoefficient_eigenvector
        (X := PiLp 2 (fun _ : Cube n => X)) (n := n)
        (fun i : Fin n => coordinateExpectation (X := X) i) p (walshVector p (vectorWalsh f p))
        (fun i => coordinateExpectation_walshVector i p (vectorWalsh f p))
    _ = ∑ i : Fin n, walshVector (unitIndex i) (vectorWalsh f (unitIndex i)) := by
      rw [Finset.sum_comm]
      simp
    _ = _ := by
      ext ε
      simp [walshVector, radProjection, rademacherSum, vectorWalsh, moment]

theorem coordinate_firstCoefficient_probabilityL2_norm {n : ℕ} (f : Cube n → X) :
    ‖projectionLinearCoefficient (coordinateExpectation (X := X) (n := n)) (probabilityL2Vector f)‖ =
      cubeL2 X (radProjection X f) := by
  rw [probabilityL2Vector, map_smul, coordinate_firstCoefficient_eq_radProjection]
  exact probabilityL2Vector_norm (radProjection X f)

end Cotype

end

end OAI
