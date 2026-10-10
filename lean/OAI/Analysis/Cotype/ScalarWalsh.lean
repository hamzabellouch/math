import OAI.Analysis.Cotype.Moments
import OAI.Analysis.Cotype.CoefficientBounds

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [NormedSpace ℝ X] in
@[simp] theorem cubeL2_nonneg {n : ℕ} (f : Cube n → X) : 0 ≤ cubeL2 X f :=
  Real.sqrt_nonneg _

omit [NormedSpace ℝ X] in
theorem cubeL2_sq {n : ℕ} (f : Cube n → X) :
    cubeL2 X f ^ 2 = average (fun ε => ‖f ε‖ ^ 2) := by
  apply Real.sq_sqrt
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

def scalarWalsh {n : ℕ} (f : Cube n → ℝ) : Cube n → ℝ := fourier f

theorem scalarWalsh_twice {n : ℕ} (f : Cube n → ℝ) (ε : Cube n) :
    scalarWalsh (scalarWalsh f) ε = (2 : ℝ)⁻¹ ^ n * f ε := by
  unfold scalarWalsh fourier
  change (Fintype.card (Cube n) : ℝ)⁻¹ *
    (∑ p, fourier f p * character ε p) = _
  simp_rw [character_symm ε]
  rw [fourier_inversion]
  simp [Cube, inv_pow]

theorem scalarWalsh_L2_sq {n : ℕ} (f : Cube n → ℝ) :
    cubeL2 ℝ (scalarWalsh f) ^ 2 = (2 : ℝ)⁻¹ ^ n * cubeL2 ℝ f ^ 2 := by
  rw [cubeL2_sq, cubeL2_sq]
  simp only [Real.norm_eq_abs, sq_abs, scalarWalsh, average, smul_eq_mul]
  rw [parseval]
  simp [average, Cube, inv_pow]

theorem scalarWalsh_L2 {n : ℕ} (f : Cube n → ℝ) :
    cubeL2 ℝ (scalarWalsh f) = Real.sqrt ((2 : ℝ)⁻¹ ^ n) * cubeL2 ℝ f := by
  apply (sq_eq_sq₀ (cubeL2_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (cubeL2_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (by positivity), scalarWalsh_L2_sq]

theorem scalar_rademacher_pairing {n : ℕ} (x y : Fin n → ℝ) :
    average (fun ε => rademacherSum ℝ x ε * rademacherSum ℝ y ε) =
      ∑ i, x i * y i := by
  simp only [rademacherSum, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [average_sum]
  simp_rw [average_sum]
  have he (i j : Fin n) :
      average (fun ε : Cube n => sign (ε i) * x i * (sign (ε j) * y j)) =
        (if i = j then 1 else 0) * (x i * y j) := by
    calc
      _ = average (fun ε : Cube n => (sign (ε i) * sign (ε j)) • (x i * y j)) := by
        congr 1
        funext ε
        simp only [smul_eq_mul]
        ring
      _ = _ := by rw [average_smul_const, coordinate_orthogonality, smul_eq_mul]
  simp_rw [he]
  simp

theorem scalar_rademacher_L2_sq {n : ℕ} (x : Fin n → ℝ) :
    cubeL2 ℝ (rademacherSum ℝ x) ^ 2 = ∑ i, x i ^ 2 := by
  rw [cubeL2_sq]
  simp only [Real.norm_eq_abs, sq_abs]
  simpa only [pow_two] using scalar_rademacher_pairing x x

end Cotype

end

end OAI
