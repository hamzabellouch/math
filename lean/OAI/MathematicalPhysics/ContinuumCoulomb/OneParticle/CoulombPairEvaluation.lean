import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.CoulombEvaluationProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombTargetLipschitz
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalSquareRoot
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PlanarForcingProgram

namespace OAI

/-! Actual direct Coulomb coefficients at arbitrary rational planar sites.
The distance is computed by the certified dyadic square-root program. -/

noncomputable section
namespace ContinuumCoulomb.CoulombPairEvaluation

def lipschitzGuard (rho : ℕ) : ℕ :=
  ⌈localizedCoulombLipschitzConstant (GaussianFrequency.frequency rho)⌉₊+1

theorem lipschitzGuard_positive (rho : ℕ) : 0 < lipschitzGuard rho := by
  unfold lipschitzGuard
  omega

theorem lipschitzGuard_bound (rho : ℕ) :
    localizedCoulombLipschitzConstant (GaussianFrequency.frequency rho) ≤ (lipschitzGuard rho:ℝ) := by
  have h := Nat.le_ceil (localizedCoulombLipschitzConstant (GaussianFrequency.frequency rho))
  unfold lipschitzGuard
  push_cast
  linarith

def precision (P : ℕ) : ℕ := 2*(P+1)
def rootPrecision (rho P : ℕ) : ℕ := 4*lipschitzGuard rho*(P+1)
def squaredDistance (a b : ℚ×ℚ) : ℚ := (a.1-b.1)^2+(a.2-b.2)^2
def distance (rho P : ℕ) (a b : ℚ×ℚ) : ℚ :=
  RationalSquareRoot.value (rootPrecision rho P,squaredDistance a b)
def approximate (rho P : ℕ) (a b : ℚ×ℚ) : ℚ :=
  CoulombEvaluation.approximate rho (precision P) (distance rho P a b)

theorem squaredDistance_cast (a b : ℚ×ℚ) :
    (squaredDistance a b:ℝ) =
      ‖PlanarForcingProgram.position a-PlanarForcingProgram.position b‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [squaredDistance,PlanarForcingProgram.position,PiLp.sub_apply,
    Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    Real.norm_eq_abs,sq_abs,Rat.cast_add,Rat.cast_pow,Rat.cast_sub]

private theorem nat_pow_bound (n : ℕ) : n+1 ≤ 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

theorem distance_error (rho P : ℕ) (a b : ℚ×ℚ) :
    |(distance rho P a b:ℝ)-‖PlanarForcingProgram.position a-PlanarForcingProgram.position b‖| ≤
      ((rootPrecision rho P:ℝ)+1)⁻¹ := by
  have h := RationalSquareRoot.value_error (rootPrecision rho P)
    (show (0:ℚ) ≤ squaredDistance a b from add_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [squaredDistance_cast,Real.sqrt_sq (norm_nonneg _)] at h
  have hb : (2:ℝ)⁻¹^(rootPrecision rho P) ≤ ((rootPrecision rho P:ℝ)+1)⁻¹ := by
    rw [inv_pow]
    apply inv_anti₀ (by positivity)
    exact_mod_cast nat_pow_bound (rootPrecision rho P)
  exact h.trans hb

theorem approximation_error (rho P : ℕ) (hrho : 0 < rho) (a b : ℚ×ℚ) :
    |(approximate rho P a b:ℝ)-localizedCoulombCoeff (GaussianFrequency.frequency rho)
      (PlanarForcingProgram.position a) (PlanarForcingProgram.position b)| ≤ ((P:ℝ)+1)⁻¹ := by
  have hf : 0 < GaussianFrequency.frequency rho := by
    apply Real.sqrt_pos.mpr
    change 0 < 4*Real.pi*(rho:ℝ)
    positivity
  have he := CoulombEvaluation.approximation_error rho (precision P) hrho (distance rho P a b)
  have hd := localizedCoulombProfile_abs_sub hf (distance rho P a b)
    ‖PlanarForcingProgram.position a-PlanarForcingProgram.position b‖
  have hp : (0:ℝ) < (P:ℝ)+1 := by positivity
  have hC : (1:ℝ) ≤ lipschitzGuard rho := by exact_mod_cast lipschitzGuard_positive rho
  have hCp : (0:ℝ) < lipschitzGuard rho := by linarith
  have hmove : localizedCoulombLipschitzConstant (GaussianFrequency.frequency rho) *
      |(distance rho P a b:ℝ)-‖PlanarForcingProgram.position a-PlanarForcingProgram.position b‖| ≤
        (4*((P:ℝ)+1))⁻¹ := by
    apply (mul_le_mul (lipschitzGuard_bound rho) (distance_error rho P a b)
      (abs_nonneg _) hCp.le).trans
    simp only [rootPrecision,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
    apply (mul_inv_le_iff₀ (by positivity)).mpr
    rw [show (4*((P:ℝ)+1))⁻¹*(4*(lipschitzGuard rho:ℝ)*((P:ℝ)+1)+1) =
      (4*(lipschitzGuard rho:ℝ)*((P:ℝ)+1)+1)/(4*((P:ℝ)+1)) by ring]
    exact (le_div_iff₀ (by positivity)).mpr (by nlinarith)
  have heBound : ((precision P:ℝ)+1)⁻¹ ≤ (2*((P:ℝ)+1))⁻¹ := by
    apply inv_anti₀ (by positivity)
    simp only [precision,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
    linarith
  rw [localizedCoulombCoeff_distance]
  have htriangle := abs_sub_le (approximate rho P a b:ℝ)
    (localizedCoulombProfile (GaussianFrequency.frequency rho) (distance rho P a b))
    (localizedCoulombProfile (GaussianFrequency.frequency rho)
      ‖PlanarForcingProgram.position a-PlanarForcingProgram.position b‖)
  apply htriangle.trans
  have hsum := add_le_add (he.trans heBound) (hd.trans hmove)
  apply hsum.trans
  rw [mul_inv,mul_inv]
  norm_num
  nlinarith [inv_pos.mpr hp]

end ContinuumCoulomb.CoulombPairEvaluation

end

end OAI
