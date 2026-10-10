import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibratedLipschitzBound

namespace OAI

/-! Polynomial unary iteration and evaluation-precision choices for the
actual calibrated bisection. -/

noncomputable section
namespace ContinuumCoulomb.CalibratedEvaluation

def refinedEnvironment (e : Environment) : Environment :=
  ((e.1.1, 8 * (e.1.2 + 1)), e.2)

def iterations (rho : ℕ) (e : Environment) : ℕ :=
  16 * lipschitzGuard rho * (e.2.1 + e.1.1 + 1) * (e.1.1 + 1) * (e.1.2 + 1)

def scheduledValue (rho : ℕ) (e : Environment) (a b : ℚ) : ℚ :=
  bisect rho (iterations rho e, (refinedEnvironment e, (a, b)))

theorem bisection_scalar_budget {C A N S : ℝ} {n : ℕ}
    (hC : 0 < C) (hA : 0 < A) (hN : 0 ≤ N) (hS : 0 < S)
    (hn : (n : ℝ) = 16 * C * A * (N + 1) * S) :
    2 * (8 * S + 1)⁻¹ + C * A * (2 * N) / 2 ^ n ≤ S⁻¹ := by
  have hn0 : (0 : ℝ) < n := by rw [hn]; positivity
  have hfirst : 2 * (8 * S + 1)⁻¹ ≤ (4 * S)⁻¹ := by
    apply (mul_inv_le_iff₀ (by positivity)).mpr
    apply (le_inv_mul_iff₀ (by positivity : (0 : ℝ) < 4 * S)).mpr
    linarith
  have hsecond : C * A * (2 * N) / 2 ^ n ≤ (8 * S)⁻¹ := by
    calc
      _ = C * A * (2 * N) * (2 : ℝ)⁻¹ ^ n := by rw [div_eq_mul_inv, inv_pow]
      _ ≤ C * A * (2 * N) * ((n : ℝ) + 1)⁻¹ :=
        mul_le_mul_of_nonneg_left (CoulombQuadratureSchedule.dyadic_le_inverse n) (by positivity)
      _ ≤ C * A * (2 * (N + 1)) * (n : ℝ)⁻¹ := by
        apply mul_le_mul
        · gcongr
          linarith
        · exact inv_anti₀ hn0 (by linarith)
        · positivity
        · positivity
      _ = (8 * S)⁻¹ := by
        rw [hn]
        field_simp [hC.ne', hA.ne', hS.ne', ne_of_gt (show 0 < N + 1 by linarith)]
        ring
  have hs := add_le_add hfirst hsecond
  apply hs.trans
  simp only [mul_inv_rev]
  norm_num
  nlinarith [inv_pos.mpr hS]

theorem scheduled_residual (rho : ℕ) (hrho : 0 < rho) (e : Environment) (a b : ℚ)
    (hK : (0 : ℚ) ≤ e.2.2.2) (hKN : (e.2.2.2 : ℝ) ≤ e.1.1)
    (hτ : (0 : ℚ) ≤ e.2.2.1) (hτ1 : e.2.2.1 ≤ 1) (hab : a ≤ b)
    (haN : -(e.1.1 : ℝ) ≤ a) (hbN : (b : ℝ) ≤ e.1.1)
    (ha : 0 ≤ residual rho e a) (hb : residual rho e b ≤ 0)
    (hgap : ∀ r ∈ Set.Icc (a : ℝ) b,
      localizedGramConstant (GaussianFrequency.frequency rho) ≤
        localizedCoulombProfile (GaussianFrequency.frequency rho) 0 -
          localizedCoulombProfile (GaussianFrequency.frequency rho) r) :
    |residual rho e (scheduledValue rho e a b)| ≤ ((e.1.2 : ℝ) + 1)⁻¹ := by
  have hK' : (0 : ℝ) ≤ e.2.2.2 := by exact_mod_cast hK
  have hτ1' : (e.2.2.1 : ℝ) ≤ 1 := by exact_mod_cast hτ1
  have he := bisect_residual rho hrho (refinedEnvironment e) a b
    hK hKN hτ hτ1 hab haN hbN ha hb hgap (iterations rho e)
  have hL := residualLipschitz_bound rho e hK' hKN hτ1'
  have hwidth : (0 : ℝ) ≤ b - a := by exact_mod_cast sub_nonneg.mpr hab
  have hwidth' : (b : ℝ) - a ≤ 2 * (e.1.1 : ℝ) := by linarith
  have hcount : (iterations rho e : ℝ) =
      16 * (lipschitzGuard rho : ℝ) * ((e.2.1 : ℝ) + e.1.1 + 1) *
        ((e.1.1 : ℝ) + 1) * ((e.1.2 : ℝ) + 1) := by
    simp only [iterations, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  have hC : (0 : ℝ) < lipschitzGuard rho := by exact_mod_cast lipschitzGuard_positive rho
  have hA : (0 : ℝ) < (e.2.1 : ℝ) + e.1.1 + 1 := by positivity
  have hbnd := bisection_scalar_budget hC hA (Nat.cast_nonneg e.1.1)
    (show (0 : ℝ) < e.1.2 + 1 by positivity) hcount
  have hterm : residualLipschitz rho e * (((b : ℝ) - a) / 2 ^ iterations rho e) ≤
      (lipschitzGuard rho : ℝ) * ((e.2.1 : ℝ) + e.1.1 + 1) * (2 * (e.1.1 : ℝ)) /
        2 ^ iterations rho e := by
    calc
      _ ≤ ((lipschitzGuard rho : ℝ) * ((e.2.1 : ℝ) + e.1.1 + 1)) *
          (((b : ℝ) - a) / 2 ^ iterations rho e) :=
        mul_le_mul_of_nonneg_right hL (div_nonneg hwidth (by positivity))
      _ ≤ _ := by rw [mul_div_assoc]; gcongr
  have he' : |residual rho e (scheduledValue rho e a b)| ≤
      2 * (8 * ((e.1.2 : ℝ) + 1) + 1)⁻¹ +
        residualLipschitz rho e * (((b : ℝ) - a) / 2 ^ iterations rho e) := by
    simpa only [refinedEnvironment, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
      Nat.cast_one, scheduledValue, residual, residualLipschitz] using he
  exact (he'.trans (add_le_add (le_refl _) hterm)).trans hbnd

end ContinuumCoulomb.CalibratedEvaluation

end

end OAI
