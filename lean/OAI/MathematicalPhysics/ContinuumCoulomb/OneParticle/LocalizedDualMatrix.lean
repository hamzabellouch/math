import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedDuality
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombGramApprox

namespace OAI

/-! Concrete compact bumps supply local duality for the actual mode densities. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

def localDualBump : ContDiffBump (0 : Position) := ⟨1, 2, by norm_num, by norm_num⟩

theorem localDualBump_smooth : ContDiff ℝ ∞ (localDualBump : Position → ℝ) :=
  localDualBump.contDiff

theorem localDualBump_support : tsupport (localDualBump : Position → ℝ) ⊆ Metric.closedBall 0 2 := by
  rw [localDualBump.tsupport_eq]
  exact Set.Subset.rfl

def localDualMass (freq : ℝ) : ℝ :=
  ∫ x, localizedDensity freq 0 x * localDualBump x

theorem localDualMass_positive {freq : ℝ} (hfreq : 0 < freq) : 0 < localDualMass freq := by
  have h0 : localDualBump (0 : Position) = 1 :=
    localDualBump.one_of_mem_closedBall (by simp [localDualBump])
  have h := localizedDualPair_diagonal_positive hfreq 0 localDualBump_smooth.continuous
    localDualBump.hasCompactSupport localDualBump.nonneg' (by rw [h0]; norm_num)
  simpa only [localizedDualPair_diagonal, localDualMass] using h

def localLeakageBound (freq D : ℝ) : ℝ :=
  (localizedTailConstant freq * Real.exp (2 - D)) * (∫ x : Position, |localDualBump x|)

theorem localLeakageBound_nonnegative (freq D : ℝ) : 0 ≤ localLeakageBound freq D :=
  mul_nonneg (mul_nonneg (localizedTailConstant_nonnegative freq) (Real.exp_pos _).le)
    (integral_nonneg (fun _ => abs_nonneg _))

theorem localDualPair_offsite {freq D : ℝ} (hfreq : 0 < freq) (hD : 3 ≤ D)
    (u v : PlanarPosition) (hsep : D ≤ ‖u - v‖) :
    |localizedDualPair freq u v localDualBump| ≤ localLeakageBound freq D := by
  have h := localizedDualPair_offsite hfreq u v localDualBump_smooth.continuous
    localDualBump.hasCompactSupport localDualBump_support (by linarith : (2 : ℝ) + 1 ≤ ‖u - v‖)
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
      (localizedTailConstant_nonnegative freq)) (integral_nonneg (fun _ => abs_nonneg _)))

theorem localDualTests_disjoint {D : ℝ} (hD : 5 ≤ D)
    (u v : PlanarPosition) (hsep : D ≤ ‖u - v‖) :
    Disjoint (tsupport (localizedTest localDualBump u)) (tsupport (localizedTest localDualBump v)) :=
  localizedTest_disjoint localDualBump_support u v (by linarith)

theorem localizedDualMatrix_lower {freq D : ℝ} (hfreq : 0 < freq) (hD : 3 ≤ D)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖)
    (s : Fin m → ℝ) :
    (localDualMass freq - m * localLeakageBound freq D) * ∑ i, s i ^ 2 ≤
      ∑ i, ∑ j, localizedDualPair freq (u i) (u j) localDualBump * s i * s j := by
  apply dualMatrix_quadratic_lower _ (localLeakageBound_nonnegative freq D)
  · intro i
    rw [localizedDualPair_diagonal]
    exact le_rfl
  · intro i j hij
    exact localDualPair_offsite hfreq hD (u i) (u j) (hsep i j hij)

end ContinuumCoulomb

end

end OAI
