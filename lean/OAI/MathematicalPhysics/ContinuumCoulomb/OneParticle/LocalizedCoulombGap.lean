import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedGramSpacing

namespace OAI

/-! The two-site specialization gives the positive denominator `U-v`
used by the Hubbard superexchange calibration. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem localizedCoulombCoeff_gap {freq D : ℝ} (hfreq : 0 < freq) (hD : 5 ≤ D)
    (hleak : 2 * localLeakageBound freq D ≤ localDualMass freq / 2)
    (u v : PlanarPosition) (hsep : D ≤ ‖u - v‖) :
    localizedGramConstant freq ≤ localizedCoulombProfile freq 0 - localizedCoulombCoeff freq u v := by
  let centers : Fin 2 → PlanarPosition := ![u, v]
  let d : Fin 2 → ℝ := ![1, -1]
  have hs : ∀ i j : Fin 2, i ≠ j → D ≤ ‖centers i - centers j‖ := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact hsep
    · change D ≤ ‖v - u‖
      simpa only [norm_sub_rev] using hsep
    · exact False.elim (hij rfl)
  have h := localizedGram_uniform_coercive hfreq hD centers hs (by simpa using hleak) d
  simp only [Fin.sum_univ_two, centers, d, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_pow, neg_one_sq, mul_one, mul_neg, neg_neg] at h
  rw [localizedCoulombCoeff_symmetric hfreq v u,
    localizedCoulombCoeff_distance freq u u, localizedCoulombCoeff_distance freq v v] at h
  simp only [sub_self, norm_zero] at h
  nlinarith only [h]

theorem localizedCoulombProfile_gap {freq D d : ℝ} (hfreq : 0 < freq) (hD : 5 ≤ D)
    (hleak : 2 * localLeakageBound freq D ≤ localDualMass freq / 2) (hd : D ≤ d) :
    localizedGramConstant freq ≤ localizedCoulombProfile freq 0 - localizedCoulombProfile freq d := by
  have hn : ‖(0 : PlanarPosition) - d • planarAxis 0‖ = d := by
    rw [zero_sub, norm_neg, norm_smul, planarAxis_zero_norm,
      Real.norm_of_nonneg (by linarith : 0 ≤ d), mul_one]
  have h := localizedCoulombCoeff_gap hfreq hD hleak 0 (d • planarAxis 0) (by rw [hn]; exact hd)
  rwa [localizedCoulombCoeff_distance, hn] at h

end ContinuumCoulomb

end

end OAI
