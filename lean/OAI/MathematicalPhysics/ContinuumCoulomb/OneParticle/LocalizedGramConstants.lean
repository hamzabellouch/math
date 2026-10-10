import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedGram

namespace OAI

/-! A fixed positive coercivity constant once the total off-site leakage is
at most half the common diagonal dual mass. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def localizedGramConstant (freq : ℝ) : ℝ :=
  localDualMass freq ^ 2 / (4 * localDualEnergyBound)

theorem localizedGramConstant_positive {freq : ℝ} (hfreq : 0 < freq) :
    0 < localizedGramConstant freq :=
  div_pos (sq_pos_of_pos (localDualMass_positive hfreq))
    (mul_pos (by norm_num) localDualEnergyBound_positive)

theorem localizedGram_uniform_coercive {freq D : ℝ} (hfreq : 0 < freq) (hD : 5 ≤ D)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖)
    (hleak : m * localLeakageBound freq D ≤ localDualMass freq / 2) (d : Fin m → ℝ) :
    localizedGramConstant freq * ∑ i, d i ^ 2 ≤
      ∑ i, ∑ j, localizedCoulombCoeff freq (u i) (u j) * d i * d j := by
  have ha := localDualMass_positive hfreq
  have hb : localDualMass freq / 2 ≤ localDualMass freq - m * localLeakageBound freq D := by linarith
  have hmargin : 0 ≤ localDualMass freq - m * localLeakageBound freq D := by linarith
  have hs := (sq_le_sq₀ (by positivity : 0 ≤ localDualMass freq / 2) hmargin).mpr hb
  have hc : localizedGramConstant freq ≤
      (localDualMass freq - m * localLeakageBound freq D) ^ 2 / localDualEnergyBound := by
    calc
      _ = (localDualMass freq / 2) ^ 2 / localDualEnergyBound := by
        unfold localizedGramConstant
        ring
      _ ≤ _ := div_le_div_of_nonneg_right hs localDualEnergyBound_positive.le
  exact (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg (fun i _ => sq_nonneg (d i)))).trans
    (localizedGram_coercive hfreq hD u hsep hmargin d)

end ContinuumCoulomb

end

end OAI
