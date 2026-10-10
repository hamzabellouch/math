import OAI.Probability.BenjaminiSchramm.GhostTiltedTransport

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm

lemma ghostAvoid_mul_mass (h : ℝ) (m : ℝ≥0∞) :
    ghostAvoid h m * m = ENNReal.ofReal (m.toReal * Real.exp (-h * m.toReal)) := by
  by_cases hm : m = ⊤
  · simp [ghostAvoid,hm]
  · rw [ghostAvoid,ite_eq_right hm,← ENNReal.ofReal_toReal hm,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    ring

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma lintegral_ghostAvoid_mass_eq_derivative (p : unitInterval) (x : V)
    {h : ℝ} (hh : 0 < h) :
    (∫⁻ ω, ghostAvoid h (G.quarterTiltedMass ω x) * G.quarterTiltedMass ω x ∂G.law p) =
      ENNReal.ofReal (G.quarterGhostDerivative p x h) := by
  unfold quarterGhostDerivative ghostMagnetizationDerivative
  have hI := (hasDerivAt_ghostMagnetization (G.law p)
    (fun ω => (G.quarterTiltedMass ω x).toReal)
    (G.measurable_quarterTiltedMass x).ennreal_toReal (fun _ => ENNReal.toReal_nonneg) hh).1
  rw [ofReal_integral_eq_lintegral_ofReal hI
    (ae_of_all _ fun ω => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)]
  exact lintegral_congr (fun ω => ghostAvoid_mul_mass h (G.quarterTiltedMass ω x))

end CriticalPercolation.BondGraph

end

end OAI
