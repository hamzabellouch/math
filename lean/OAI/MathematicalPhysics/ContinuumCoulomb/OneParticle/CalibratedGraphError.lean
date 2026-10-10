import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibrationGraphBudget
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibratedBisectionLocation

namespace OAI

/-! The actual scheduled rational distances produce a finite Hubbard
superexchange graph whose ground energy is close to the requested spin graph.
Only the analytic endpoint signs and separated-site gap are hypotheses. -/

noncomputable section
namespace ContinuumCoulomb.CalibratedEvaluation
open scoped BigOperators

def edgeEnvironment (N P scale : ℕ) (τ K : ℚ) : Environment := ((N, P), (scale, (τ, K)))

def scheduledDistance (rho N P scale : ℕ) (τ K a b : ℚ) : ℚ :=
  scheduledValue rho (edgeEnvironment N P scale τ K) a b

def scheduledCoefficient (rho N P scale : ℕ) (τ K a b : ℚ) : ℝ :=
  ((scale : ℝ) * planarHopping (scheduledDistance rho N P scale τ K a b)) ^ 2 /
    (localizedCoulombProfile (GaussianFrequency.frequency rho) 0 -
      localizedCoulombProfile (GaussianFrequency.frequency rho)
        (scheduledDistance rho N P scale τ K a b))

theorem scheduled_graphSourceBottom_error {Edge : Type*} [Fintype Edge]
    (rho : ℕ) (hrho : 0 < rho) (m : ℕ) (left right : Edge → Fin (m + 1))
    (N P scale : ℕ) (τ : ℚ) (K a b : Edge → ℚ)
    (hK : ∀ e, 0 ≤ K e) (hKN : ∀ e, (K e : ℝ) ≤ N)
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hab : ∀ e, a e ≤ b e)
    (haN : ∀ e, -(N : ℝ) ≤ a e) (hbN : ∀ e, (b e : ℝ) ≤ N)
    (ha : ∀ e, 0 ≤ residual rho (edgeEnvironment N P scale τ (K e)) (a e))
    (hb : ∀ e, residual rho (edgeEnvironment N P scale τ (K e)) (b e) ≤ 0)
    (hgap : ∀ e r, r ∈ Set.Icc (a e : ℝ) (b e) →
      localizedGramConstant (GaussianFrequency.frequency rho) ≤
        localizedCoulombProfile (GaussianFrequency.frequency rho) 0 -
          localizedCoulombProfile (GaussianFrequency.frequency rho) r) :
    |HubbardGlobal.graphSourceBottom m left right
        (fun e => scheduledCoefficient rho N P scale τ (K e) (a e) (b e)) -
      HubbardGlobal.graphSourceBottom m left right (fun e => (τ : ℝ) ^ 2 * K e)| ≤
      4 * Fintype.card Edge *
        (((P : ℝ) + 1)⁻¹ *
          (2 * Real.sqrt ((N : ℝ) * localizedCoulombProfile (GaussianFrequency.frequency rho) 0) +
            ((P : ℝ) + 1)⁻¹) / localizedGramConstant (GaussianFrequency.frequency rho)) := by
  let freq := GaussianFrequency.frequency rho
  let d : Edge → ℚ := fun e => scheduledDistance rho N P scale τ (K e) (a e) (b e)
  let t : Edge → ℝ := fun e => (scale : ℝ) * planarHopping (d e)
  let gap : Edge → ℝ := fun e => localizedCoulombProfile freq 0 - localizedCoulombProfile freq (d e)
  have hfreq : 0 < freq := Real.sqrt_pos.mpr (by
    change 0 < 4 * Real.pi * (rho : ℝ)
    positivity)
  have hmem (e : Edge) : (d e : ℝ) ∈ Set.Icc (a e : ℝ) (b e) := by
    have hm := scheduledValue_mem rho (edgeEnvironment N P scale τ (K e)) (a e) (b e) (hab e)
    exact ⟨by exact_mod_cast hm.1, by exact_mod_cast hm.2⟩
  have hgap' (e : Edge) : localizedGramConstant freq ≤ gap e := hgap e (d e) (hmem e)
  have hU (e : Edge) : gap e ≤ localizedCoulombProfile freq 0 := by
    have hp : 0 ≤ localizedCoulombProfile freq (d e) := by
      unfold localizedCoulombProfile
      rw [localizedCoulombProfileAt_eq]
      exact localizedCoulombCoeff_nonnegative _ _ _
    dsimp only [gap]
    linarith
  have hres (e : Edge) :
      |t e - (τ : ℝ) * Real.sqrt ((K e : ℝ) * gap e)| ≤ ((P : ℝ) + 1)⁻¹ := by
    have hs := scheduled_residual rho hrho (edgeEnvironment N P scale τ (K e))
      (a e) (b e) (hK e) (hKN e) hτ hτ1 (hab e) (haN e) (hbN e) (ha e) (hb e) (hgap e)
    simpa only [residual, coulombHoppingTarget, edgeEnvironment, d, t, gap, freq,
      scheduledDistance] using hs
  have hKr (e : Edge) : (0 : ℝ) ≤ K e := by exact_mod_cast hK e
  have hτr : (0 : ℝ) ≤ τ := by exact_mod_cast hτ
  have hτr1 : (τ : ℝ) ≤ 1 := by exact_mod_cast hτ1
  have h := HubbardGlobal.calibrated_graphSourceBottom_uniform_error m left right
    t (fun e => (K e : ℝ)) gap hKr hKN (localizedGramConstant_positive hfreq)
    hgap' hU hτr hτr1 hres
  simpa only [scheduledCoefficient, scheduledDistance, t, gap, d, freq] using h

end ContinuumCoulomb.CalibratedEvaluation

end

end OAI
