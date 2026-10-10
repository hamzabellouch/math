import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingFiniteRetention
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingFiniteBudget

namespace OAI

/-! The concrete half-plane observation follows from the proved retained
mass bound and the terminal flag of the actual recorder configuration. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Recorder VelocityDetector Set MeasureTheory
open scoped BigOperators

def accumulatedLoss (ν C σ D K : ℝ) (n : ℕ) : ℝ :=
  ν * ((radius σ D K 0)⁻¹ ^ 2 * C) * 2 +
    ∑ i ∈ Finset.range n, ν * ((radius σ D K i)⁻¹ ^ 2 * C) * duration σ D K i

theorem accumulatedLoss_lt {ν C σ D K : ℝ}
    (hσ : 0 < σ) (hD : 1 ≤ D) (hK : 0 ≤ K) (hc : ν * C ≤ σ * 3000) (n : ℕ) :
    accumulatedLoss ν C σ D K n < 1 / 24 :=
  finite_diffusion_loss_lt hσ hD hK hc n

theorem configurationCenter_terminal (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ) (σ D K : ℝ) (n : ℕ)
    (U : Configuration (State M) (Alphabet M))
    (hU : haltingControl (finiteMachine M hM) U.control = true) :
    configurationCenter M hM blank m σ D K n U 1 = 16 * radius σ D K n := by
  simp only [configurationCenter, hU, ↓reduceIte, Matrix.cons_val_one, Matrix.cons_val_zero]

theorem configurationCenter_nonterminal (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ) (σ D K : ℝ) (n : ℕ)
    (U : Configuration (State M) (Alphabet M))
    (hU : haltingControl (finiteMachine M hM) U.control = false) :
    configurationCenter M hM blank m σ D K n U 1 = -(16 * radius σ D K n) := by
  simp only [configurationCenter, hU, Bool.false_eq_true, ↓reduceIte,
    Matrix.cons_val_one, Matrix.cons_val_zero]

theorem retained_terminal_observation (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    {ν C σ D K : ℝ} (hσ : 0 < σ) (hD : 1 ≤ D) (hK : 0 ≤ K)
    (hc : ν * C ≤ σ * 3000) (n : ℕ)
    (U : Configuration (State M) (Alphabet M))
    (hU : haltingControl (finiteMachine M hM) U.control = true)
    {ρ : Plane → ℝ} (hi : Integrable ρ) (hn : ∀ x, 0 ≤ ρ x) (hmass : (∫ x, ρ x) = 1)
    (hr : 1 - accumulatedLoss ν C σ D K n ≤
      ∫ x, concentrationCutoff (radius σ D K n)
        (configurationCenter M hM blank m σ D K n U) x * ρ x) :
    1 / 2 < ∫ x in upperHalfPlane, ρ x := by
  have hR := radius_pos hσ hD hK n
  apply concentration_terminal_observer hi hn hR
    (δ := accumulatedLoss ν C σ D K n)
    (c := configurationCenter M hM blank m σ D K n U)
  · rw [configurationCenter_terminal M hM blank m σ D K n U hU]
    linarith
  · exact hmass
  · linarith [accumulatedLoss_lt hσ hD hK hc n]
  · simpa only [hmass] using hr


theorem accumulatedLoss_partial_le {ν C σ D K b : ℝ}
    (hν : 0 ≤ ν) (hC : 0 ≤ C) (n : ℕ)
    (hb : b ≤ stageStart σ D K (n + 1)) :
    accumulatedLoss ν C σ D K n +
      ν * ((radius σ D K n)⁻¹ ^ 2 * C) * (b - stageStart σ D K n) ≤
      accumulatedLoss ν C σ D K (n + 1) := by
  have hc : 0 ≤ ν * ((radius σ D K n)⁻¹ ^ 2 * C) := by positivity
  have ht : b - stageStart σ D K n ≤ duration σ D K n := by
    rw [stageStart_succ] at hb
    linarith
  have he := mul_le_mul_of_nonneg_left ht hc
  simp only [accumulatedLoss, Finset.sum_range_succ]
  linarith

theorem initialLoss_partial_le {ν C σ D K b : ℝ}
    (hν : 0 ≤ ν) (hC : 0 ≤ C) (hb : b ≤ 2) :
    ν * ((radius σ D K 0)⁻¹ ^ 2 * C) * b ≤ accumulatedLoss ν C σ D K 0 := by
  have hc : 0 ≤ ν * ((radius σ D K 0)⁻¹ ^ 2 * C) := by positivity
  simpa only [accumulatedLoss, Finset.range_zero, Finset.sum_empty, add_zero] using
    mul_le_mul_of_nonneg_left hb hc


end ForcedComputation.ExpandingDetector

end

end OAI
