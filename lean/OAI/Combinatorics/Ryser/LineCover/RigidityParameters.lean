import OAI.Combinatorics.Ryser.LineCover.FailureNumerics
import OAI.Combinatorics.Ryser.LineCover.RigidityNumerics

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

open Filter Topology

structure RigidityParameters (D : ℕ) (δ ρ A κ q : ℝ) : Prop where
  q_one : 1 ≤ q
  m_four : 4 ≤ q / 2
  m_h : 4 * ((10 * (D + 1) : ℕ) : ℝ) ≤ q / 2
  m_t : 2 * (logarithmicSampleSize A q : ℝ) ≤ q / 2
  h_t : 10 * (D + 1) ≤ logarithmicSampleSize A q
  r_t : (logarithmicSampleSize A q : ℝ) ≤ q ^ (1 / 2 + κ / 4)
  r_h : 2 * ((10 * (D + 1) : ℕ) : ℝ) ≤ q ^ (1 / 2 + κ / 4)
  n_t : (logarithmicSampleSize A q : ℝ) ≤ ρ * q / 2
  n_h : 2 * ((10 * (D + 1) : ℕ) : ℝ) ≤ ρ * q / 2
  T_one : 1 < q ^ (1 / 2 - κ / 3)
  gap_half : rigidityBudget D κ q / (δ * q) ≤ q / 2
  gap_rho : rigidityBudget D κ q / (δ * q) ≤ ρ * q / 2
  heavy : rigidityBudget D κ q / (q ^ (1 / 2 - κ / 3) - 1) ≤ q ^ (1 + κ)
  low : lowFailureEnvelope D δ A κ q < 1
  high : highFailureEnvelope D δ ρ A κ q < 1
  lineerror : q ^ (1 / 2 + κ / 10) ≤ δ * q / 2

theorem eventually_rigidityParameters (D : ℕ) {δ ρ A κ : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hA : 0 < A) (hκ : 0 < κ)
    (hκsmall : κ ≤ 1 / 10) :
    ∀ᶠ q : ℝ in atTop, RigidityParameters D δ ρ A κ q := by
  have hsizes := eventually_sampling_size_bounds D hA hρ hκ
  have hgaps := eventually_rigidityBudget_div_le_min D hδ hρ hκ hκsmall
  have hheavy := eventually_rigidity_heavy_bounds D hκ hκsmall
  have hlow := eventually_lowFailureEnvelope_lt_one D δ hA hκ
    (show κ ≤ 1 by linarith)
  have hhigh := eventually_highFailureEnvelope_lt_one D δ ρ hA hκ
  have hline := eventually_line_error_le_half hδ hκsmall
  filter_upwards [hsizes, hgaps, hheavy, hlow, hhigh, hline] with
    q hsize hgap hheavyq hlo hhi hlin
  rcases hsize with ⟨hq, hht, hmh, hmt, hrt, hnt⟩
  have hhtR : ((10 * (D + 1) : ℕ) : ℝ) ≤ (logarithmicSampleSize A q : ℝ) := by
    exact_mod_cast hht
  have ht0 : (0 : ℝ) ≤ logarithmicSampleSize A q := Nat.cast_nonneg _
  refine {
    q_one := by linarith
    m_four := by linarith
    m_h := ?_
    m_t := hmt
    h_t := hht
    r_t := by linarith
    r_h := by linarith
    n_t := by linarith
    n_h := by linarith
    T_one := hheavyq.1
    gap_half := hgap.trans (min_le_left _ _)
    gap_rho := hgap.trans (min_le_right _ _)
    heavy := hheavyq.2
    low := hlo
    high := hhi
    lineerror := hlin }
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using hmh

theorem exists_rigidityThreshold (D : ℕ) {δ ρ A κ : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hA : 0 < A) (hκ : 0 < κ)
    (hκsmall : κ ≤ 1 / 10) :
    ∃ Q : ℝ, ∀ q : ℝ, Q ≤ q → RigidityParameters D δ ρ A κ q := by
  exact Filter.eventually_atTop.mp
    (eventually_rigidityParameters D hδ hρ hA hκ hκsmall)

end RyserCoveringCounterexample.LineCover

end

end OAI
