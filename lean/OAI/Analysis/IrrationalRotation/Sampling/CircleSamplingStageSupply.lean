import OAI.Analysis.IrrationalRotation.Model.CircleSamplingStage
import OAI.Analysis.IrrationalRotation.Sampling.PrescribedSamplingStage

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace Invariant233

theorem circleSamplingStage_supply {θ : ℝ} (hθ : Irrational θ)
    (j K d q₀ : ℕ) (hj : 0 < j) (hK : 0 < K) (hq₀ : 0 < q₀) :
    ∀ᶠ m : ℕ in atTop, ∀ R : ℝ, Nonempty (CircleSamplingStage θ j K d q₀ m R) := by
  let shift : Fin q₀ → ℝ := fun r => (r.val : ℝ) / q₀
  let width : Fin q₀ → ℝ := fun _ =>
    1 / (((j + 1 : ℕ) : ℝ) ^ 2 * (1 + (d : ℝ)) * q₀)
  have hwidth : ∀ r, 0 < width r := by
    intro r
    dsimp [width]
    positivity
  have hs := TrialSampling.eventually_exists_prescribed_sampling_stage hθ q₀ shift width
    hwidth (ρ := 1 / (j : ℝ)) (by positivity)
  filter_upwards [hs, eventually_ge_atTop K, eventually_ge_atTop (3 : ℕ)]
    with m hms hmK hm3
  intro R
  have hN : 2 < m * K := by nlinarith
  have hNm : m * K ≤ m ^ 2 := by nlinarith
  obtain ⟨samples, hsample, q, hzero, hpos, hstrict, hdiv, hratio, hphases,
    hspread, hnorm⟩ := hms (m * K) hN hNm R q₀ hq₀
  refine ⟨{
    q := q
    samples := samples
    q_zero := hzero
    q_pos := hpos
    q_strict := hstrict
    q_div := hdiv
    q_ratio := hratio
    phases := ?_
    spread := ?_
    samples_nonempty := fun r => (hsample r).1
    samples_positive := fun r => (hsample r).2.2.2.2.1
    samples_range := fun r => (hsample r).2.1
    samples_phase := fun r => (hsample r).2.2.1
    sampling_L2 := hnorm }⟩
  · simpa only [Nat.cast_mul] using hphases
  · simpa only [Nat.cast_mul] using hspread

end Invariant233

end

end OAI
