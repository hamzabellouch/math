import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingNonprincipalObservation

namespace OAI

/-! # Dissipative energy with a compact physical observation on large tori -/

open Filter Topology MeasureTheory

namespace DefocusingNLS

local notation "T" => UnitAddTorus (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}
noncomputable local instance energyObservationMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance energyObservationProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem exists_expandingEnergy_observation (a Q : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < ((N + 1 : ℕ) : ℝ)) (hQ : 0 ≤ Q)
    (q : Radius → FourierL2) (hqb : ∀ L, ‖q L‖ ≤ Q)
    (hq : ∀ (L : ℕ → Radius), Tendsto (fun n => (L n).1) atTop atTop →
      ExpandingCompactApproximation a (N + 1 : ℕ) ha1 hN
        (fun n => (L n).1) (fun n => (L n).2) (fun n => q (L n)))
    (m : ℕ) (hm : 0 < m) (P : ℝ) (hP : 0 ≤ P)
    (hQB : ∀ (L : Radius) (x : T), ‖expandingUnitTorusFunction a (N + 1 : ℕ) L.1 (q L) x‖ ^ (2 * m) ≤ P)
    (hgap : 0 < (N + 1 : ℕ) + 2 * a - 6 - 2 * ((2 * (m : ℝ) + 1) * P)) :
    ∃ c : ℝ, 0 < c ∧ ∃ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (L : Radius), (n : ℝ) ≤ L.1 → ∀ f : FourierL2,
      -a * ‖expandingLowEnergy a (N + 1 : ℕ) L.1 L.2 f‖ ^ 2 +
        (6 - 2 * a - (N + 1 : ℕ)) * ‖expandingHighEnergy a (N + 1 : ℕ) L.1 L.2 f‖ ^ 2 +
        2 * inner ℝ f (expandingLinearizedPotential a (N + 1 : ℕ) L.1 ha ha1 hN L.2 m (q L) f) ≤
      -c * ‖f‖ ^ 2 + C * ‖expandingPhysicalBall a (N + 1 : ℕ) L.1 n ha ha1 hN L.2 f‖ ^ 2 := by
  let B := (2 * (m : ℝ) + 1) * P
  let g := (N + 1 : ℕ) + 2 * a - 6 - 2 * B
  let γ := min a g
  have hγ : 0 < γ := lt_min ha hgap
  obtain ⟨n, C, hC, herror⟩ := exists_expandingNonprincipal_observation a Q N ha ha1 hN hQ q hqb hq
    m hm P hP hQB (γ / 4) (by positivity)
  refine ⟨γ / 2, half_pos hγ, n, 2 * C, by positivity, ?_⟩
  intro L hL f
  have he := herror L hL f
  have hp := expandingOrderedPrincipal_energy_le a L.1 (N + 1) m L.2
    (expandingUnitTorusFunction a (N + 1 : ℕ) L.1 (q L))
    (expandingUnitTorusFunction a (N + 1 : ℕ) L.1 (q L)).continuous P hP (hQB L) f
  have hnorm := expandingEnergy_norm_sq a (N + 1 : ℕ) L.1 L.2 f
  have hl := mul_nonneg (sub_nonneg.mpr (min_le_left a g))
    (sq_nonneg ‖expandingLowEnergy a (N + 1 : ℕ) L.1 L.2 f‖)
  have hh := mul_nonneg (sub_nonneg.mpr (min_le_right a g))
    (sq_nonneg ‖expandingHighEnergy a (N + 1 : ℕ) L.1 L.2 f‖)
  change 0 ≤ (a - γ) * _ at hl
  change 0 ≤ (g - γ) * _ at hh
  unfold expandingNonprincipalEnergy at he
  dsimp only [B, g] at hh
  nlinarith

end DefocusingNLS

end OAI
