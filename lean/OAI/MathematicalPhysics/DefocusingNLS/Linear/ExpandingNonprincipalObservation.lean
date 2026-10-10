import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingNonprincipalEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingQuadraticObservation

namespace OAI

/-! # Uniform compact observation for the actual odd-power energy error -/

open Filter Topology MeasureTheory

namespace DefocusingNLS

local notation "T" => UnitAddTorus (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}
noncomputable local instance nonprincipalObservationMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance nonprincipalObservationProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem exists_expandingNonprincipal_observation (a Q : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < ((N + 1 : ℕ) : ℝ)) (hQ : 0 ≤ Q)
    (q : Radius → FourierL2) (hqb : ∀ L, ‖q L‖ ≤ Q)
    (hq : ∀ (L : ℕ → Radius), Tendsto (fun n => (L n).1) atTop atTop →
      ExpandingCompactApproximation a (N + 1 : ℕ) ha1 hN
        (fun n => (L n).1) (fun n => (L n).2) (fun n => q (L n)))
    (m : ℕ) (hm : 0 < m) (P : ℝ) (hP : 0 ≤ P)
    (hQB : ∀ (L : Radius) (x : T), ‖expandingUnitTorusFunction a (N + 1 : ℕ) L.1 (q L) x‖ ^ (2 * m) ≤ P)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : Radius), (n : ℝ) ≤ L.1 → ∀ f : FourierL2,
      expandingNonprincipalEnergy a L.1 (N + 1) ha ha1 hN L.2 m (q L) P hP (hQB L) f ≤
        ε * ‖f‖ ^ 2 + C *
          ‖expandingPhysicalBall a (N + 1 : ℕ) L.1 n ha ha1 hN L.2 f‖ ^ 2 := by
  let F : Radius → FourierL2 → ℝ := fun L f =>
    expandingNonprincipalEnergy a L.1 (N + 1) ha ha1 hN L.2 m (q L) P hP (hQB L) f
  obtain ⟨D, hD, hDb⟩ := exists_expandingLinearized_norm_bound a (N + 1 : ℕ) Q ha ha1 hN hQ m
  let B := D + (2 * (m : ℝ) + 1) * P
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨n, hn⟩ := exists_expanding_observation_threshold a (N + 1 : ℕ) F (by
    intro L hLinf f hf hlocal
    exact tendsto_expandingCompactEnergy_error a Q 1 N ha ha1 hN
      (fun j => (L j).1) (fun j => (L j).2) hLinf (fun j => q (L j)) (hq L hLinf)
      (fun j => hqb (L j)) f hf hlocal m hm P hP (fun j => hQB (L j))) ε hε
  refine ⟨n, B * ((n : ℝ) + 1) ^ 2, by positivity, ?_⟩
  exact expanding_quadratic_observation_estimate a (N + 1 : ℕ) ha ha1 hN F B hB
    (fun L f => expandingNonprincipalEnergy_le a L.1 (N + 1) ha ha1 hN L.2 m (q L)
      P hP (hQB L) D (hDb L.1 L.2 (q L) (hqb L)) f)
    (fun L c f => expandingNonprincipalEnergy_smul a L.1 (N + 1) ha ha1 hN L.2 m (q L)
      P hP (hQB L) c f) ε hε n hn

end DefocusingNLS

end OAI
