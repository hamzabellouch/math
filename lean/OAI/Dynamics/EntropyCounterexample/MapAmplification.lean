import OAI.Dynamics.EntropyCounterexample.MapData

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem concrete_prediction_independent (L M : ℝ) (hL : 2 < L) (hM : 2 < M) :
    prediction (concreteData L hL) = prediction (concreteData M hM) := rfl

theorem concrete_predictedClock_independent (L M : ℝ) (hL : 2 < L) (hM : 2 < M)
    (m : ℕ) (t : ℝ) (z : Sphere) :
    predictedClock (concreteData L hL) m t z =
      predictedClock (concreteData M hM) m t z := rfl

def amplificationAbove (B : ℝ) : ℝ := max B 2 + 1

theorem two_lt_amplificationAbove (B : ℝ) : 2 < amplificationAbove B := by
  have := le_max_right B (2 : ℝ)
  unfold amplificationAbove
  linarith

theorem lt_amplificationAbove (B : ℝ) : B < amplificationAbove B := by
  have := le_max_left B (2 : ℝ)
  unfold amplificationAbove
  linarith

theorem amplificationAbove_pos (B : ℝ) : 0 < amplificationAbove B :=
  lt_trans (by norm_num) (two_lt_amplificationAbove B)

theorem geometric_ratio_lt_one (B : ℝ) : B / amplificationAbove B < 1 :=
  (div_lt_one (amplificationAbove_pos B)).2 (lt_amplificationAbove B)

theorem angular_ratio_lt_one (B : ℝ) : (2 : ℝ) / amplificationAbove B < 1 :=
  (div_lt_one (amplificationAbove_pos B)).2 (two_lt_amplificationAbove B)

end Problem340.Construction

end

end OAI
