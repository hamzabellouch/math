import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorIteration
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceSpectrum

namespace OAI

/-! Explicit final weight bounds and promise thresholds for the actual
three-stage positive-spin graph. -/

namespace ContinuumCoulomb.MediatorIteration
open scoped BigOperators InnerProductSpace

theorem finalGraph_lower {n r W G : ℕ} (F : Bonds n r) (hW : 0 < W) (hG : 0 < G)
    (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W) (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) :
    ∀ e, (1 / 2 : ℝ) ≤ (finalGraph F W G).weight e := by
  have hW3 : 0 < thirdBound r W G := lt_of_lt_of_le (by norm_num)
    (MediatorParameters.thirdWeight_two_le r W G)
  have hdelta1 : (1 : ℝ) ≤ deltaOne r W G := by
    have hp : 0 < deltaOne r W G := by
      unfold deltaOne MediatorParameters.delta
      exact pow_pos (MediatorParameters.scale_pos r hW hG) 2
    exact_mod_cast hp
  have hdelta3 : (1 : ℝ) ≤ deltaThree r W G := by
    have hp : 0 < deltaThree r W G := by
      unfold deltaThree MediatorParameters.delta
      exact pow_pos (MediatorParameters.scale_pos _ hW3 hG) 2
    exact_mod_cast hp
  apply join_weight_property _ _ (fun J => (1 / 2 : ℝ) ≤ J)
  · intro e
    change (1 / 2 : ℝ) ≤ ((deltaOne r W G : ℚ) : ℝ)
    simpa only [Rat.cast_natCast] using (show (1 / 2 : ℝ) ≤ deltaOne r W G by linarith)
  · apply join_weight_property _ _ (fun J => (1 / 2 : ℝ) ≤ J)
    · intro e
      change (1 / 2 : ℝ) ≤ ((deltaThree r W G : ℚ) : ℝ)
      simpa only [Rat.cast_natCast] using (show (1 / 2 : ℝ) ≤ deltaThree r W G by linarith)
    · intro e
      exact MediatorParameters.spoke_lower_half _ hW3 hG
        (secondPaths_bounds F hW hG hJ hJl (finProdFinEquiv.symm e).1).1

theorem finalGraph_upper {n r W G : ℕ} (F : Bonds n r) (hW : 0 < W) (hG : 0 < G)
    (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W) (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) :
    ∀ e, ((finalGraph F W G).weight e : ℝ) ≤ MediatorParameters.finalWeight r W G := by
  have hW3 : 0 < thirdBound r W G := lt_of_lt_of_le (by norm_num)
    (MediatorParameters.thirdWeight_two_le r W G)
  have hr : r * 2 + r * 2 * 2 = 6 * r := by omega
  have hdelta1 : deltaOne r W G ≤ MediatorParameters.finalWeight r W G := by
    unfold deltaOne MediatorParameters.finalWeight
    omega
  have hdelta3 : deltaThree r W G ≤ MediatorParameters.finalWeight r W G := by
    unfold deltaThree thirdBound
    rw [hr]
    unfold MediatorParameters.finalWeight
    omega
  have hspoke : 2 * MediatorParameters.scale (r * 2 + r * 2 * 2) (thirdBound r W G) G * thirdBound r W G ≤
      MediatorParameters.finalWeight r W G := by
    unfold thirdBound
    rw [hr]
    unfold MediatorParameters.finalWeight
    omega
  apply join_weight_property _ _ (fun J => (J : ℝ) ≤ MediatorParameters.finalWeight r W G)
  · intro e
    change ((deltaOne r W G : ℚ) : ℝ) ≤ _
    exact_mod_cast hdelta1
  · apply join_weight_property _ _ (fun J => (J : ℝ) ≤ MediatorParameters.finalWeight r W G)
    · intro e
      change ((deltaThree r W G : ℚ) : ℝ) ≤ _
      exact_mod_cast hdelta3
    · intro e
      have h := MediatorParameters.spoke_upper (r * 2 + r * 2 * 2) hW3 hG
        (secondPaths_bounds F hW hG hJ hJl (finProdFinEquiv.symm e).1).2
      apply h.trans
      exact_mod_cast hspoke

/-- All final positive weights have bounded reciprocals, uniformly over
the original signed nonzero coefficients. -/
theorem finalGraph_reciprocal {n r W G : ℕ} (F : Bonds n r) (hW : 0 < W) (hG : 0 < G)
    (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W) (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) :
    ∀ e, 1 / ((finalGraph F W G).weight e : ℝ) ≤ 2 := by
  intro e
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2)
    (finalGraph_lower F hW hG hJ hJl e)
  norm_num at h
  simpa only [one_div] using h

def lowerThreshold {n r : ℕ} (F : Bonds n r) (W G : ℕ) (a : ℚ) : ℚ :=
  a - offset F W G + 3 / (512 * (G : ℚ))

def upperThreshold {n r : ℕ} (F : Bonds n r) (W G : ℕ) (b : ℚ) : ℚ :=
  b - offset F W G - 3 / (512 * (G : ℚ))

theorem three_stage_yes {n r W G : ℕ} (F : Bonds n r) (hF : F.NoLoops)
    (hW : 0 < W) (hG : 0 < G) (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W)
    (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) {a : ℚ}
    (hyes : sourceMatrixBottom n F.matrix ≤ a) :
    sourceMatrixBottom (n + r * 2 + r * 2 * 2 + (r * 2 + r * 2 * 2) * 2)
      (finalGraph F W G).matrix ≤ lowerThreshold F W G a := by
  have he := (abs_le.mp (three_stage_bottom F hF hW hG hJ hJl)).2
  simp only [lowerThreshold, Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_mul,
    Rat.cast_ofNat, Rat.cast_natCast]
  linarith

theorem three_stage_no {n r W G : ℕ} (F : Bonds n r) (hF : F.NoLoops)
    (hW : 0 < W) (hG : 0 < G) (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W)
    (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) {b : ℚ}
    (hno : (b : ℝ) ≤ sourceMatrixBottom n F.matrix) :
    (upperThreshold F W G b : ℝ) ≤
      sourceMatrixBottom (n + r * 2 + r * 2 * 2 + (r * 2 + r * 2 * 2) * 2)
        (finalGraph F W G).matrix := by
  have he := (abs_le.mp (three_stage_bottom F hF hW hG hJ hJl)).1
  simp only [upperThreshold, Rat.cast_sub, Rat.cast_div, Rat.cast_mul,
    Rat.cast_ofNat, Rat.cast_natCast]
  linarith

theorem three_stage_threshold_gap {n r W G : ℕ} (F : Bonds n r) {a b : ℚ}
    (hprecision : 1 / (G : ℚ) ≤ b - a) :
    253 / 256 * (b - a) ≤ upperThreshold F W G b - lowerThreshold F W G a := by
  have heq : (3 / (512 * (G : ℚ))) + 3 / (512 * (G : ℚ)) = 3 / 256 * (1 / (G : ℚ)) := by ring
  unfold upperThreshold lowerThreshold
  linarith

end ContinuumCoulomb.MediatorIteration

end OAI
