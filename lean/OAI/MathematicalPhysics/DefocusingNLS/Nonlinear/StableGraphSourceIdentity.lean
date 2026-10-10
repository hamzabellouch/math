import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphSplitSource

namespace OAI

/-! # Exact values of the weighted graph sources

The bounded extension used outside the sequence ball has no effect on its
fixed point. Removing the geometric weight recovers the actual pointwise
nonlinear source on that ball.
-/

open scoped BoundedContinuousFunction

namespace DefocusingNLS

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem stableWeightedSource_value (f : ℕ → V → W)
    (ρ η ε r : ℝ) (hρ : 0 ≤ ρ) (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hr : 0 ≤ r) (hrsmall : 2 * r ≤ 1)
    (hlip : ∀ n v w, ‖v‖ ≤ ρ → ‖w‖ ≤ ρ → ‖f n v - f n w‖ ≤ η * ‖v - w‖)
    (hzero : ∀ n, ‖f n 0‖ ≤ ε * r ^ n) (x : ℕ →ᵇ V) (hx : ‖x‖ ≤ ρ) (n : ℕ) :
    stableSequenceValue
        (stableWeightedSource f ρ η ε r hρ hη hε hr hrsmall hlip hzero x) n =
      f n (stableSequenceValue x n) := by
  simp only [stableSequenceValue, stableWeightedSource, dite_eq_left hx,
    BoundedContinuousFunction.coe_ofNormedAddCommGroupDiscrete, stableWeightedSourceTerm,
    smul_smul, ← mul_pow]
  norm_num

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem stablePairSequence_value (x : (ℕ →ᵇ E) × (ℕ →ᵇ F)) (n : ℕ) :
    stableSequenceValue (stablePairSequence x) n =
      (stableSequenceValue x.1 n, stableSequenceValue x.2 n) := rfl

noncomputable def stableFrameAssembly (ζ : F →L[ℝ] E) : E × F →L[ℝ] E :=
  ContinuousLinearMap.fst ℝ E F + ζ.comp (ContinuousLinearMap.snd ℝ E F)

@[simp] theorem stableFrameAssembly_apply (ζ : F →L[ℝ] E) (v : E × F) :
    stableFrameAssembly ζ v = v.1 + ζ v.2 := rfl

theorem stableFrameAssembly_norm_le (ζ : F →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C)
    (hζ : ‖ζ‖ ≤ C) : ‖stableFrameAssembly ζ‖ ≤ 1 + C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  calc
    ‖stableFrameAssembly ζ v‖ ≤ ‖v.1‖ + ‖ζ v.2‖ := norm_add_le _ _
    _ ≤ ‖v‖ + C * ‖v‖ := add_le_add (norm_fst_le v)
      ((ζ.le_opNorm _).trans (mul_le_mul hζ (norm_snd_le v) (norm_nonneg _) hC))
    _ = (1 + C) * ‖v‖ := by ring

end DefocusingNLS

end OAI
