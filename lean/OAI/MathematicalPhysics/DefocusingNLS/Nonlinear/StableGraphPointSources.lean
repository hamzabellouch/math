import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphSourceIdentity
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphFrameBounds

namespace OAI

/-! # The actual projected point sources on weighted pair sequences

These definitions package the nonlinear remainder and the linear coordinate
commutation defect. The extension is only outside the fixed sequence ball;
inside that ball their values are exactly the endpoint sources.
-/

open scoped BoundedContinuousFunction

namespace DefocusingNLS

variable {E F W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

noncomputable def stableWeightedPairSource (f : ℕ → E × F → W)
    (ρ η ε r : ℝ) (hρ : 0 ≤ ρ) (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hr : 0 ≤ r) (hrsmall : 2 * r ≤ 1)
    (hlip : ∀ n v w, ‖v‖ ≤ ρ → ‖w‖ ≤ ρ → ‖f n v - f n w‖ ≤ η * ‖v - w‖)
    (hzero : ∀ n, ‖f n 0‖ ≤ ε * r ^ n)
    (x : (ℕ →ᵇ E) × (ℕ →ᵇ F)) : ℕ →ᵇ W :=
  stableWeightedSource f ρ η ε r hρ hη hε hr hrsmall hlip hzero (stablePairSequence x)

theorem stableWeightedPairSource_dist_le (f : ℕ → E × F → W)
    (ρ η ε r : ℝ) (hρ : 0 ≤ ρ) (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hr : 0 ≤ r) (hrsmall : 2 * r ≤ 1)
    (hlip : ∀ n v w, ‖v‖ ≤ ρ → ‖w‖ ≤ ρ → ‖f n v - f n w‖ ≤ η * ‖v - w‖)
    (hzero : ∀ n, ‖f n 0‖ ≤ ε * r ^ n)
    (x y : (ℕ →ᵇ E) × (ℕ →ᵇ F)) (hx : ‖x‖ ≤ ρ) (hy : ‖y‖ ≤ ρ) :
    dist (stableWeightedPairSource f ρ η ε r hρ hη hε hr hrsmall hlip hzero x)
      (stableWeightedPairSource f ρ η ε r hρ hη hε hr hrsmall hlip hzero y) ≤ η * dist x y := by
  exact (stableWeightedSource_dist_le f ρ η ε r hρ hη hε hr hrsmall hlip hzero
    _ _ ((norm_stablePairSequence_le x).trans hx) ((norm_stablePairSequence_le y).trans hy)).trans
      (mul_le_mul_of_nonneg_left (stablePairSequence_dist_le x y) hη)

theorem stableWeightedPairSource_zero_bound (f : ℕ → E × F → W)
    (ρ η ε r : ℝ) (hρ : 0 ≤ ρ) (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hr : 0 ≤ r) (hrsmall : 2 * r ≤ 1)
    (hlip : ∀ n v w, ‖v‖ ≤ ρ → ‖w‖ ≤ ρ → ‖f n v - f n w‖ ≤ η * ‖v - w‖)
    (hzero : ∀ n, ‖f n 0‖ ≤ ε * r ^ n) :
    ‖stableWeightedPairSource f ρ η ε r hρ hη hε hr hrsmall hlip hzero 0‖ ≤ ε := by
  have hz : ‖stablePairSequence (0 : (ℕ →ᵇ E) × (ℕ →ᵇ F))‖ = 0 :=
    le_antisymm (by simpa using norm_stablePairSequence_le (0 : (ℕ →ᵇ E) × (ℕ →ᵇ F)))
      (norm_nonneg _)
  have hh := stableWeightedSource_norm_le f ρ η ε r hρ hη hε hr hrsmall hlip hzero
    (stablePairSequence (0 : (ℕ →ᵇ E) × (ℕ →ᵇ F))) (by rw [hz]; exact hρ)
  simpa only [stableWeightedPairSource, hz, mul_zero, zero_add] using hh

theorem stableWeightedPairSource_value (f : ℕ → E × F → W)
    (ρ η ε r : ℝ) (hρ : 0 ≤ ρ) (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hr : 0 ≤ r) (hrsmall : 2 * r ≤ 1)
    (hlip : ∀ n v w, ‖v‖ ≤ ρ → ‖w‖ ≤ ρ → ‖f n v - f n w‖ ≤ η * ‖v - w‖)
    (hzero : ∀ n, ‖f n 0‖ ≤ ε * r ^ n)
    (x : (ℕ →ᵇ E) × (ℕ →ᵇ F)) (hx : ‖x‖ ≤ ρ) (n : ℕ) :
    stableSequenceValue
        (stableWeightedPairSource f ρ η ε r hρ hη hε hr hrsmall hlip hzero x) n =
      f n (stableSequenceValue x.1 n, stableSequenceValue x.2 n) := by
  simpa only [stableWeightedPairSource, stablePairSequence_value] using stableWeightedSource_value
    f ρ η ε r hρ hη hε hr hrsmall hlip hzero (stablePairSequence x)
      ((norm_stablePairSequence_le x).trans hx) n

noncomputable def stableFrameForwardSource
    (ζ : ℕ → F →L[ℝ] E) (π : ℕ → E →L[ℝ] F) (h : ℕ → E → E)
    (n : ℕ) (v : E × F) : E :=
  stableFrameProjection (ζ (n + 1)) (π (n + 1)) (h n (stableFrameAssembly (ζ n) v))

noncomputable def stableFrameCoordinateSource
    (ζ : ℕ → F →L[ℝ] E) (π : ℕ → E →L[ℝ] F)
    (A : ℕ → E →L[ℝ] E) (D : F →L[ℝ] F) (h : ℕ → E → E)
    (n : ℕ) (v : E × F) : F :=
  ((π (n + 1)).comp (A n) - D.comp (π n)) (stableFrameAssembly (ζ n) v) +
    π (n + 1) (h n (stableFrameAssembly (ζ n) v))

theorem stableFrameForwardSource_value
    (ζ : ℕ → F →L[ℝ] E) (π : ℕ → E →L[ℝ] F) (h : ℕ → E → E)
    (x : (ℕ →ᵇ E) × (ℕ →ᵇ F)) (n : ℕ) :
    stableFrameForwardSource ζ π h n (stableSequenceValue x.1 n, stableSequenceValue x.2 n) =
      stableFrameProjection (ζ (n + 1)) (π (n + 1))
        (h n (stableFrameState ζ (stableSequenceValue x.1) (stableSequenceValue x.2) n)) := rfl

theorem stableFrameCoordinateSource_value
    (ζ : ℕ → F →L[ℝ] E) (π : ℕ → E →L[ℝ] F)
    (A : ℕ → E →L[ℝ] E) (D : F →L[ℝ] F) (h : ℕ → E → E)
    (x : (ℕ →ᵇ E) × (ℕ →ᵇ F)) (n : ℕ) :
    stableFrameCoordinateSource ζ π A D h n
        (stableSequenceValue x.1 n, stableSequenceValue x.2 n) =
      ((π (n + 1)).comp (A n) - D.comp (π n))
          (stableFrameState ζ (stableSequenceValue x.1) (stableSequenceValue x.2) n) +
        π (n + 1)
          (h n (stableFrameState ζ (stableSequenceValue x.1) (stableSequenceValue x.2) n)) := rfl

theorem stableFramePointSources_lipschitz
    (ζ : ℕ → F →L[ℝ] E) (π : ℕ → E →L[ℝ] F)
    (A : ℕ → E →L[ℝ] E) (D : F →L[ℝ] F) (h : ℕ → E → E)
    (Cζ CP Cπ τ κ ρ R : ℝ)
    (hCζ : 0 ≤ Cζ) (hCP : 0 ≤ CP) (hCπ : 0 ≤ Cπ)
    (hτ : 0 ≤ τ) (hκ : 0 ≤ κ)
    (hζ : ∀ n, ‖ζ n‖ ≤ Cζ)
    (hP : ∀ n, ‖stableFrameProjection (ζ (n + 1)) (π (n + 1))‖ ≤ CP)
    (hπ : ∀ n, ‖π (n + 1)‖ ≤ Cπ)
    (he : ∀ n, ‖(π (n + 1)).comp (A n) - D.comp (π n)‖ ≤ τ)
    (hball : (1 + Cζ) * ρ ≤ R)
    (hh : ∀ n v w, ‖v‖ ≤ R → ‖w‖ ≤ R → ‖h n v - h n w‖ ≤ κ * ‖v - w‖)
    (n : ℕ) (v w : E × F) (hv : ‖v‖ ≤ ρ) (hw : ‖w‖ ≤ ρ) :
    ‖stableFrameForwardSource ζ π h n v - stableFrameForwardSource ζ π h n w‖ ≤
        CP * κ * (1 + Cζ) * ‖v - w‖ ∧
      ‖stableFrameCoordinateSource ζ π A D h n v -
          stableFrameCoordinateSource ζ π A D h n w‖ ≤
        (τ + Cπ * κ) * (1 + Cζ) * ‖v - w‖ := by
  simpa only [stableFrameForwardSource, stableFrameCoordinateSource, one_smul, one_mul]
    using stableGraph_split_source_lipschitz (stableFrameAssembly (ζ n))
      (stableFrameProjection (ζ (n + 1)) (π (n + 1))) (π (n + 1))
      ((π (n + 1)).comp (A n) - D.comp (π n)) (h n)
      (1 + Cζ) CP Cπ τ κ 1 ρ R (by positivity) hCP hCπ hτ hκ (by norm_num)
      (stableFrameAssembly_norm_le (ζ n) Cζ hCζ (hζ n)) (hP n) (hπ n) (he n)
      hball (hh n) v w hv hw

theorem stableFramePointSources_zero
    (ζ : ℕ → F →L[ℝ] E) (π : ℕ → E →L[ℝ] F)
    (A : ℕ → E →L[ℝ] E) (D : F →L[ℝ] F) (h : ℕ → E → E)
    (CP Cπ ε r : ℝ) (hCP : 0 ≤ CP) (hCπ : 0 ≤ Cπ)
    (hP : ∀ n, ‖stableFrameProjection (ζ (n + 1)) (π (n + 1))‖ ≤ CP)
    (hπ : ∀ n, ‖π (n + 1)‖ ≤ Cπ)
    (hh : ∀ n, ‖h n 0‖ ≤ ε * r ^ n) (n : ℕ) :
    ‖stableFrameForwardSource ζ π h n 0‖ ≤ (CP * ε) * r ^ n ∧
      ‖stableFrameCoordinateSource ζ π A D h n 0‖ ≤ (Cπ * ε) * r ^ n := by
  simpa only [stableFrameForwardSource, stableFrameCoordinateSource, one_smul, one_mul,
    mul_assoc] using stableGraph_split_source_zero (stableFrameAssembly (ζ n))
      (stableFrameProjection (ζ (n + 1)) (π (n + 1))) (π (n + 1))
      ((π (n + 1)).comp (A n) - D.comp (π n)) (h n)
      CP Cπ 1 (ε * r ^ n) hCP hCπ (by norm_num) (hP n) (hπ n) (hh n)

end DefocusingNLS

end OAI
