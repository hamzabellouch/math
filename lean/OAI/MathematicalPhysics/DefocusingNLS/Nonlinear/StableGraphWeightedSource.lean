import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphSelection

namespace OAI

/-! # Endpoint remainders define bounded weighted sequence sources

The zero-data remainder decays geometrically along the expanding radii.
Pointwise Lipschitz bounds on a small state ball therefore give a bounded
Lipschitz map on the weighted sequence ball.  The extension outside that
ball is used only to supply a total function to the local contraction.
-/

open scoped BoundedContinuousFunction

namespace DefocusingNLS

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem stableSequenceValue_norm_le (ρ : ℝ) (x : ℕ →ᵇ V) (hx : ‖x‖ ≤ ρ) (n : ℕ) :
    ‖stableSequenceValue x n‖ ≤ ρ := by
  apply (norm_stableSequenceValue_le x n).trans
  exact (mul_le_mul_of_nonneg_right
    (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1))
    (norm_nonneg x)).trans (by simpa using hx)

noncomputable def stableWeightedSourceTerm (f : ℕ → V → W) (x : ℕ →ᵇ V) (n : ℕ) : W :=
  (2 : ℝ) ^ n • f n (stableSequenceValue x n)

theorem stableWeightedSourceTerm_bound (f : ℕ → V → W)
    (ρ η ε r : ℝ) (hρ : 0 ≤ ρ) (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hr : 0 ≤ r) (hrsmall : 2 * r ≤ 1)
    (hlip : ∀ n v w, ‖v‖ ≤ ρ → ‖w‖ ≤ ρ → ‖f n v - f n w‖ ≤ η * ‖v - w‖)
    (hzero : ∀ n, ‖f n 0‖ ≤ ε * r ^ n)
    (x : ℕ →ᵇ V) (hx : ‖x‖ ≤ ρ) (n : ℕ) :
    ‖stableWeightedSourceTerm f x n‖ ≤ η * ‖x‖ + ε := by
  have hv := stableSequenceValue_norm_le ρ x hx n
  have hf : ‖f n (stableSequenceValue x n)‖ ≤
      η * ‖stableSequenceValue x n‖ + ε * r ^ n := by
    calc
      _ = ‖(f n (stableSequenceValue x n) - f n 0) + f n 0‖ := by congr 1; abel
      _ ≤ ‖f n (stableSequenceValue x n) - f n 0‖ + ‖f n 0‖ := norm_add_le _ _
      _ ≤ η * ‖stableSequenceValue x n‖ + ε * r ^ n :=
        add_le_add (by simpa using hlip n _ 0 hv (by simpa using hρ)) (hzero n)
  have hcancel : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
  unfold stableWeightedSourceTerm
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (2 : ℝ) ^ n * (η * ‖stableSequenceValue x n‖ + ε * r ^ n) :=
      mul_le_mul_of_nonneg_left hf (by positivity)
    _ ≤ (2 : ℝ) ^ n * (η * ((1 / 2 : ℝ) ^ n * ‖x‖) + ε * r ^ n) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left (norm_stableSequenceValue_le x n) hη) le_rfl) (by positivity)
    _ = η * ‖x‖ * ((2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n) +
        (2 : ℝ) ^ n * (ε * r ^ n) := by ring
    _ = η * ‖x‖ + (2 : ℝ) ^ n * (ε * r ^ n) := by rw [hcancel, mul_one]
    _ ≤ η * ‖x‖ + ε := add_le_add le_rfl
      (stableSequence_geometric_source_bound ε r hε hr hrsmall n)

theorem stableWeightedSourceTerm_dist_le (f : ℕ → V → W)
    (ρ η : ℝ) (hη : 0 ≤ η)
    (hlip : ∀ n v w, ‖v‖ ≤ ρ → ‖w‖ ≤ ρ → ‖f n v - f n w‖ ≤ η * ‖v - w‖)
    (x y : ℕ →ᵇ V) (hx : ‖x‖ ≤ ρ) (hy : ‖y‖ ≤ ρ) (n : ℕ) :
    dist (stableWeightedSourceTerm f x n) (stableWeightedSourceTerm f y n) ≤
      η * dist x y := by
  have hf := hlip n _ _ (stableSequenceValue_norm_le ρ x hx n)
    (stableSequenceValue_norm_le ρ y hy n)
  have hv : ‖stableSequenceValue x n - stableSequenceValue y n‖ ≤
      (1 / 2 : ℝ) ^ n * dist x y := by
    rw [stableSequenceValue, stableSequenceValue, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (by positivity), ← dist_eq_norm]
    exact mul_le_mul_of_nonneg_left (BoundedContinuousFunction.dist_coe_le_dist n) (by positivity)
  have hcancel : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
  rw [dist_eq_norm]
  unfold stableWeightedSourceTerm
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (2 : ℝ) ^ n * (η * ‖stableSequenceValue x n - stableSequenceValue y n‖) :=
      mul_le_mul_of_nonneg_left hf (by positivity)
    _ ≤ (2 : ℝ) ^ n * (η * ((1 / 2 : ℝ) ^ n * dist x y)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv hη) (by positivity)
    _ = η * dist x y * ((2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n) := by ring
    _ = η * dist x y := by rw [hcancel, mul_one]

noncomputable def stableWeightedSource (f : ℕ → V → W)
    (ρ η ε r : ℝ) (hρ : 0 ≤ ρ) (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hr : 0 ≤ r) (hrsmall : 2 * r ≤ 1)
    (hlip : ∀ n v w, ‖v‖ ≤ ρ → ‖w‖ ≤ ρ → ‖f n v - f n w‖ ≤ η * ‖v - w‖)
    (hzero : ∀ n, ‖f n 0‖ ≤ ε * r ^ n) (x : ℕ →ᵇ V) : ℕ →ᵇ W :=
  if hx : ‖x‖ ≤ ρ then
    BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (stableWeightedSourceTerm f x)
      (η * ‖x‖ + ε) (stableWeightedSourceTerm_bound f ρ η ε r hρ hη hε hr hrsmall hlip hzero x hx)
  else 0

theorem stableWeightedSource_norm_le (f : ℕ → V → W)
    (ρ η ε r : ℝ) (hρ : 0 ≤ ρ) (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hr : 0 ≤ r) (hrsmall : 2 * r ≤ 1)
    (hlip : ∀ n v w, ‖v‖ ≤ ρ → ‖w‖ ≤ ρ → ‖f n v - f n w‖ ≤ η * ‖v - w‖)
    (hzero : ∀ n, ‖f n 0‖ ≤ ε * r ^ n) (x : ℕ →ᵇ V) (hx : ‖x‖ ≤ ρ) :
    ‖stableWeightedSource f ρ η ε r hρ hη hε hr hrsmall hlip hzero x‖ ≤ η * ‖x‖ + ε := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).2
  intro n
  simpa only [stableWeightedSource, dite_eq_left hx,
    BoundedContinuousFunction.coe_ofNormedAddCommGroupDiscrete] using
    stableWeightedSourceTerm_bound f ρ η ε r hρ hη hε hr hrsmall hlip hzero x hx n

theorem stableWeightedSource_dist_le (f : ℕ → V → W)
    (ρ η ε r : ℝ) (hρ : 0 ≤ ρ) (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hr : 0 ≤ r) (hrsmall : 2 * r ≤ 1)
    (hlip : ∀ n v w, ‖v‖ ≤ ρ → ‖w‖ ≤ ρ → ‖f n v - f n w‖ ≤ η * ‖v - w‖)
    (hzero : ∀ n, ‖f n 0‖ ≤ ε * r ^ n) (x y : ℕ →ᵇ V)
    (hx : ‖x‖ ≤ ρ) (hy : ‖y‖ ≤ ρ) :
    dist (stableWeightedSource f ρ η ε r hρ hη hε hr hrsmall hlip hzero x)
      (stableWeightedSource f ρ η ε r hρ hη hε hr hrsmall hlip hzero y) ≤ η * dist x y := by
  apply (BoundedContinuousFunction.dist_le (mul_nonneg hη dist_nonneg)).2
  intro n
  simpa only [stableWeightedSource, dite_eq_left hx, dite_eq_left hy,
    BoundedContinuousFunction.coe_ofNormedAddCommGroupDiscrete] using
    stableWeightedSourceTerm_dist_le f ρ η hη hlip x y hx hy n

section Pair

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- Package the stable and unstable weighted coordinates into one sequence. -/
noncomputable def stablePairSequence (x : (ℕ →ᵇ E) × (ℕ →ᵇ F)) : ℕ →ᵇ E × F :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun n => (x.1 n, x.2 n)) ‖x‖
    (fun n => by
      change max ‖x.1 n‖ ‖x.2 n‖ ≤ ‖x‖
      exact max_le ((x.1.norm_coe_le_norm n).trans (norm_fst_le x))
        ((x.2.norm_coe_le_norm n).trans (norm_snd_le x)))

theorem norm_stablePairSequence_le (x : (ℕ →ᵇ E) × (ℕ →ᵇ F)) :
    ‖stablePairSequence x‖ ≤ ‖x‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg x)).2
  intro n
  change max ‖x.1 n‖ ‖x.2 n‖ ≤ ‖x‖
  exact max_le ((x.1.norm_coe_le_norm n).trans (norm_fst_le x))
    ((x.2.norm_coe_le_norm n).trans (norm_snd_le x))

theorem stablePairSequence_dist_le (x y : (ℕ →ᵇ E) × (ℕ →ᵇ F)) :
    dist (stablePairSequence x) (stablePairSequence y) ≤ dist x y := by
  apply (BoundedContinuousFunction.dist_le dist_nonneg).2
  intro n
  change max (dist (x.1 n) (y.1 n)) (dist (x.2 n) (y.2 n)) ≤ dist x y
  exact max_le
    ((BoundedContinuousFunction.dist_coe_le_dist n).trans (le_max_left _ _))
    ((BoundedContinuousFunction.dist_coe_le_dist n).trans (le_max_right _ _))

end Pair

end DefocusingNLS

end OAI
