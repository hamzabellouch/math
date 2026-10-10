import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphPointSources

namespace OAI

/-! # Coordinate continuity of the actual weighted point sources -/

open scoped BoundedContinuousFunction

namespace DefocusingNLS

theorem continuous_stableWeightedPairSource_coordinate
    {P E F W : Type*} [TopologicalSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : P → ℕ → E × F → W)
    (hf : ∀ n, Continuous (fun z : P × (E × F) => f z.1 n z.2))
    (ρ η ε r : ℝ) (hρ : 0 ≤ ρ) (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hr : 0 ≤ r) (hrsmall : 2 * r ≤ 1)
    (hlip : ∀ p n v w, ‖v‖ ≤ ρ → ‖w‖ ≤ ρ →
      ‖f p n v - f p n w‖ ≤ η * ‖v - w‖)
    (hzero : ∀ p n, ‖f p n 0‖ ≤ ε * r ^ n)
    (x : P → (ℕ →ᵇ E) × (ℕ →ᵇ F)) (hx : ∀ p, ‖x p‖ ≤ ρ)
    (hxc : ∀ n, Continuous (fun p => (x p).1 n))
    (hyc : ∀ n, Continuous (fun p => (x p).2 n)) (n : ℕ) :
    Continuous (fun p => stableWeightedPairSource (f p) ρ η ε r
      hρ hη hε hr hrsmall (hlip p) (hzero p) (x p) n) := by
  have hscale : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have he (p : P) : stableWeightedPairSource (f p) ρ η ε r
      hρ hη hε hr hrsmall (hlip p) (hzero p) (x p) n =
      (2 : ℝ) ^ n • f p n ((1 / 2 : ℝ) ^ n • (x p).1 n, (1 / 2 : ℝ) ^ n • (x p).2 n) := by
    have hv := stableWeightedPairSource_value (f p) ρ η ε r
      hρ hη hε hr hrsmall (hlip p) (hzero p) (x p) (hx p) n
    calc
      _ = ((2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n) •
          stableWeightedPairSource (f p) ρ η ε r
            hρ hη hε hr hrsmall (hlip p) (hzero p) (x p) n := by rw [hscale, one_smul]
      _ = _ := by rw [mul_smul]; exact congrArg ((2 : ℝ) ^ n • ·) hv
  simp_rw [he]
  exact continuous_const.smul ((hf n).comp (continuous_id.prodMk
    ((continuous_const.smul (hxc n)).prodMk (continuous_const.smul (hyc n)))))

end DefocusingNLS

end OAI
