import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableWeightedContinuity

namespace OAI

/-! # Weighted-source continuity only on the ball used by the contraction -/

open scoped BoundedContinuousFunction

namespace DefocusingNLS

theorem continuous_stableWeightedPairSource_local
    {P E F W : Type*} [TopologicalSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : P → ℕ → E × F → W)
    (ρ η ε r : ℝ) (hρ : 0 ≤ ρ) (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hr : 0 ≤ r) (hrsmall : 2 * r ≤ 1)
    (hf : ∀ n, Continuous (fun z : P × {v : E × F // ‖v‖ ≤ ρ} => f z.1 n z.2.1))
    (hlip : ∀ p n v w, ‖v‖ ≤ ρ → ‖w‖ ≤ ρ →
      ‖f p n v - f p n w‖ ≤ η * ‖v - w‖)
    (hzero : ∀ p n, ‖f p n 0‖ ≤ ε * r ^ n)
    (x : P → (ℕ →ᵇ E) × (ℕ →ᵇ F)) (hx : ∀ p, ‖x p‖ ≤ ρ)
    (hxc : ∀ n, Continuous (fun p => (x p).1 n))
    (hyc : ∀ n, Continuous (fun p => (x p).2 n)) (n : ℕ) :
    Continuous (fun p => stableWeightedPairSource (f p) ρ η ε r
      hρ hη hε hr hrsmall (hlip p) (hzero p) (x p) n) := by
  let v := fun p => (stableSequenceValue (x p).1 n, stableSequenceValue (x p).2 n)
  have hv : ∀ p, ‖v p‖ ≤ ρ := by
    intro p
    exact stableSequenceValue_norm_le ρ (stablePairSequence (x p))
      ((norm_stablePairSequence_le _).trans (hx p)) n
  have hvc : Continuous v :=
    (continuous_const.smul (hxc n)).prodMk (continuous_const.smul (hyc n))
  have hfc : Continuous (fun p => f p n (v p)) :=
    (hf n).comp (continuous_id.prodMk (hvc.subtype_mk hv))
  have hscale : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have he (p : P) : stableWeightedPairSource (f p) ρ η ε r
      hρ hη hε hr hrsmall (hlip p) (hzero p) (x p) n = (2 : ℝ) ^ n • f p n (v p) := by
    have hh := stableWeightedPairSource_value (f p) ρ η ε r
      hρ hη hε hr hrsmall (hlip p) (hzero p) (x p) (hx p) n
    calc
      _ = ((2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n) •
          stableWeightedPairSource (f p) ρ η ε r
            hρ hη hε hr hrsmall (hlip p) (hzero p) (x p) n := by rw [hscale, one_smul]
      _ = _ := by rw [mul_smul]; exact congrArg ((2 : ℝ) ^ n • ·) hh
  simp_rw [he]
  exact continuous_const.smul hfc

end DefocusingNLS

end OAI
