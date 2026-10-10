import OAI.Analysis.KadisonKastler.GraphMomentBounds
import OAI.Analysis.KadisonKastler.FiniteMomentSelection

namespace OAI

/-! # Simultaneous graph signal and clipping-cost selection

The normalized sign sum is passed through an actual real-linear signal
map. A constant orbit signal gives its exact second moment and the
Hilbert fourth-moment bound. Finite selection then retains the signal
and bounds the actual vector-state clipping cost in the same sample.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {I G : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype G] [Nonempty G]

omit [DecidableEq I] [Nonempty I] in
/-- A real-linear signal map commutes with the normalized sign sum. -/
theorem map_normalizedFiniteSignSum (L : (H →L[ℂ] H) →ₗ[ℝ] V)
    (a : I → H →L[ℂ] H) (ε : I → Bool) :
    L (normalizedFiniteSignSum a ε) = normalizedHilbertSignSum (fun i => L (a i)) ε := by
  simp only [normalizedFiniteSignSum, normalizedHilbertSignSum, finiteSignSum,
    hilbertSignSum, map_smul, map_sum]

/-- All sampled summands have the same signal variance. -/
theorem sampled_sign_signal_second (L : (H →L[ℂ] H) →ₗ[ℝ] V)
    (a : G → H →L[ℂ] H) (s : ℝ) (hsignal : ∀ g, ‖L (a g)‖ ^ 2 = s) :
    (𝔼 ω : I → G, 𝔼 ε : I → Bool,
      ‖L (normalizedFiniteSignSum (fun i => a (ω i)) ε)‖ ^ 2) = s := by
  simp_rw [map_normalizedFiniteSignSum, expect_normalizedHilbertSignSum_sq]
  simp only [hsignal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hm : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [← mul_assoc, inv_mul_cancel₀ hm, one_mul, Fintype.expect_const]

/-- The signal fourth moment is controlled independently of the number
of matrix samples. -/
theorem sampled_sign_signal_fourth (L : (H →L[ℂ] H) →ₗ[ℝ] V)
    (a : G → H →L[ℂ] H) (s : ℝ) (hsignal : ∀ g, ‖L (a g)‖ ^ 2 = s) :
    (𝔼 ω : I → G, 𝔼 ε : I → Bool,
      ‖L (normalizedFiniteSignSum (fun i => a (ω i)) ε)‖ ^ 4) ≤ 3 * s ^ 2 := by
  have hm : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hω (ω : I → G) :
      (𝔼 ε : I → Bool,
        ‖L (normalizedFiniteSignSum (fun i => a (ω i)) ε)‖ ^ 4) ≤ 3 * s ^ 2 := by
    simp only [map_normalizedFiniteSignSum]
    have h := expect_normalizedHilbertSignSum_fourth_le (fun i => L (a (ω i)))
    simpa only [hsignal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ hm, one_mul] using h
  calc
    _ ≤ (𝔼 _ω : I → G, 3 * s ^ 2) := Finset.expect_le_expect (fun ω _ => hω ω)
    _ = _ := Fintype.expect_const _

/-- The clipping cost is nonnegative for a nonnegative graph scale. -/
theorem graphMomentCost_nonneg (Ω : H) {k : ℝ} (hk : 0 ≤ k) (x : H →L[ℂ] H) :
    0 ≤ graphMomentCost Ω k x := by
  have hright : realVectorState Ω ((star x * x) ^ 2) = ‖(star x * x) Ω‖ ^ 2 := by
    simpa only [pow_two, star_mul, star_star] using
      realVectorState_star_mul_self Ω (star x * x)
  have hleft : realVectorState Ω ((x * star x) ^ 2) = ‖(x * star x) Ω‖ ^ 2 := by
    simpa only [pow_two, star_mul, star_star] using
      realVectorState_star_mul_self Ω (x * star x)
  have hsecond : realVectorState Ω (x * star x) = ‖star x Ω‖ ^ 2 := by
    simpa only [star_star] using realVectorState_star_mul_self Ω (star x)
  simp only [graphMomentCost, realVectorState_star_mul_self, hright, hleft, hsecond]
  positivity

/-- One actual finite sample simultaneously retains half of the signal
variance and has clipping cost at most 240. -/
theorem exists_sampled_sign_signal_and_cost
    (Ω : H) {k : ℝ} (hk : 0 ≤ k)
    (L : (H →L[ℂ] H) →ₗ[ℝ] V) (a : G → H →L[ℂ] H)
    {s : ℝ} (hs : 0 < s) (hsignal : ∀ g, ‖L (a g)‖ ^ 2 = s)
    (hcost : (𝔼 ω : I → G, 𝔼 ε : I → Bool,
      graphMomentCost Ω k (normalizedFiniteSignSum (fun i => a (ω i)) ε)) ≤ 10) :
    ∃ ω : I → G, ∃ ε : I → Bool,
      s / 2 ≤ ‖L (normalizedFiniteSignSum (fun i => a (ω i)) ε)‖ ^ 2 ∧
      graphMomentCost Ω k (normalizedFiniteSignSum (fun i => a (ω i)) ε) ≤ 240 := by
  let Z : (I → G) × (I → Bool) → ℝ := fun p =>
    ‖L (normalizedFiniteSignSum (fun i => a (p.1 i)) p.2)‖ ^ 2
  let B : (I → G) × (I → Bool) → ℝ := fun p =>
    graphMomentCost Ω k (normalizedFiniteSignSum (fun i => a (p.1 i)) p.2)
  have hmean : (𝔼 p, Z p) = s := by
    rw [show (𝔼 p, Z p) = 𝔼 ω : I → G, 𝔼 ε : I → Bool, Z (ω, ε) from
      by simpa only [Finset.univ_product_univ] using
        Finset.expect_product (Finset.univ : Finset (I → G))
          (Finset.univ : Finset (I → Bool)) Z]
    exact sampled_sign_signal_second L a s hsignal
  have hfourth : (𝔼 p, Z p ^ 2) ≤ 3 * s ^ 2 := by
    rw [show (𝔼 p, Z p ^ 2) = 𝔼 ω : I → G, 𝔼 ε : I → Bool, Z (ω, ε) ^ 2 from
      by simpa only [Finset.univ_product_univ] using
        Finset.expect_product (Finset.univ : Finset (I → G))
          (Finset.univ : Finset (I → Bool)) (fun p => Z p ^ 2)]
    simpa only [Z, ← pow_mul] using sampled_sign_signal_fourth L a s hsignal
  have hB : (𝔼 p, B p) ≤ 10 := by
    rw [show (𝔼 p, B p) = 𝔼 ω : I → G, 𝔼 ε : I → Bool, B (ω, ε) from
      by simpa only [Finset.univ_product_univ] using
        Finset.expect_product (Finset.univ : Finset (I → G))
          (Finset.univ : Finset (I → Bool)) B]
    exact hcost
  obtain ⟨p, hp⟩ := exists_signal_and_cost_le Z B hs
    (fun _ => sq_nonneg _) (fun _ => graphMomentCost_nonneg Ω hk _) hmean hfourth hB
  exact ⟨p.1, p.2, hp⟩

end

end KadisonKastler

end OAI
