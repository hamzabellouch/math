import OAI.Analysis.KadisonKastler.FiniteIndependentSamples
import OAI.Analysis.KadisonKastler.VectorStateFourthMoment

namespace OAI

/-! # Fourth moments for independently sampled operator coefficients

The diagonal correction in the sign expansion is retained before the
independent samples are averaged. Consequently its coefficient is
`1/m`, while the two off-diagonal pairings have coefficient `1-1/m`.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H I G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Fintype I] [DecidableEq I] [Fintype G] [Nonempty G]

/-- Exact diagonal counting and the crossed-pairing inequality give the
unnormalized sampled fourth-moment estimate. -/
theorem expect_sampledSignSum_vector_fourth_le
    (Ω : H) (a : G → H →L[ℂ] H) :
    (𝔼 ω : I → G, 𝔼 ε : I → Bool,
      realVectorState Ω ((star (finiteSignSum (fun i => a (ω i)) ε) *
        finiteSignSum (fun i => a (ω i)) ε) ^ 2)) ≤
      (Fintype.card I : ℝ) * (𝔼 g, realVectorState Ω ((star (a g) * a g) ^ 2)) +
      (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1) *
        ((𝔼 g, 𝔼 h, realVectorState Ω ((star (a g) * a g) * (star (a h) * a h))) +
          2 * (𝔼 g, 𝔼 h, realVectorState Ω
            ((star (a g) * a h) * (star (a h) * a g)))) := by
  let D : ℝ := 𝔼 g, realVectorState Ω ((star (a g) * a g) ^ 2)
  let P : ℝ := 𝔼 g, 𝔼 h,
    realVectorState Ω ((star (a g) * a g) * (star (a h) * a h))
  let Q : ℝ := 𝔼 g, 𝔼 h,
    realVectorState Ω ((star (a g) * a h) * (star (a h) * a g))
  have hpoint (ω : I → G) :
      (𝔼 ε : I → Bool,
        realVectorState Ω ((star (finiteSignSum (fun i => a (ω i)) ε) *
          finiteSignSum (fun i => a (ω i)) ε) ^ 2)) ≤
      (∑ i, ∑ j, realVectorState Ω
        ((star (a (ω i)) * a (ω i)) * (star (a (ω j)) * a (ω j)))) +
      2 * (∑ i, ∑ j, realVectorState Ω
        ((star (a (ω i)) * a (ω j)) * (star (a (ω j)) * a (ω i)))) -
      2 * ∑ i, realVectorState Ω ((star (a (ω i)) * a (ω i)) ^ 2) := by
    rw [expect_finiteSignSum_vector_fourth]
    have hc := sum_vectorState_crossed_le Ω (fun i => a (ω i))
    linarith
  have hP : (𝔼 ω : I → G, ∑ i, ∑ j, realVectorState Ω
      ((star (a (ω i)) * a (ω i)) * (star (a (ω j)) * a (ω j)))) =
      (Fintype.card I : ℝ) * D +
        (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1) * P := by
    simpa only [D, P, pow_two] using expect_sample_pair_sum (I := I)
      (fun g h => realVectorState Ω ((star (a g) * a g) * (star (a h) * a h)))
  have hQ : (𝔼 ω : I → G, ∑ i, ∑ j, realVectorState Ω
      ((star (a (ω i)) * a (ω j)) * (star (a (ω j)) * a (ω i)))) =
      (Fintype.card I : ℝ) * D +
        (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1) * Q := by
    simpa only [D, Q, pow_two] using expect_sample_pair_sum (I := I)
      (fun g h => realVectorState Ω ((star (a g) * a h) * (star (a h) * a g)))
  have hD : (𝔼 ω : I → G, ∑ i,
      realVectorState Ω ((star (a (ω i)) * a (ω i)) ^ 2)) =
      (Fintype.card I : ℝ) * D := by
    rw [Finset.expect_sum_comm]
    have hi (i : I) : (𝔼 ω : I → G,
        realVectorState Ω ((star (a (ω i)) * a (ω i)) ^ 2)) = D :=
      expect_sample_coordinate i (fun g => realVectorState Ω ((star (a g) * a g) ^ 2))
    simp only [hi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have havg := Finset.expect_le_expect (s := Finset.univ) (fun ω _ => hpoint ω)
  simp only [Finset.expect_sub_distrib, Finset.expect_add_distrib,
    ← Finset.mul_expect, hP, hQ, hD] at havg
  change _ ≤ (Fintype.card I : ℝ) * D +
    (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1) * (P + 2 * Q)
  linarith

omit [Fintype I] [DecidableEq I] [Fintype G] [Nonempty G] in
private theorem vector_fourth_smul (Ω : H) (t : ℝ) (x : H →L[ℂ] H) :
    realVectorState Ω ((star (t • x) * (t • x)) ^ 2) =
      t ^ 4 * realVectorState Ω ((star x * x) ^ 2) := by
  simp only [pow_two, star_smul, star_trivial, smul_mul_assoc, mul_smul_comm,
    smul_smul, map_smul, smul_eq_mul]
  ring

variable [Nonempty I]

/-- Normalizing by the sample size yields the exact `1/m` diagonal cost
and the two independent off-diagonal moments. -/
theorem expect_sampledNormalizedSignSum_vector_fourth_le
    (Ω : H) (a : G → H →L[ℂ] H) :
    (𝔼 ω : I → G, 𝔼 ε : I → Bool,
      realVectorState Ω ((star (normalizedFiniteSignSum (fun i => a (ω i)) ε) *
        normalizedFiniteSignSum (fun i => a (ω i)) ε) ^ 2)) ≤
      (𝔼 g, realVectorState Ω ((star (a g) * a g) ^ 2)) / Fintype.card I +
      (1 - (Fintype.card I : ℝ)⁻¹) *
        ((𝔼 g, 𝔼 h, realVectorState Ω ((star (a g) * a g) * (star (a h) * a h))) +
          2 * (𝔼 g, 𝔼 h, realVectorState Ω
            ((star (a g) * a h) * (star (a h) * a g)))) := by
  have hs : (Real.sqrt (Fintype.card I : ℝ))⁻¹ ^ 4 =
      (Fintype.card I : ℝ)⁻¹ ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, inv_pow,
      Real.sq_sqrt (Nat.cast_nonneg _), inv_pow]
  simp only [normalizedFiniteSignSum, vector_fourth_smul]
  simp_rw [← Finset.mul_expect]
  rw [hs]
  refine (mul_le_mul_of_nonneg_left (expect_sampledSignSum_vector_fourth_le (I := I) Ω a)
    (sq_nonneg ((Fintype.card I : ℝ)⁻¹))).trans_eq ?_
  have hm : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp [hm]

end

end KadisonKastler

end OAI
