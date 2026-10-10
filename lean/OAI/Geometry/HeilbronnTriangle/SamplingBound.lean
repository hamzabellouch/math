import OAI.Geometry.HeilbronnTriangle.RepeatedLabels

namespace OAI


namespace Problem355.Sampling

lemma conditional_bad_triple_bound
    {p h N O D E c₀ c₁ L W : ℝ}
    (hh : 0 < h) (hN : 0 < N) (hD : 0 < D) (hE : 0 < E)
    (hc₀ : 0 < c₀) (hc₁ : 0 ≤ c₁) (hL : 0 ≤ L)
    (hOrbit : c₀ * h ^ 8 / (D ^ 3 * E ^ 2) ≤ O)
    (hCount : W ≤ c₁ * L * N ^ 6 / (D * E) ^ 2)
    (hLift : p ≤ h ^ 9 / (N ^ 9 * O) * W) :
    p ≤ (c₁ / c₀) * L * h * D / N ^ 3 := by
  have hbase : 0 < c₀ * h ^ 8 / (D ^ 3 * E ^ 2) := by positivity
  have hO : 0 < O := lt_of_lt_of_le hbase hOrbit
  have hcoef : 0 ≤ h ^ 9 / (N ^ 9 * O) := by positivity
  have hmax : 0 ≤ c₁ * L * N ^ 6 / (D * E) ^ 2 := by positivity
  have hfactor : h ^ 9 / (N ^ 9 * O) ≤
      h ^ 9 / (N ^ 9 * (c₀ * h ^ 8 / (D ^ 3 * E ^ 2))) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hOrbit (by positivity))
  calc
    p ≤ h ^ 9 / (N ^ 9 * O) * W := hLift
    _ ≤ h ^ 9 / (N ^ 9 * O) * (c₁ * L * N ^ 6 / (D * E) ^ 2) :=
      mul_le_mul_of_nonneg_left hCount hcoef
    _ ≤ h ^ 9 / (N ^ 9 * (c₀ * h ^ 8 / (D ^ 3 * E ^ 2))) *
        (c₁ * L * N ^ 6 / (D * E) ^ 2) :=
      mul_le_mul_of_nonneg_right hfactor hmax
    _ = (c₁ / c₀) * L * h * D / N ^ 3 := by
      field_simp

lemma average_conditional_bad_triple_le
    {α Ω : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype Ω]
    (weight p D : α → α → α → Ω → ℝ) {K M : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hweight : ∀ a b c ω, 0 ≤ weight a b c ω)
    (hconditional : ∀ a b c ω, p a b c ω ≤ K * D a b c ω)
    (hmoment : ∀ a b c, ∑ ω, weight a b c ω * D a b c ω ≤ M)
    (hzero : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → ∀ ω, p a b c ω = 0) :
    (∑ a, ∑ b, ∑ c, ∑ ω, weight a b c ω * p a b c ω) /
        (Fintype.card α : ℝ) ^ 3 ≤ 3 * (K * M) / (Fintype.card α : ℝ) := by
  apply average_repeated_labels_le _ (K * M) (mul_nonneg hK hM)
  · intro a b c
    calc
      ∑ ω, weight a b c ω * p a b c ω ≤
          ∑ ω, weight a b c ω * (K * D a b c ω) := by
        apply Finset.sum_le_sum
        intro ω _
        exact mul_le_mul_of_nonneg_left (hconditional a b c ω) (hweight a b c ω)
      _ = K * ∑ ω, weight a b c ω * D a b c ω := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω _
        ring
      _ ≤ K * M := mul_le_mul_of_nonneg_left (hmoment a b c) hK
  · intro a b c hab hac hbc
    simp [hzero a b c hab hac hbc]

end Problem355.Sampling

end OAI
