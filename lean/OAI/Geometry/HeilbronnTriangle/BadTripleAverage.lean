import OAI.Geometry.HeilbronnTriangle.RepeatedLabels

namespace OAI


namespace Problem355.Sampling

open Finset

variable {α Ω : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype Ω]

theorem bad_triple_average_le
    (weight D probability : α → α → α → Ω → ℝ)
    (A M : ℝ) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hweight : ∀ a b c ω, 0 ≤ weight a b c ω)
    (hmoment : ∀ a b c, (∑ ω, weight a b c ω * D a b c ω) ≤ M)
    (hzero : ∀ a b c ω, a ≠ b → a ≠ c → b ≠ c → probability a b c ω = 0)
    (hbad : ∀ a b c ω, a = b ∨ a = c ∨ b = c →
      probability a b c ω ≤ A * D a b c ω) :
    (∑ a, ∑ b, ∑ c, ∑ ω, weight a b c ω * probability a b c ω) /
        (Fintype.card α : ℝ) ^ 3 ≤ 3 * A * M / (Fintype.card α : ℝ) := by
  have hbound (a b c : α) :
      (∑ ω, weight a b c ω * probability a b c ω) ≤ A * M := by
    by_cases hrep : a = b ∨ a = c ∨ b = c
    · calc
        (∑ ω, weight a b c ω * probability a b c ω) ≤
            ∑ ω, weight a b c ω * (A * D a b c ω) :=
          Finset.sum_le_sum fun ω _ =>
            mul_le_mul_of_nonneg_left (hbad a b c ω hrep) (hweight a b c ω)
        _ = A * (∑ ω, weight a b c ω * D a b c ω) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ω hω
          ring
        _ ≤ A * M := mul_le_mul_of_nonneg_left (hmoment a b c) hA
    · have hab : a ≠ b := fun h => hrep (Or.inl h)
      have hac : a ≠ c := fun h => hrep (Or.inr (Or.inl h))
      have hbc : b ≠ c := fun h => hrep (Or.inr (Or.inr h))
      simp only [hzero a b c _ hab hac hbc, mul_zero, Finset.sum_const_zero]
      exact mul_nonneg hA hM
  have h := average_repeated_labels_le
    (fun a b c => ∑ ω, weight a b c ω * probability a b c ω)
    (A * M) (mul_nonneg hA hM) hbound (by
      intro a b c hab hac hbc
      simp only [hzero a b c _ hab hac hbc, mul_zero, Finset.sum_const_zero])
  simpa only [mul_assoc] using h

theorem bad_triple_average_le_six
    (weight D probability : α → α → α → Ω → ℝ)
    (A : ℝ) (hA : 0 ≤ A)
    (hweight : ∀ a b c ω, 0 ≤ weight a b c ω)
    (hmoment : ∀ a b c, (∑ ω, weight a b c ω * D a b c ω) ≤ 2)
    (hzero : ∀ a b c ω, a ≠ b → a ≠ c → b ≠ c → probability a b c ω = 0)
    (hbad : ∀ a b c ω, a = b ∨ a = c ∨ b = c →
      probability a b c ω ≤ A * D a b c ω) :
    (∑ a, ∑ b, ∑ c, ∑ ω, weight a b c ω * probability a b c ω) /
        (Fintype.card α : ℝ) ^ 3 ≤ 6 * A / (Fintype.card α : ℝ) := by
  have h := bad_triple_average_le weight D probability A 2 hA (by norm_num)
    hweight hmoment hzero hbad
  convert h using 1
  ring

theorem lifting_weighted_count_bound
    {h N D E orbit c₀ C L mass : ℝ}
    (hh : 0 < h) (hN : 0 < N) (hD : 0 < D) (hE : 0 < E)
    (ho : 0 < orbit) (hc₀ : 0 < c₀)
    (hmass : 0 ≤ mass)
    (horbit : c₀ * h ^ 8 / (D ^ 3 * E ^ 2) ≤ orbit)
    (hcount : mass ≤ C * L ^ 2 * N ^ 6 / (D ^ 2 * E ^ 2)) :
    h ^ 9 / (N ^ 9 * orbit) * mass ≤
      (C / c₀) * L ^ 2 * h * D / N ^ 3 := by
  have hinv : 1 / orbit ≤ (D ^ 3 * E ^ 2) / (c₀ * h ^ 8) := by
    apply (div_le_div_iff₀ ho (by positivity)).2
    have hl := (div_le_iff₀ (by positivity : 0 < D ^ 3 * E ^ 2)).1 horbit
    simpa only [one_mul, mul_one, mul_comm] using hl
  calc
    h ^ 9 / (N ^ 9 * orbit) * mass = (h ^ 9 / N ^ 9) * (1 / orbit) * mass := by
      ring
    _ ≤ (h ^ 9 / N ^ 9) * ((D ^ 3 * E ^ 2) / (c₀ * h ^ 8)) * mass :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinv (by positivity)) hmass
    _ ≤ (h ^ 9 / N ^ 9) * ((D ^ 3 * E ^ 2) / (c₀ * h ^ 8)) *
        (C * L ^ 2 * N ^ 6 / (D ^ 2 * E ^ 2)) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = (C / c₀) * L ^ 2 * h * D / N ^ 3 := by
      field_simp

theorem bad_triple_average_of_lifting_bounds
    (weight D E orbit mass probability : α → α → α → Ω → ℝ)
    {h N c₀ C L : ℝ} (hh : 0 < h) (hN : 0 < N) (hc₀ : 0 < c₀) (hC : 0 ≤ C)
    (hweight : ∀ a b c ω, 0 ≤ weight a b c ω)
    (hD : ∀ a b c ω, 0 < D a b c ω)
    (hE : ∀ a b c ω, 0 < E a b c ω)
    (ho : ∀ a b c ω, 0 < orbit a b c ω)
    (hmass : ∀ a b c ω, 0 ≤ mass a b c ω)
    (hmoment : ∀ a b c, (∑ ω, weight a b c ω * D a b c ω) ≤ 2)
    (hzero : ∀ a b c ω, a ≠ b → a ≠ c → b ≠ c → probability a b c ω = 0)
    (horbit : ∀ a b c ω, c₀ * h ^ 8 /
      ((D a b c ω) ^ 3 * (E a b c ω) ^ 2) ≤ orbit a b c ω)
    (hcount : ∀ a b c ω, a = b ∨ a = c ∨ b = c →
      mass a b c ω ≤ C * L ^ 2 * N ^ 6 /
        ((D a b c ω) ^ 2 * (E a b c ω) ^ 2))
    (hlift : ∀ a b c ω, a = b ∨ a = c ∨ b = c →
      probability a b c ω ≤ h ^ 9 / (N ^ 9 * orbit a b c ω) * mass a b c ω) :
    (∑ a, ∑ b, ∑ c, ∑ ω, weight a b c ω * probability a b c ω) /
      (Fintype.card α : ℝ) ^ 3 ≤
        6 * (C / c₀) * L ^ 2 * h / (N ^ 3 * (Fintype.card α : ℝ)) := by
  have h := bad_triple_average_le_six weight D probability
    ((C / c₀) * L ^ 2 * h / N ^ 3) (by positivity)
    hweight hmoment hzero (by
      intro a b c ω hrep
      calc
        probability a b c ω ≤
            h ^ 9 / (N ^ 9 * orbit a b c ω) * mass a b c ω :=
          hlift a b c ω hrep
        _ ≤ (C / c₀) * L ^ 2 * h * D a b c ω / N ^ 3 :=
          lifting_weighted_count_bound hh hN (hD a b c ω) (hE a b c ω)
            (ho a b c ω) hc₀ (hmass a b c ω) (horbit a b c ω) (hcount a b c ω hrep)
        _ = ((C / c₀) * L ^ 2 * h / N ^ 3) * D a b c ω := by ring)
  convert h using 1
  ring

end Problem355.Sampling

end OAI
