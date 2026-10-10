import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

/-! # Choosing the modulation radius before the graph's tail cutoff -/

namespace DefocusingNLS

theorem exists_physical_modulation_budget (A B D E H M : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hH : 0 ≤ H) (_hM : 0 ≤ M) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ ρ K : ℝ, 0 < ρ → 0 < K →
      ∃ r ε η J δ : ℝ, 0 < r ∧ r ≤ 1 / 2 ∧ r ≤ 2 * Real.log 2 ∧
        0 < ε ∧ 0 < η ∧ 2 ≤ J ∧ 0 < δ ∧ D * δ ≤ r ∧
        2 * K * B * (A + 1) * r ≤ ρ / 4 ∧
        H * (E * (r ^ 2 + r / J) + ε * M * r + B * D * δ +
          (ν * (2 * K * B * (A + 1) * r + 2 * η) + 2 * η) / K) ≤ r := by
  obtain ⟨ν, hν, hνsmall⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1 / 16)
    (2 * H * B * (A + 1))
  refine ⟨ν, hν, ?_⟩
  intro ρ K hρ hK
  obtain ⟨r₀, hr₀, hr₀small⟩ := exists_pos_mul_lt (div_pos hρ (by norm_num : (0 : ℝ) < 4))
    (2 * K * B * (A + 1))
  obtain ⟨r₁, hr₁, hr₁small⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1 / 16) (H * E)
  let r := min r₀ (min r₁ (min (1 / 2) (2 * Real.log 2)))
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min_iff.mpr ⟨hr₀, lt_min_iff.mpr ⟨hr₁, lt_min_iff.mpr ⟨by norm_num,
      mul_pos (by norm_num) (Real.log_pos (by norm_num))⟩⟩⟩
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hrr₁ : r ≤ r₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hrhalf : r ≤ 1 / 2 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hrlog : r ≤ 2 * Real.log 2 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hrsmall : H * E * r ≤ 1 / 16 :=
    (mul_le_mul_of_nonneg_left hrr₁ (mul_nonneg hH hE)).trans hr₁small.le
  have hstable : 2 * K * B * (A + 1) * r ≤ ρ / 4 :=
    (mul_le_mul_of_nonneg_left hrr₀ (by positivity)).trans hr₀small.le
  obtain ⟨ε, hε, hεsmall⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1 / 16) (H * M)
  obtain ⟨η, hη, hηsmall⟩ := exists_pos_mul_lt (div_pos hr (by norm_num : (0 : ℝ) < 16))
    (H * (2 * ν + 2) / K)
  let J := 2 + 16 * H * E
  have hJ : 2 ≤ J := by dsimp [J]; nlinarith [mul_nonneg hH hE]
  have hJpos : 0 < J := lt_of_lt_of_le (by norm_num) hJ
  have hJsmall : H * E / J ≤ 1 / 16 := by
    apply (div_le_iff₀ hJpos).mpr
    dsimp [J]
    nlinarith
  obtain ⟨δ₀, hδ₀, hδ₀small⟩ := exists_pos_mul_lt hr D
  obtain ⟨δ₁, hδ₁, hδ₁small⟩ := exists_pos_mul_lt
    (div_pos hr (by norm_num : (0 : ℝ) < 16)) (H * B * D)
  let δ := min δ₀ δ₁
  have hδ : 0 < δ := lt_min_iff.mpr ⟨hδ₀, hδ₁⟩
  have hDδ : D * δ ≤ r :=
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hD).trans hδ₀small.le
  have hδsmall : H * B * D * δ ≤ r / 16 :=
    (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)).trans hδ₁small.le
  refine ⟨r, ε, η, J, δ, hr, hrhalf, hrlog, hε, hη, hJ, hδ, hDδ, hstable, ?_⟩
  have hquad := mul_le_mul_of_nonneg_right hrsmall hr.le
  have htail := mul_le_mul_of_nonneg_right hJsmall hr.le
  have heps := mul_le_mul_of_nonneg_right hεsmall.le hr.le
  have hflat := mul_le_mul_of_nonneg_right hνsmall.le hr.le
  have hid : H * (E * (r ^ 2 + r / J) + ε * M * r + B * D * δ +
      (ν * (2 * K * B * (A + 1) * r + 2 * η) + 2 * η) / K) =
      (H * E * r) * r + (H * E / J) * r + (H * M * ε) * r + H * B * D * δ +
      (2 * H * B * (A + 1) * ν) * r + (H * (2 * ν + 2) / K) * η := by
    field_simp
    ring
  rw [hid]
  linarith

end DefocusingNLS

end OAI
