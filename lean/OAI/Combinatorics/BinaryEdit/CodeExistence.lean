import OAI.Combinatorics.BinaryEdit.CodeNumerics
import OAI.Combinatorics.BinaryEdit.SegmentCodeLCS

namespace OAI

/-! Closing the probabilistic segment-code construction at the exact source
parameters: block width M² and cutoff ceil(120 log₂ M). -/

namespace TreeEdit.BinaryLower.Code

universe u

/-- A single binary codebook separates all long segments of unequal labels.
The alphabet can be arbitrary finite; its size is only bounded by M. -/
theorem exists_fixed_width_separated_code {M : ℕ} (hM : 2 ≤ M)
    (Γ : Type u) [Fintype Γ] (hΓ : Fintype.card Γ ≤ M) :
    ∃ c : Γ → Word Bool (M ^ 2),
      ∀ (k l : Γ), k ≠ l → ∀ (a i j : ℕ), segmentThreshold M ≤ a →
        i + a ≤ M ^ 2 → j + a ≤ M ^ 2 →
          100 * lcs (((c k).val.drop i).take a)
            (((c l).val.drop j).take a) ≤ 99 * a := by
  apply SegmentCode.exists_lcs_separated_code Γ (M ^ 2) (segmentThreshold M)
  simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using
    code_union_bound_for_alphabet hΓ hM

/-- There is an absolute threshold at which the actual codebook and the
short-pair error budget needed by the deterministic proof coexist. -/
theorem exists_binary_code_with_error_budget :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      2 ≤ M ∧
      2 * (M : ℝ) * segmentThreshold M ≤ (M : ℝ) ^ 2 / 2 ∧
      ∀ (Γ : Type u) [Fintype Γ], Fintype.card Γ ≤ M →
        ∃ c : Γ → Word Bool (M ^ 2),
          ∀ (k l : Γ), k ≠ l → ∀ (a i j : ℕ), segmentThreshold M ≤ a →
            i + a ≤ M ^ 2 → j + a ≤ M ^ 2 →
              100 * lcs (((c k).val.drop i).take a)
                (((c l).val.drop j).take a) ≤ 99 * a := by
  obtain ⟨M₀, hM₀⟩ := exists_code_numerical_threshold
  refine ⟨M₀, fun M hM => ?_⟩
  obtain ⟨hM2, herr, _⟩ := hM₀ M hM
  exact ⟨hM2, herr, fun Γ _ hΓ => exists_fixed_width_separated_code hM2 Γ hΓ⟩

end TreeEdit.BinaryLower.Code

end OAI
