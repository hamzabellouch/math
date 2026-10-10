import OAI.Combinatorics.BinaryEdit.CodeExistence
import OAI.Combinatorics.BinaryEdit.CodeConversion
import OAI.Combinatorics.BinaryEdit.EncodedSegmentSeparation

namespace OAI

/-! The unconditional prescribed-length binary conversion theorem. The code
is selected once for the alphabet and input length, before either input word.
The edits used throughout are ordinary unrestricted unit-cost edits. -/

namespace TreeEdit.BinaryLower

universe u

/-- Polynomial code, `thm:804`, including the sharper `eq:402` and the exact
encoded length. The code is chosen once and works for every input pair. -/
theorem fixed_length_binary_conversion :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ∀ (Γ : Type u) [Fintype Γ],
        1 ≤ Fintype.card Γ → Fintype.card Γ ≤ M →
        ∃ c : Γ → Word Bool (M ^ 2),
          (∀ x : Word Γ M, (encode c x.val).length = M ^ 3) ∧
          ∀ x y : Word Γ M,
            (((M ^ 2 : ℕ) : ℝ) / 804 * (ed x.val y.val : ℝ) ≤
                (ed (encode c x.val) (encode c y.val) : ℝ)) ∧
            ((ed (encode c x.val) (encode c y.val) : ℝ) ≤
                ((M ^ 2 : ℕ) : ℝ) * (ed x.val y.val : ℝ)) ∧
            (((M ^ 2 : ℕ) : ℝ) / 402 * (deficit M x.val y.val : ℝ) ≤
                (deficit (M * M ^ 2) (encode c x.val) (encode c y.val) : ℝ)) := by
  obtain ⟨M₀, hM₀⟩ := Code.exists_binary_code_with_error_budget.{u}
  refine ⟨M₀, ?_⟩
  intro M hM Γ inst _hΓpos hΓ
  obtain ⟨hMtwo, herr, hcode⟩ := hM₀ M hM
  obtain ⟨c, hsep⟩ := hcode Γ hΓ
  refine ⟨c, ?_, ?_⟩
  · intro x
    rw [length_encode, x.property]
    ring
  · intro x y
    have hMpos : 0 < M := by omega
    have hP : 0 < M ^ 2 := pow_pos hMpos 2
    have hadd := Code.additive_of_codeword_separation hP c hsep
      x.val y.val x.property y.property
    have hbounds := Code.encode_bounds_of_additive c x.property y.property
      hadd (Code.natural_short_pair_error herr)
    exact ⟨hbounds.1.1, hbounds.1.2, hbounds.2⟩

end TreeEdit.BinaryLower

end OAI
