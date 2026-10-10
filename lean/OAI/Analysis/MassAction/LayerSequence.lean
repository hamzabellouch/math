import OAI.Analysis.MassAction.FixedMinimum

namespace OAI

universe uAlpha

noncomputable section

namespace Problem326.Affine

/-- Build the finite sequence of type families used at a fixed minimum.
Each new threshold is chosen only after the preceding finite family, so arbitrary
positive label-dependent tolerances are allowed. The family constructor may
itself depend on the chosen threshold. -/
theorem exists_layer_sequence {α : Type uAlpha} (n : ℕ) {t b : ℝ} (htb : t < b)
    (E : α → ℝ) (F₀ : Finset α) (hE₀ : ∀ a ∈ F₀, 0 < E a)
    (Good : ℕ → ℝ → Finset α → Prop)
    (hmake : ∀ k : ℕ, 0 < k → k ≤ n → ∀ β : ℝ, t < β → β < b →
      ∃ F : Finset α, Good k β F ∧ ∀ a ∈ F, 0 < E a) :
    ∃ (β : ℕ → ℝ) (F : ℕ → Finset α),
      β 0 = b ∧ F 0 = F₀ ∧
      (∀ k, t < β k ∧ β k ≤ b ∧ ∀ a ∈ F k, 0 < E a) ∧
      ∀ k < n, β (k + 1) < β k ∧
        (∀ a ∈ F k, β (k + 1) - t < E a) ∧
        Good (k + 1) (β (k + 1)) (F (k + 1)) := by
  classical
  let S := {q : ℝ × Finset α // t < q.1 ∧ q.1 ≤ b ∧ ∀ a ∈ q.2, 0 < E a}
  let s₀ : S := ⟨(b, F₀), htb, le_rfl, hE₀⟩
  have hs : ∀ k : ℕ, ∀ s : S, ∃ s' : S, k < n →
      s'.val.1 < s.val.1 ∧
      (∀ a ∈ s.val.2, s'.val.1 - t < E a) ∧
      Good (k + 1) s'.val.1 s'.val.2 := by
    intro k s
    by_cases hk : k < n
    · obtain ⟨β, htβ, hβupper, hβE⟩ :=
        exists_threshold s.val.2 E s.property.2.2 s.property.1
      have hβb : β < b := hβupper.trans_le s.property.2.1
      obtain ⟨F, hFgood, hFE⟩ := hmake (k + 1) (by omega) (by omega) β htβ hβb
      exact ⟨⟨(β, F), htβ, hβb.le, hFE⟩, fun _ => ⟨hβupper, hβE, hFgood⟩⟩
    · exact ⟨s, fun h => (hk h).elim⟩
  choose next hnext using hs
  let state : ℕ → S := Nat.rec s₀ (fun k s => next k s)
  refine ⟨fun k => (state k).val.1, fun k => (state k).val.2, rfl, rfl, ?_, ?_⟩
  · intro k
    exact (state k).property
  · intro k hk
    exact hnext k (state k) hk

end Problem326.Affine

end

end OAI
