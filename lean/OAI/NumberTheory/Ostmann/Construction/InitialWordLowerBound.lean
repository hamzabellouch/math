import OAI.NumberTheory.Ostmann.Construction.PositiveWordStatistic

namespace OAI

/-! # From positive endpoint means to the initial word statistic -/

namespace Ostmann

open scoped BigOperators SchwartzMap

/-- The product-bin and endpoint pigeonholes feed the full nonnegative
Schwartz-weighted statistic. -/
theorem initial_word_lower_bound {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    {k m : ℕ} (E : Finset ℕ) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (μ : Fin k → A → ℝ) (F : ℤ → Fin k → A → ℂ)
    (bin : (Fin k → A) → B) (R : Fin m → ℤ → ℂ)
    (hμ : ∀ i x, 0 ≤ μ i x) (hmass : ∀ i, ∑ x, μ i x = 1)
    (hF : ∀ a i x, ‖F a i x‖ ≤ 1) (hR : ∀ i a, ‖R i a‖ ≤ 1)
    (c δ γ : ℝ) (hc : 0 ≤ c) (hδ : 0 ≤ δ) (hγ : 0 ≤ γ)
    (hψ : ∀ x, 0 ≤ (ψ x).re)
    (hcE : ∀ a ∈ E, c ≤ (ψ ((a : ℝ) / X)).re)
    (hmean : ∀ a ∈ E, ∀ i, δ ≤ (∑ x, (μ i x : ℂ) * F a i x).re)
    (hcell : ∀ a ∈ E, ∀ i, γ ≤ (R i a).re) :
    ∃ b : B,
      (E.card : ℝ) / Fintype.card B *
        (c * (δ ^ k / Fintype.card B) ^ 2 * γ ^ (2 * m)) ≤
      ∑' a : ℤ, wordStatisticTerm ψ X (fun a => binnedWordAverage μ (F a) bin b) R a := by
  let v : ℕ → B → ℂ := fun a => binnedWordAverage μ (F a) bin
  obtain ⟨b, S, hSE, hcard, hbin⟩ := common_large_bin E v (δ ^ k) (by
    intro a ha
    exact binnedWordAverage_total_lower μ (F a) bin δ hδ (hmean a ha))
  let S' := S.image (fun a : ℕ => (a : ℤ))
  have hS' : S'.card = S.card := Finset.card_image_of_injective _ (by
    intro a b h
    change (a : ℤ) = (b : ℤ) at h
    exact_mod_cast h)
  have hcardB : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  have hpop : (E.card : ℝ) / Fintype.card B ≤ S'.card := by
    apply (div_le_iff₀ hcardB).mpr
    rw [hS']
    have hh : (E.card : ℝ) ≤ (Fintype.card B : ℝ) * S.card := by exact_mod_cast hcard
    nlinarith
  have hlow := wordStatistic_lower ψ X hX
    (fun a => binnedWordAverage μ (F a) bin b) R S' hψ
    (fun a => binnedWordAverage_norm_le_one μ (F a) bin b hμ hmass (hF a)) hR
    c (δ ^ k / Fintype.card B) γ (by positivity) hγ
    (by
      intro a ha
      change a ∈ S.image (fun a : ℕ => (a : ℤ)) at ha
      obtain ⟨z, hz, hza⟩ := Finset.mem_image.mp ha
      subst a
      simpa only [Int.cast_natCast] using hcE z (hSE hz))
    (by
      intro a ha
      change a ∈ S.image (fun a : ℕ => (a : ℤ)) at ha
      obtain ⟨z, hz, hza⟩ := Finset.mem_image.mp ha
      subst a
      apply (div_le_iff₀ hcardB).mpr
      have hh := hbin z hz
      simpa [v, mul_comm] using hh)
    (by
      intro a ha i
      change a ∈ S.image (fun a : ℕ => (a : ℤ)) at ha
      obtain ⟨z, hz, hza⟩ := Finset.mem_image.mp ha
      subst a
      exact (hcell z (hSE hz) i).trans (Complex.re_le_norm _))
  exact ⟨b, (mul_le_mul_of_nonneg_right hpop (by positivity)).trans hlow⟩

end Ostmann

end OAI
