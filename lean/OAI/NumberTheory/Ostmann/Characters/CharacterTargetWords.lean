import OAI.NumberTheory.Ostmann.Construction.TargetPrimeWords

namespace OAI

/-! # Simultaneous positive-length words for every character pivot and the filler -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- A word consists of cells from one whole, previously tested rich shell. -/
structure CharacterTargetWord (P : Finset ℕ) (F : ℕ → ℂ)
    (c δ U : ℝ) (k : ℕ) (T : ℝ) where
  shell : ℕ
  indices : List ℕ
  shell_le : shell ≤ 5 * k
  rich : c ≤ ∑ p ∈ loglogShell P (U + shell), (p : ℝ)⁻¹
  lower : Real.log T - 2 * (k : ℝ) / 10000 ≤ U + shell
  upper : U + shell + 1 ≤ Real.log T - (k : ℝ) / 10000
  cells : ∀ h ∈ indices,
    δ * c / (32 * Real.exp (U + shell)) ≤
      finiteCellMass (loglogShell P (U + shell)) primeLogIndex (fun p => (p : ℝ)⁻¹) h ∧
    (∑ p : loglogShell P (U + shell), primeCellWordPrior _ h p) = 1 ∧
    δ / 2 ≤ (∑ p : loglogShell P (U + shell), (primeCellWordPrior _ h p : ℂ) * F p).re
  error : |(indices.sum : ℝ) - T| < 64 / (δ * c)
  length_le : (indices.length : ℝ) ≤ 256 / (δ * c) * Real.exp (2 * (k : ℝ) / 10000)

theorem CharacterTargetWord.length_pos {P : Finset ℕ} {F : ℕ → ℂ} {c δ U T : ℝ} {k : ℕ}
    (w : CharacterTargetWord P F c δ U k T) (hT : 64 / (δ * c) < T) (hT0 : 0 ≤ T) :
    0 < w.indices.length := by
  by_contra! hn
  have he : w.indices = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hn)
  have hh := w.error
  rw [he, List.sum_nil, Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg hT0] at hh
  exact (not_lt_of_ge hT.le) hh

/-- All nonanchor roles are chosen after fixing the word bin. Their total
length is bounded by the number of actual roles times the single-word bound. -/
theorem PublishedProgressionInput.character_target_words
    (P0 : PublishedProgressionInput) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (k : ℕ), 20000 ≤ k → C ≤ Real.exp ((k : ℝ) / 10000) →
      ∀ (τ : ℝ), 0 < τ → U ≤ Real.log τ →
      Real.log τ ≤ U + 2 * (k : ℝ) / 10000 →
      ∀ (P : Finset ℕ) (F : ℕ → ℂ), (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, ‖F p‖ ≤ 1) →
      (∀ u v : ℝ, U ≤ u → v ≤ U + 5 * k → (k : ℝ) / 10000 ≤ v - u →
        ∃ j : ℕ, u ≤ U + j ∧ U + j + 1 ≤ v ∧
          c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹) →
      (∀ j : ℕ, j ≤ 5 * k → c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ →
        (∀ p ∈ loglogShell P (U + j),
          Real.log (p : ℝ) ≤ (1000 * (4 : ℝ) ^ k * τ) / 4) →
        δ * (∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹) ≤
          ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ * (F p).re) →
      ∀ T : Option (Fin k) → ℝ,
      (∀ j, (2 : ℝ) ^ (k - 1) * τ / 4 ≤ T j) →
      (∀ j, T j ≤ 600 * (4 : ℝ) ^ k * τ) →
      ∃ w : ∀ j, CharacterTargetWord P F c δ U k (T j),
        (∀ j, 0 < (w j).indices.length) ∧
        (∑ j, ((w j).indices.length : ℝ)) ≤
          (k + 1 : ℕ) * (256 / (δ * c) * Real.exp (2 * (k : ℝ) / 10000)) := by
  obtain ⟨C, hC, hwords⟩ := P0.target_prime_word c δ hc hδ
  refine ⟨C, hC, ?_⟩
  filter_upwards [hwords, Real.tendsto_exp_atTop.eventually
    (eventually_gt_atTop (4 * (64 / (δ * c))))] with U hw hU
  intro k hk hCk τ hτ hτlo hτhi P F hP hF hrich htest T hTlo hThi
  have hchoice : ∀ j, Nonempty (CharacterTargetWord P F c δ U k (T j)) := by
    intro j
    obtain ⟨s, n, w, hs, hr, hlo, hhi, hn, hcells, herr, hlength⟩ :=
      hw k hk hCk τ hτ hτlo hτhi P F hP hF hrich htest (T j) (hTlo j) (hThi j)
    exact ⟨⟨s, w, hs, hr, hlo, hhi, hcells, herr, by simpa only [hn] using hlength⟩⟩
  let w : ∀ j, CharacterTargetWord P F c δ U k (T j) := fun j => Classical.choice (hchoice j)
  refine ⟨w, ?_, ?_⟩
  · intro j
    have hτU : Real.exp U ≤ τ := by
      simpa only [Real.exp_log hτ] using Real.exp_le_exp.mpr hτlo
    have hp : (1 : ℝ) ≤ 2 ^ (k - 1) := one_le_pow₀ (by norm_num)
    have htau := mul_le_mul_of_nonneg_right hp hτ.le
    have ht : 64 / (δ * c) < T j := by nlinarith only [hU, hτU, htau, hTlo j]
    exact (w j).length_pos ht ((by positivity : 0 < 64 / (δ * c)).trans ht).le
  · calc
      _ ≤ ∑ _j : Option (Fin k),
          256 / (δ * c) * Real.exp (2 * (k : ℝ) / 10000) :=
        Finset.sum_le_sum (fun j _ => (w j).length_le)
      _ = _ := by simp

end Ostmann

end OAI
