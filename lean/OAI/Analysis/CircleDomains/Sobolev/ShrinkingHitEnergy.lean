import OAI.Analysis.CircleDomains.Probability.ResidualTailNull

namespace OAI

/-! Square-summable hit probabilities have small punctured-collar tails. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

theorem tendsto_punctured_hit_energy {S : Type*} [Countable S]
    (m : S → ℝ≥0∞) (hm : (∑' s, m s ^ 2) ≠ ∞) (p : S) (U : ℕ → Set S)
    (hshrink : ∀ s ≠ p, ∀ᶠ n in atTop, s ∉ U n) :
    Tendsto (fun n => ∑' s, if s ∈ U n ∧ s ≠ p then m s ^ 2 else 0) atTop (𝓝 0) := by
  have hcover (s : S) : ∀ᶠ n in atTop, s ∈ {s | s ∉ U n ∨ s = p} := by
    by_cases hs : s = p
    · exact Eventually.of_forall fun _ => Or.inr hs
    · exact (hshrink s hs).mono fun _ hn => Or.inl hn
  have h := tendsto_deleted_series_zero (fun s => m s ^ 2) hm
    (fun n => {s | s ∉ U n ∨ s = p}) hcover
  convert h using 1
  funext n
  apply tsum_congr
  intro s
  by_cases hu : s ∈ U n <;> by_cases hs : s = p <;> simp [hu, hs]

theorem eventually_outside_shrinking_set {S : Type*} (U : ℕ → Set S)
    (hanti : Antitone U) (p : S) (hinter : (⋂ n, U n) ⊆ {p}) :
    ∀ s ≠ p, ∀ᶠ n in atTop, s ∉ U n := by
  intro s hsp
  have hn : ∃ n, s ∉ U n := by
    by_contra! h
    exact hsp (hinter (mem_iInter.mpr h))
  obtain ⟨n, hn⟩ := hn
  exact eventually_atTop.2 ⟨n, fun k hk hsk => hn (hanti hk hsk)⟩

theorem tendsto_punctured_hit_norm {S : Type*} [Countable S]
    (m : S → ℝ≥0∞) (hm : (∑' s, m s ^ 2) ≠ ∞) (p : S) (U : ℕ → Set S)
    (hshrink : ∀ s ≠ p, ∀ᶠ n in atTop, s ∉ U n) :
    Tendsto (fun n => countingSquareNorm
      (fun s => if s ∈ U n ∧ s ≠ p then m s else 0)) atTop (𝓝 0) := by
  have ht := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0 |>.comp
    (tendsto_punctured_hit_energy m hm p U hshrink)
  have he (n : ℕ) : (∑' s, if s ∈ U n ∧ s ≠ p then m s ^ 2 else 0) =
      ∑' s, (if s ∈ U n ∧ s ≠ p then m s else 0) ^ 2 := by
    apply tsum_congr
    intro s
    split_ifs <;> simp
  simpa only [he, countingSquareNorm, Function.comp_def,
    ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    using ht

end CircleDomainRigidity

end

end OAI
