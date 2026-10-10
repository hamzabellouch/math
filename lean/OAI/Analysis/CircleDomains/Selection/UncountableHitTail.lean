import OAI.Analysis.CircleDomains.Sobolev.ShrinkingHitEnergy

namespace OAI

/-! Shrinking hit estimates on the whole dust set. Square summability
itself supplies the countable support; the dust is not assumed countable. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

theorem tendsto_punctured_hit_energy_of_finite_tsum {S : Type*}
    (m : S → ℝ≥0∞) (hm : (∑' s, m s ^ 2) ≠ ∞) (p : S) (U : ℕ → Set S)
    (hshrink : ∀ s ≠ p, ∀ᶠ n in atTop, s ∉ U n) :
    Tendsto (fun n => ∑' s, if s ∈ U n ∧ s ≠ p then m s ^ 2 else 0) atTop (𝓝 0) := by
  let T := support (fun s => m s ^ 2)
  have hT : T.Countable := Summable.countable_support_ennreal hm
  let : Countable T := hT.to_subtype
  have hsum : (∑' t : T, m t.val ^ 2) ≠ ∞ := by
    simpa only [T, tsum_subtype_support] using hm
  have hcover (t : T) : ∀ᶠ n in atTop, t ∈ {t : T | t.val ∉ U n ∨ t.val = p} := by
    by_cases ht : t.val = p
    · exact Eventually.of_forall fun _ => Or.inr ht
    · exact (hshrink t.val ht).mono fun _ h => Or.inl h
  have ht := tendsto_deleted_series_zero (fun t : T => m t.val ^ 2) hsum
    (fun n => {t : T | t.val ∉ U n ∨ t.val = p}) hcover
  have he (n : ℕ) : (∑' t : T, if t.val ∉ U n ∨ t.val = p then 0 else m t.val ^ 2) =
      ∑' s, if s ∈ U n ∧ s ≠ p then m s ^ 2 else 0 := by
    have hc : (fun t : T => if t.val ∉ U n ∨ t.val = p then 0 else m t.val ^ 2) =
        fun t => if t.val ∈ U n ∧ t.val ≠ p then m t.val ^ 2 else 0 := by
      funext t
      by_cases hu : t.val ∈ U n <;> by_cases hp : t.val = p <;> simp [hu, hp]
    rw [hc]
    apply tsum_subtype_eq_of_support_subset
      (f := fun s : S => if s ∈ U n ∧ s ≠ p then m s ^ 2 else 0) (s := T)
    intro s hs
    by_contra hn
    have hz : m s ^ 2 = 0 := notMem_support.mp hn
    simp only [mem_support, ne_eq] at hs
    split_ifs at hs <;> simp_all
  convert ht using 1
  funext n
  rw [← he n]
  apply tsum_congr
  intro t
  by_cases hu : t.val ∈ U n <;> by_cases hp : t.val = p <;> simp [hu, hp]

theorem tendsto_punctured_hit_norm_of_finite_tsum {S : Type*}
    (m : S → ℝ≥0∞) (hm : (∑' s, m s ^ 2) ≠ ∞) (p : S) (U : ℕ → Set S)
    (hshrink : ∀ s ≠ p, ∀ᶠ n in atTop, s ∉ U n) :
    Tendsto (fun n => countingSquareNorm
      (fun s => if s ∈ U n ∧ s ≠ p then m s else 0)) atTop (𝓝 0) := by
  have ht := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0 |>.comp
    (tendsto_punctured_hit_energy_of_finite_tsum m hm p U hshrink)
  have he (n : ℕ) : (∑' s, if s ∈ U n ∧ s ≠ p then m s ^ 2 else 0) =
      ∑' s, (if s ∈ U n ∧ s ≠ p then m s else 0) ^ 2 := by
    apply tsum_congr
    intro s
    split_ifs <;> simp
  simpa only [he, countingSquareNorm, Function.comp_def,
    ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using ht

end CircleDomainRigidity

end

end OAI
