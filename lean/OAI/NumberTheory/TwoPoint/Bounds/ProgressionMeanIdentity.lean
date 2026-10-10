import OAI.NumberTheory.TwoPoint.Bounds.QuantitativeCenteringAssembly
import OAI.NumberTheory.TwoPoint.Bounds.DivisibilityPrefix

namespace OAI

/-! Match the analytic real-cutoff mean with the manuscript's ordinary
progression sum, for every residue class. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma progressionLiouvilleMean_eq (h l b : ℕ) [NeZero l] (X : ℝ) :
    progressionLiouvilleMean h l b X =
      progressionSum liouville liouville h l b ⌊X⌋₊ / (X : ℂ) := by
  unfold progressionLiouvilleMean
  rw [positivePrefix_eq_Icc]
  congr 1
  simp only [progressionSum, sum_filter]
  apply sum_congr rfl
  intro n _
  simp only [progressionSequence, ZMod.natCast_eq_natCast_iff']
  split_ifs <;> simp only [zero_mul]

lemma primeFactors_exclusions (h l : ℕ) (hh : 0 < h) (hl : 0 < l) :
    (∀ p, p.Prime → p ∣ h → p ∈ (h * l).primeFactors) ∧
      (∀ p, p.Prime → p ∣ l → p ∈ (h * l).primeFactors) := by
  have hn : h * l ≠ 0 := (Nat.mul_pos hh hl).ne'
  constructor
  · intro p hp hph
    exact Nat.mem_primeFactors.mpr ⟨hp, dvd_mul_of_dvd_left hph l, hn⟩
  · intro p hp hpl
    exact Nat.mem_primeFactors.mpr ⟨hp, dvd_mul_of_dvd_right hpl h, hn⟩

end TwoPointCorrelations

end OAI
