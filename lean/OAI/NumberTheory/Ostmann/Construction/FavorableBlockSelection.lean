import OAI.NumberTheory.Ostmann.Construction.FiniteLogBlockMass
import OAI.NumberTheory.Ostmann.Preliminaries.MertensHarmonicBands

namespace OAI

/-! # Selecting one dense logarithmic block from the favorable prime mass -/
namespace Ostmann
open scoped Classical BigOperators

theorem favorable_logarithmic_block (L : ℝ) (hL : 1000 ≤ L) (F : Finset ℕ)
    (hF : F ⊆ logLogPrimeBand L)
    (hmass : (3 / 20 : ℝ) * L < ∑ p ∈ F, (p : ℝ)⁻¹) :
    ∃ lo : ℝ, Real.exp ((1 / 20 : ℝ) * L) ≤ lo ∧
      lo ≤ Real.exp ((9 / 10 : ℝ) * L) ∧
      (1 / 20 : ℝ) * (10 * Real.exp ((1 / 100 : ℝ) * L)) <
        ∑ p ∈ F.filter (fun p : ℕ => lo ≤ Real.log (p : ℝ) ∧
          Real.log (p : ℝ) ≤ lo + 10 * Real.exp ((1 / 100 : ℝ) * L)), Real.log (p : ℝ) / p := by
  have hL0 : 0 ≤ L := by linarith
  have hw1 : 1 ≤ 10 * Real.exp ((1 / 100 : ℝ) * L) := by
    have he := Real.one_le_exp (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 100) hL0)
    linarith
  have ha : 10 * Real.exp ((1 / 100 : ℝ) * L) ≤ Real.exp ((1 / 20 : ℝ) * L) := by
    have hten : 10 ≤ Real.exp ((1 / 25 : ℝ) * L) := by
      linarith [Real.add_one_le_exp ((1 / 25 : ℝ) * L)]
    have hh := mul_le_mul_of_nonneg_right hten (Real.exp_nonneg ((1 / 100 : ℝ) * L))
    rw [← Real.exp_add] at hh
    convert hh using 1; ring_nf
  have hlogN : Real.log (⌊Real.exp ((9 / 10 : ℝ) * L)⌋₊ + 1 : ℕ) ≤ L := by
    have hb : 1 ≤ Real.exp ((9 / 10 : ℝ) * L) := Real.one_le_exp (by positivity)
    have htwo : 2 ≤ Real.exp ((1 / 10 : ℝ) * L) := by
      linarith [Real.add_one_le_exp ((1 / 10 : ℝ) * L)]
    have hh := mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg ((9 / 10 : ℝ) * L))
    rw [← Real.exp_add, show (9 / 10 : ℝ) * L + (1 / 10 : ℝ) * L = L by ring] at hh
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    have hf := Nat.floor_le (Real.exp_nonneg ((9 / 10 : ℝ) * L))
    push_cast
    linarith
  apply exists_logarithmic_heavy_interval F (Real.exp ((1 / 20 : ℝ) * L))
    (Real.exp ((9 / 10 : ℝ) * L)) (10 * Real.exp ((1 / 100 : ℝ) * L))
    (1 / 20) (by positivity) hw1 ha (by norm_num)
  · intro p hp
    exact ⟨(logLogPrimeBand_mem (hF hp)).2.1.le, (logLogPrimeBand_mem (hF hp)).2.2⟩
  · apply lt_trans _ hmass
    linarith

end Ostmann

end OAI
