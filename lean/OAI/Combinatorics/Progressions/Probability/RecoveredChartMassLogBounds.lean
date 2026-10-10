import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem recoveredChart_dimension_add_one_exp_bound (n : ℕ) {L : ℝ}
    (hL : 0 ≤ L) (hn : (n : ℝ) ≤ Real.exp L) :
    (n : ℝ) + 1 ≤ Real.exp (L + 1) := by
  have hLone : 1 ≤ Real.exp L := Real.one_le_exp_iff.mpr hL
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    (n : ℝ) + 1 ≤ 2 * Real.exp L := by linarith
    _ ≤ Real.exp 1 * Real.exp L := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem recoveredChartMass_exp_bound (j n d : ℕ) {L A C R : ℝ}
    (hL : 0 ≤ L) (hn : (n : ℝ) ≤ Real.exp L) (hd : (d : ℝ) ≤ Real.exp L)
    (hC : C ∈ Set.Icc 0 (Real.exp A)) (hR : R ∈ Set.Icc (0 : ℝ) 1) :
    ((j + 2 : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (j + 1) * C * ((d : ℝ) + 1) * R ≤
      Real.exp (((j + 2 : ℕ) : ℝ) + ((j + 2 : ℕ) : ℝ) * (L + 1) + A) := by
  have hC0 := hC.1
  have hCA := hC.2
  have hj : ((j + 2 : ℕ) : ℝ) ≤ Real.exp ((j + 2 : ℕ) : ℝ) := by
    linarith [Real.add_one_le_exp (((j + 2 : ℕ) : ℝ))]
  have hn' := recoveredChart_dimension_add_one_exp_bound n hL hn
  have hd' := recoveredChart_dimension_add_one_exp_bound d hL hd
  calc
    _ ≤ ((j + 2 : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (j + 1) * C * ((d : ℝ) + 1) :=
      mul_le_of_le_one_right (by positivity) hR.2
    _ ≤ Real.exp ((j + 2 : ℕ) : ℝ) * (Real.exp (L + 1)) ^ (j + 1) *
        Real.exp A * Real.exp (L + 1) := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      push_cast
      ring

theorem recoveredSlowChartMass_exp_bound (s n : ℕ) {L A B budget : ℝ}
    (hL : 0 ≤ L) (hn : (n : ℝ) ≤ Real.exp L)
    (hB : B ∈ Set.Icc 0 (Real.exp A)) :
    ((s + 1 : ℕ) : ℝ) * ((n : ℝ) + 1) ^ s * Real.exp budget * B ^ s ≤
      Real.exp (((s + 1 : ℕ) : ℝ) + (s : ℝ) * (L + 1) + budget + (s : ℝ) * A) := by
  have hB0 := hB.1
  have hBA := hB.2
  have hs : ((s + 1 : ℕ) : ℝ) ≤ Real.exp ((s + 1 : ℕ) : ℝ) := by
    linarith [Real.add_one_le_exp (((s + 1 : ℕ) : ℝ))]
  have hn' := recoveredChart_dimension_add_one_exp_bound n hL hn
  calc
    _ ≤ Real.exp ((s + 1 : ℕ) : ℝ) * (Real.exp (L + 1)) ^ s * Real.exp budget *
        (Real.exp A) ^ s := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add,
        ← Real.exp_add, ← Real.exp_add]

end Erdos3

end

end OAI
