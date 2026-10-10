import OAI.NumberTheory.JointDickman.Analysis.MellinWindowProfile
import OAI.NumberTheory.JointDickman.Analysis.MellinLogWindows

namespace OAI

/-! # The support and central plateau of the logarithmic smoothing kernel -/
namespace JointDickman
open Finset
open scoped SchwartzMap

lemma logarithmicWindowProfile_zero_of_outside {η δ x y : ℝ}
    (hη : 0 < η) (hηhalf : η < 1/2) (hδ : 0 < δ) (hx : 0 < x) (hy : 0 < y)
    (hout : y ≤ x ∨ x * Real.exp δ ≤ y) :
    logarithmicWindowProfile η hη hηhalf ((Real.log x + δ - Real.log y) / δ) = 0 := by
  apply logarithmicWindowProfile_zero
  rcases hout with hlo | hhi
  · right
    apply (le_div_iff₀ hδ).mpr
    have hh := Real.log_le_log hy hlo
    linarith
  · left
    apply div_nonpos_of_nonpos_of_nonneg _ hδ.le
    have hh := Real.log_le_log (mul_pos hx (Real.exp_pos δ)) hhi
    rw [Real.log_mul hx.ne' (Real.exp_ne_zero δ), Real.log_exp] at hh
    linarith

lemma logarithmicWindowProfile_one_of_inside {η δ x y : ℝ}
    (hη : 0 < η) (hηhalf : η < 1/2) (hδ : 0 < δ) (hx : 0 < x) (hy : 0 < y)
    (hlo : x * Real.exp (η * δ) ≤ y)
    (hhi : y ≤ x * Real.exp ((1 - η) * δ)) :
    logarithmicWindowProfile η hη hηhalf ((Real.log x + δ - Real.log y) / δ) = 1 := by
  apply logarithmicWindowProfile_one
  constructor
  · apply (le_div_iff₀ hδ).mpr
    have hh := Real.log_le_log hy hhi
    rw [Real.log_mul hx.ne' (Real.exp_ne_zero _), Real.log_exp] at hh
    nlinarith
  · apply (div_le_iff₀ hδ).mpr
    have hh := Real.log_le_log (mul_pos hx (Real.exp_pos _)) hlo
    rw [Real.log_mul hx.ne' (Real.exp_ne_zero _), Real.log_exp] at hh
    nlinarith

/-- Enlarging the finite Dirichlet polynomial adds only zero kernel terms. -/
theorem mellinPacket_logarithmicWindow_support (f : ℕ → ℂ) {K N : ℕ} {η δ x : ℝ}
    (hη : 0 < η) (hηhalf : η < 1/2) (hδ : 0 < δ) (hx : 0 < x)
    (hK : K ≤ ⌊x⌋₊) (hN : ⌊x * Real.exp δ⌋₊ ≤ N) :
    mellinPacket (Ioc K N) f
      (normalizedSchwartzScale (logarithmicWindowProfile η hη hηhalf) δ hδ)
      (Real.log x + δ) =
    (∑ n ∈ Ioc ⌊x⌋₊ ⌊x * Real.exp δ⌋₊,
      (f n / (n : ℂ)) * logarithmicWindowProfile η hη hηhalf
        ((Real.log x + δ - Real.log (n : ℝ)) / δ)) / (δ : ℂ) := by
  rw [mellinPacket_apply]
  simp_rw [normalizedSchwartzScale_apply, ← mul_div_assoc]
  rw [← sum_div]
  congr 1
  symm
  apply sum_subset
  · intro n hn
    rcases mem_Ioc.mp hn with ⟨hlo, hhi⟩
    exact mem_Ioc.mpr ⟨hK.trans_lt hlo, hhi.trans hN⟩
  · intro n hn hnout
    have hn0 : 0 < (n : ℝ) := by
      have hh := (Nat.zero_le K).trans_lt (mem_Ioc.mp hn).1
      exact_mod_cast hh
    have hout : (n : ℝ) ≤ x ∨ x * Real.exp δ ≤ (n : ℝ) := by
      by_cases hnx : n ≤ ⌊x⌋₊
      · left
        exact (show (n : ℝ) ≤ (⌊x⌋₊ : ℝ) by exact_mod_cast hnx).trans (Nat.floor_le hx.le)
      · right
        have hnupper : ⌊x * Real.exp δ⌋₊ < n := by
          have : ¬ n ≤ ⌊x * Real.exp δ⌋₊ := by
            intro hh
            exact hnout (mem_Ioc.mpr ⟨Nat.lt_of_not_ge hnx, hh⟩)
          omega
        exact (Nat.lt_of_floor_lt hnupper).le
    rw [logarithmicWindowProfile_zero_of_outside hη hηhalf hδ hx hn0 hout, mul_zero]

end JointDickman

end OAI
