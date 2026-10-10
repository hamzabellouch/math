import Mathlib
import OAI.Probability.BinarySweep.FiniteLaws.MomentBounds
import OAI.Probability.BinarySweep.Trajectories.PathExtension

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

lemma grid_log_lower {b r : ℕ} {bits : Fin b → ℕ} (hd : ∀ j, r ≤ bits j) :
    (b : ℝ) * ((r : ℝ) * Real.log 2) ≤ Real.log (gridSize bits) := by
  calc
    _ = ∑ _j : Fin b, (r : ℝ) * Real.log 2 := by simp
    _ ≤ ∑ j : Fin b, (bits j : ℝ) * Real.log 2 := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hd j)
      exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    _ = _ := by
      rw [log_gridSize]
      simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

lemma grid_parameter_allowance {b h r : ℕ} {bits : Fin b → ℕ}
    (hb : 1 ≤ b) (hd : ∀ j, r ≤ bits j)
    (hr : (400000000 : ℝ) ≤ (r : ℝ) * Real.log 2) (H : PathFamily bits h) :
    cExponent (gridSize bits) ≤ 2*c0 ∧
    e0/2 ≤ eExponent (gridSize bits) ∧
    (e0/4) * h * Real.log (gridSize bits) ≤
      eExponent (gridSize bits) * h * Real.log (gridSize bits) - pathCost H := by
  have hlogb := grid_log_lower hd
  have hbc : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbn : (0 : ℝ) ≤ b := by positivity
  have hm := mul_le_mul_of_nonneg_left hr hbn
  have hbl : (400000000 : ℝ) * b ≤ Real.log (gridSize bits) := by nlinarith
  have hl : (400000000 : ℝ) ≤ Real.log (gridSize bits) := by nlinarith
  have hs : (20000 : ℝ) ≤ Real.sqrt (Real.log (gridSize bits)) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact hl
  have hs' : 1 / Real.sqrt (Real.log (gridSize bits)) ≤ (1 / 20000 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hs
  have hc : cExponent (gridSize bits) ≤ 2*c0 := by
    unfold cExponent c0
    linarith
  have he : e0/2 ≤ eExponent (gridSize bits) := by
    unfold eExponent e0
    linarith
  refine ⟨hc, he, ?_⟩
  have hh : (0 : ℝ) ≤ h := by positivity
  have hl0 : 0 ≤ Real.log (gridSize bits) := by linarith
  have he' := mul_le_mul_of_nonneg_right he (mul_nonneg hh hl0)
  have hbb : (b : ℝ) ≤ (e0/4) * Real.log (gridSize bits) := by
    unfold e0
    nlinarith
  have hcost := (pathCost_le H).trans (mul_le_mul_of_nonneg_right hbb hh)
  nlinarith

lemma exists_main_scale : ∃ r : ℕ, 0 < r ∧ (400000000 : ℝ) ≤ (r : ℝ) * Real.log 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨r, hr⟩ := exists_nat_gt ((400000000 : ℝ) / Real.log 2)
  have hr' : (400000000 : ℝ) < (r : ℝ) * Real.log 2 := (div_lt_iff₀ hl).mp hr
  refine ⟨r, ?_, hr'.le⟩
  have hp : (0 : ℝ) < r := by nlinarith
  exact_mod_cast hp

theorem conditional_moment_one_dimensional :
    ∃ r : ℕ, 0 < r ∧ ∃ zStar : ℝ, 0 < zStar ∧
      ∀ b : ℕ, 1 ≤ b → ∀ bits : Fin b → ℕ, (∀ j, r ≤ bits j ∧ bits j ≤ 2*r) →
      ∀ h : ℕ, ∀ H : PathFamily bits h, ∀ z : ℝ, 0 ≤ z → z ≤ zStar →
      ∀ q : ℕ, ∀ ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (RepSpace 1),
        IsUnitaryRep ρ →
        logMoment (traceMoment q (conditionalOperator H z ρ)) ≤
          ((-cExponent (gridSize bits) * Real.log (1 : ℕ) +
            eExponent (gridSize bits) * h * Real.log (gridSize bits) - pathCost H : ℝ) : EReal) := by
  obtain ⟨r, hr0, hr⟩ := exists_main_scale
  refine ⟨r, hr0, 1/2, by norm_num, ?_⟩
  intro b hb bits hd h H z hz hzr q ρ hρ
  have hz1 : z < 1 := by linarith
  apply conditional_moment_of_automatic_regime H hz hz1 q ρ hρ
  have ha := (grid_parameter_allowance hb (fun j => (hd j).1) hr H).2.2
  have hl0 : 0 ≤ Real.log (gridSize bits) := Real.log_nonneg (by
    exact_mod_cast gridSize_pos bits)
  have hn : 0 ≤ (e0/4) * h * Real.log (gridSize bits) := by
    unfold e0
    positivity
  simpa only [Nat.cast_one, Real.log_one, mul_zero] using hn.trans ha

end BinaryCoordinateSweeps

end

end OAI
