import Mathlib
import OAI.Probability.BinarySweep.Analytic.OneAxisPerturbation
import OAI.Probability.BinarySweep.FiniteLaws.QuantitativeMoment
import OAI.Probability.BinarySweep.Conditional.MainEasyCases

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

def oneAxisRadius (r : ℕ) : ℝ :=
  (2 * (((2^(2*r) : ℕ).factorial : ℝ))^2)⁻¹

lemma oneAxisRadius_pos (r : ℕ) : 0 < oneAxisRadius r := by
  unfold oneAxisRadius
  positivity

lemma oneAxisRadius_le_half (r : ℕ) : oneAxisRadius r ≤ 1/2 := by
  have hB : (1 : ℝ) ≤ ((2^(2*r) : ℕ).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2^(2*r))
  unfold oneAxisRadius
  calc
    _ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by nlinarith)
    _ = 1/2 := by norm_num

lemma oneAxis_size_le {r : ℕ} {bits : Fin 1 → ℕ} (hd : ∀ j, bits j ≤ 2*r) :
    gridSize bits ≤ 2^(2*r) := by
  simp only [gridSize, Fin.prod_univ_one]
  exact Nat.pow_le_pow_right (by omega) (hd 0)

lemma oneAxis_norm_le_inv_dimension {r h D : ℕ} {bits : Fin 1 → ℕ}
    (hd : ∀ j, bits j ≤ 2*r) (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hzr : z ≤ oneAxisRadius r)
    (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (RepSpace D))
    [ρ.IsIrreducible] (hρ : IsUnitaryRep ρ) (hD : 1 < D) :
    ‖conditionalOperator H z ρ‖ ≤ (D : ℝ)⁻¹ := by
  let B : ℝ := ((2^(2*r) : ℕ).factorial : ℝ)
  have hB : 0 < B := by dsimp [B]; positivity
  have hfac : ((gridSize bits).factorial : ℝ) ≤ B := by
    dsimp [B]
    exact_mod_cast Nat.factorial_le (oneAxis_size_le hd)
  have hdim : D ≤ (gridSize bits).factorial := by
    have hbound := Irrep.finrank_le_card ρ
    simp only [finrank_euclideanSpace_fin, Fintype.card_perm, card_freeSlot] at hbound
    exact hbound.trans (Nat.factorial_le (Nat.sub_le _ _))
  have hDB : (D : ℝ) ≤ B := (by exact_mod_cast hdim :
    (D : ℝ) ≤ ((gridSize bits).factorial : ℝ)).trans hfac
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  calc
    _ ≤ 2 * ((gridSize bits).factorial : ℝ) * z :=
      oneAxis_conditional_norm_le H hz (hzr.trans (oneAxisRadius_le_half r)) ρ hρ hD
    _ ≤ 2 * B * oneAxisRadius r := by gcongr
    _ = B⁻¹ := by dsimp [oneAxisRadius, B]; field_simp
    _ ≤ (D : ℝ)⁻¹ := inv_anti₀ hD0 hDB

theorem conditional_moment_one_axis {r q : ℕ}
    (hr : (400000000 : ℝ) ≤ (r : ℝ) * Real.log 2) (hq : 0 < q)
    (bits : Fin 1 → ℕ) (hd : ∀ j, r ≤ bits j ∧ bits j ≤ 2*r)
    {h D : ℕ} (H : PathFamily bits h) {z : ℝ} (hz : 0 ≤ z)
    (hzr : z ≤ oneAxisRadius r)
    (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (RepSpace D))
    [ρ.IsIrreducible] (hρ : IsUnitaryRep ρ) :
    logMoment (traceMoment q (conditionalOperator H z ρ)) ≤
      ((-cExponent (gridSize bits) * Real.log D +
        eExponent (gridSize bits) * h * Real.log (gridSize bits) - pathCost H : ℝ) : EReal) := by
  have ha := grid_parameter_allowance (by omega : 1 ≤ 1) (fun j => (hd j).1) hr H
  have hl0 : 0 ≤ Real.log (gridSize bits) := Real.log_nonneg (by
    exact_mod_cast gridSize_pos bits)
  have hallow : 0 ≤ eExponent (gridSize bits) * h * Real.log (gridSize bits) - pathCost H := by
    apply le_trans _ ha.2.2
    unfold e0
    positivity
  by_cases hD : 1 < D
  · have hn := oneAxis_norm_le_inv_dimension (fun j => (hd j).2) H hz hzr ρ hρ hD
    apply (logMoment_le_neg_log_dimension (by omega) hq _ hn).trans
    have hc : cExponent (gridSize bits) ≤ 1 := by
      have := ha.1
      unfold c0 at this
      linarith
    have hlog : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ D))
    exact_mod_cast (show -Real.log D ≤ -cExponent (gridSize bits) * Real.log D +
      eExponent (gridSize bits) * h * Real.log (gridSize bits) - pathCost H by nlinarith)
  · have hlog : Real.log D = 0 := by
      have hD' : D = 0 ∨ D = 1 := by omega
      rcases hD' with rfl | rfl <;> norm_num
    apply conditional_moment_of_automatic_regime H hz
      (lt_of_le_of_lt (hzr.trans (oneAxisRadius_le_half r)) (by norm_num)) q ρ hρ
    simpa only [hlog, mul_zero] using hallow

end BinaryCoordinateSweeps

end

end OAI
