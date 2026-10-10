import OAI.NumberTheory.CubicMoment.Estimates.CellMassAggregation

namespace OAI

/-! There are at most 2J populated cells in a dyadic norm interval.
The resulting all-pair mass bound uses the original coefficient energies. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma dyadic_logCell_card_bound (P : Finset Eisenstein) {J A : ℝ} (hJ : 1 ≤ J)
    (hP : ∀ a ∈ P, 1 ≤ norm a/A ∧ norm a/A ≤ 2) :
    ((P.image (logNormCell J A)).card:ℝ) ≤ 2*J := by
  have hJ0 : 0 ≤ J := le_trans zero_le_one hJ
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hr : ∀ a ∈ P, 0 ≤ J*Real.log (norm a/A) ∧
      J*Real.log (norm a/A) ≤ J*Real.log 2 := by
    intro a ha
    exact ⟨mul_nonneg hJ0 (Real.log_nonneg (hP a ha).1),
      mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith [(hP a ha).1]) (hP a ha).2) hJ0⟩
  have hc := logNormCell_count hr
  have hz : 0 ≤ ⌊J*Real.log 2⌋ := Int.floor_nonneg.mpr (mul_nonneg hJ0 hlog)
  have hci : ((P.image (logNormCell J A)).card:ℤ) ≤ ⌊J*Real.log 2⌋+1 := by omega
  have hcr : ((P.image (logNormCell J A)).card:ℝ) ≤ (⌊J*Real.log 2⌋:ℝ)+1 := by
    exact_mod_cast hci
  have hfl := Int.floor_le (J*Real.log 2)
  nlinarith [mul_le_mul_of_nonneg_left hlog1 hJ0]

lemma dyadic_logCell_pair_mass (P S : Finset Eisenstein) {J A B : ℝ} (hJ : 1 ≤ J)
    (hP : ∀ a ∈ P, 1 ≤ norm a/A ∧ norm a/A ≤ 2)
    (hS : ∀ b ∈ S, 1 ≤ norm b/B ∧ norm b/B ≤ 2)
    (E : Finset (ℤ × ℤ))
    (hE : E ⊆ (P.image (logNormCell J A)).product (S.image (logNormCell J B)))
    (α β : Eisenstein → ℂ) :
    (∑ e ∈ E, Real.sqrt (∑ a ∈ logNormCellSupport P J A e.1, ‖α a‖^2)*
      Real.sqrt (∑ b ∈ logNormCellSupport S J B e.2, ‖β b‖^2)) ≤
      2*J*Real.sqrt (∑ a ∈ P, ‖α a‖^2)*Real.sqrt (∑ b ∈ S, ‖β b‖^2) := by
  have hh := logCell_pair_mass_sum_le P S J A B E hE α β
  have hp := dyadic_logCell_card_bound P hJ hP
  have hs := dyadic_logCell_card_bound S hJ hS
  have hJ0 : 0 ≤ J := le_trans zero_le_one hJ
  have hroot : Real.sqrt ((P.image (logNormCell J A)).card:ℝ)*
      Real.sqrt ((S.image (logNormCell J B)).card:ℝ) ≤ 2*J := by
    calc
      _ ≤ Real.sqrt (2*J)*Real.sqrt (2*J) := mul_le_mul (Real.sqrt_le_sqrt hp)
        (Real.sqrt_le_sqrt hs) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt (by positivity)
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))

end CubicFirstMoment

end

end OAI
