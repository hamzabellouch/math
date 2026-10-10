import OAI.Combinatorics.EditApproximation.Coarse.CoarseInitialWork

namespace OAI

/-! The direct long-target branch removes dependence of initial-entry
work on the target interval width. This is the source-width charge used
when coarse leaves are summed over the physical dependency tree. -/

namespace EditApproximation

open MeasureTheory

theorem coarseInitialArrayWork_expected_source_width {α : Type*} [DecidableEq α]
    {B D : ℕ} [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (Q lam : ℚ) (x y : List α) (N : ℕ)
    (hsize : coarseEntryWidth x y ≤ N) (hcapacity : coarseEntryWidth x y ≤ B ^ D)
    (hQ : 0 < Q) (hlam : 0 < lam) (factor : ℝ) (hfactor : 1 ≤ factor)
    (hinverse : coarseInverseAllowanceFactor B Q lam ≤ factor) :
    (∫ draws, (coarseInitialArrayWork B D Q lam x y draws : ℝ)
      ∂coarseInitialMeasure B D (coarseEntryWidth x y)) ≤
    6 * B * x.length * (Nat.clog 2 N + 1 : ℕ) * (D + 1 : ℕ) * factor ^ D := by
  have hnonneg : 0 ≤ factor := le_trans (by norm_num) hfactor
  by_cases hlong : 2 * x.length < y.length
  · have hzero (draws) : coarseInitialArrayWork B D Q lam x y draws = 0 := by
      simp only [coarseInitialArrayWork, ite_eq_left hlong]
    simp only [hzero, Nat.cast_zero, integral_zero]
    positivity
  · have hwidth : coarseEntryWidth x y ≤ 2 * x.length := by
      unfold coarseEntryWidth
      omega
    have hlog := Nat.clog_mono_right 2 hsize
    have h := coarseInitialArrayWork_expected_bound Q lam x y hcapacity hQ hlam factor hfactor hinverse
    apply h.trans
    calc
      3 * B * coarseEntryWidth x y * (Nat.clog 2 (coarseEntryWidth x y) + 1 : ℕ) *
          (D + 1 : ℕ) * factor ^ D ≤
        3 * B * (2 * (x.length : ℝ)) * (Nat.clog 2 N + 1 : ℕ) * (D + 1 : ℕ) * factor ^ D := by
          gcongr
          · exact_mod_cast hwidth
      _ = _ := by ring

end EditApproximation

end OAI
