import OAI.Analysis.CircleDomains.Probability.CountableVisitNorm
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace OAI

/-! Real square norms of band widths are bounded by their ENNReal budgets,
including when the marked set is only a subset of the full budget support. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem real_square_norm_le_counting {A B : Type*}
    (v : A → ℝ) (w : B → ℝ≥0∞) (e : A → B) (he : Injective e)
    (hv : ∀ a, 0 ≤ v a) (hb : ∀ a, ENNReal.ofReal (v a) ≤ w (e a))
    (hw : (∑' b, w b ^ 2) < ∞) :
    Real.sqrt (∑' a, v a ^ 2) ≤ (countingSquareNorm w).toReal := by
  have hE : (∑' a, ENNReal.ofReal (v a ^ 2)) ≤ ∑' b, w b ^ 2 := by
    calc
      _ = ∑' a, ENNReal.ofReal (v a) ^ 2 := by
        congr 1
        funext a
        exact ENNReal.ofReal_pow (hv a) 2
      _ ≤ ∑' a, w (e a) ^ 2 := ENNReal.tsum_le_tsum
        (fun a => pow_le_pow_left' (hb a) 2)
      _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective he (fun b => w b ^ 2)
  have hr := ENNReal.toReal_mono hw.ne hE
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)] at hr
  simp only [ENNReal.toReal_ofReal (sq_nonneg _)] at hr
  rw [countingSquareNorm, ← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow]
  exact Real.sqrt_le_sqrt hr

end CircleDomainRigidity

end

end OAI
