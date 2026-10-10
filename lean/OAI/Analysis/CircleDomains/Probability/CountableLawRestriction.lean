import OAI.Analysis.CircleDomains.Probability.CodeLawCandidateBounds

namespace OAI

/-! Restriction of the full mean-visit bound to any injectively indexed
subfamily of the prescribed marks. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem countingSquareNorm_comp_injective {A B : Type*} (v : B → ℝ≥0∞)
    (e : A → B) (he : Injective e) : countingSquareNorm (v ∘ e) ≤ countingSquareNorm v := by
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  exact ENNReal.tsum_comp_le_tsum_of_injective he (fun b => v b ^ 2)

theorem countingSquareNorm_restrict_range {X A B : Type*} (v : X → ℝ≥0∞)
    (a : A → X) (b : B → X) (ha : Injective a) (hab : range a ⊆ range b) :
    countingSquareNorm (v ∘ a) ≤ countingSquareNorm (v ∘ b) := by
  classical
  choose e he using fun s => hab (mem_range_self s)
  have hinj : Injective e := by
    intro s t h
    apply ha
    rw [← he s, ← he t, h]
  simpa only [Function.comp_def, he] using
    countingSquareNorm_comp_injective (v ∘ b) e hinj

end CircleDomainRigidity

end

end OAI
