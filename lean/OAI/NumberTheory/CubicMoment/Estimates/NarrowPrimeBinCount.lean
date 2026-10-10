import OAI.NumberTheory.CubicMoment.Estimates.GeometricPrimeBins

namespace OAI

/-! Uniform bin counts when the geometric ratio is allowed to approach
one. The width loss is explicit, as required for logarithmic stopping bins. -/
noncomputable section
namespace CubicFirstMoment

lemma logarithm_one_add_lower {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) :
    δ/2 ≤ Real.log (1+δ) := by
  apply le_trans ?_ (Real.le_log_one_add_of_nonneg hδ.le)
  apply (le_div_iff₀ (by positivity : 0 < δ+2)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hδone hδ.le]

theorem geometricBinCount_width_bound {δ B : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hB : 1 ≤ B) :
    (geometricBinCount (1+δ) B:ℝ) ≤ 2*Real.log B/δ+1 := by
  have hlogδ := logarithm_one_add_lower hδ hδone
  have hlogpos : 0 < Real.log (1+δ) := (by positivity : 0 < δ/2).trans_le hlogδ
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hcount := (Nat.ceil_lt_add_one (div_nonneg hlogB hlogpos.le)).le
  change (geometricBinCount (1+δ) B:ℝ) ≤ _ at hcount
  apply hcount.trans
  refine add_le_add ?_ le_rfl
  calc
    Real.log B/Real.log (1+δ) ≤ Real.log B/(δ/2) :=
      div_le_div_of_nonneg_left hlogB (by positivity) hlogδ
    _ = 2*Real.log B/δ := by ring

end CubicFirstMoment

end

end OAI
