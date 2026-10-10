import OAI.Analysis.KadisonSimilarity.FreeProduct.DihedralArcProjection

namespace OAI

/-! Centering an orthogonal projection at one half gives norm at most one half. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_projection_sub_half_le (P : H →L[ℂ] H) (hP : IsStarProjection P) :
    ‖P - (1 / 2 : ℝ) • 1‖ ≤ 1 / 2 := by
  have hP1 : P ≤ 1 := sub_nonneg.mp hP.one_sub.nonneg
  have hlo : -((1 / 2 : ℝ) • (1 : H →L[ℂ] H)) ≤ P - (1 / 2 : ℝ) • 1 := by
    simpa only [zero_sub] using sub_le_sub_right hP.nonneg ((1 / 2 : ℝ) • 1)
  have hone : (1 : H →L[ℂ] H) - (1 / 2 : ℝ) • 1 = (1 / 2 : ℝ) • 1 := by
    calc
      _ = (1 : ℝ) • (1 : H →L[ℂ] H) - (1 / 2 : ℝ) • 1 := by rw [one_smul]
      _ = (1 - 1 / 2 : ℝ) • (1 : H →L[ℂ] H) := (sub_smul _ _ _).symm
      _ = (1 / 2 : ℝ) • (1 : H →L[ℂ] H) := by norm_num
  have hhi : P - (1 / 2 : ℝ) • 1 ≤ (1 / 2 : ℝ) • 1 := by
    simpa only [hone] using sub_le_sub_right hP1 ((1 / 2 : ℝ) • 1)
  have hself : IsSelfAdjoint (P - (1 / 2 : ℝ) • 1) :=
    hP.isSelfAdjoint.sub ((IsSelfAdjoint.all (1 / 2 : ℝ)).smul (IsSelfAdjoint.one _))
  have h := IsSelfAdjoint.norm_le_max_of_le_of_le hlo hhi hself
  have hn : ‖(1 / 2 : ℝ) • (1 : H →L[ℂ] H)‖ ≤ 1 / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact mul_le_of_le_one_right (by norm_num) ContinuousLinearMap.norm_id_le
  exact h.trans (by simpa only [norm_neg, max_self] using hn)

end KadisonSimilarity

end

end OAI
