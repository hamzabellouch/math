import OAI.MeasureTheory.Falconer.Geometry.ProjectionRatioGeometry

namespace OAI

/-! The interpolation normalization is controlled by the same coefficient
bound as the scalar graph projection. -/
namespace Falconer

 theorem projectionRatio_normalizing_bound {a b y M : ℝ} (hy : y ≠ b)
    (hM : 1 ≤ M) (hc : |projectionRatio a b y| ≤ M) :
    |((b-a)/(b-y))/4| ≤ M := by
  have hby : b-y ≠ 0 := sub_ne_zero.mpr hy.symm
  have he : (b-a)/(b-y) = 1+projectionRatio a b y := by
    unfold projectionRatio
    field_simp
    ring
  rw [he,abs_div]
  norm_num
  have hh := abs_add_le (1:ℝ) (projectionRatio a b y)
  norm_num at hh
  linarith

 theorem projectionRatio_ne_pole {a b y : ℝ} (hc : projectionRatio a b y ≠ 0) : y ≠ b := by
  intro h
  subst y
  simp only [projectionRatio,sub_self,div_zero] at hc
  exact hc rfl

end Falconer

end OAI
