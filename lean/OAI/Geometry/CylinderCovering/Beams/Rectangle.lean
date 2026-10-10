import OAI.Geometry.CylinderCovering.Beams.BeamStrip

namespace OAI

noncomputable section
open Set
open scoped InnerProductSpace
namespace CylinderCovering.BeamStrip

theorem rectangle_isRectangle {q A l r : ℝ} (hA : 0 < A) (hlr : l < r) :
    IsRectangle (rectangle q A l r) := by
  refine ⟨(-A) • normal q + l • vertical, (2*A) • normal q,
    (r-l) • vertical, ?_, ?_, ?_, ?_⟩
  · simp [inner_smul_left, inner_smul_right, normal_vertical_inner]
  · exact smul_ne_zero (by positivity) (by
      intro h; have := normal_norm q; rw [h, norm_zero] at this; norm_num at this)
  · exact smul_ne_zero (sub_ne_zero.mpr hlr.ne') (by
      intro h; have := vertical_norm; rw [h, norm_zero] at this; norm_num at this)
  · ext z
    constructor
    · rintro ⟨s, hs, t, ht, rfl⟩
      refine ⟨(s+A)/(2*A), ?_, (t-l)/(r-l), ?_, ?_⟩
      · constructor
        · exact div_nonneg (by linarith [hs.1]) (by positivity)
        · apply (div_le_one (by positivity : 0 < 2*A)).mpr; linarith [hs.2]
      · constructor
        · exact div_nonneg (by linarith [ht.1]) (by linarith)
        · apply (div_le_one (by linarith : 0 < r-l)).mpr; linarith [ht.2]
      · have h1 : (s+A)/(2*A)*(2*A) = s+A := div_mul_cancel₀ _ (by positivity)
        have h2 : (t-l)/(r-l)*(r-l) = t-l := div_mul_cancel₀ _ (sub_ne_zero.mpr hlr.ne')
        simp only [smul_smul, h1, h2]
        module
    · rintro ⟨s, hs, t, ht, rfl⟩
      refine ⟨-A+s*(2*A), ?_, l+t*(r-l), ?_, ?_⟩
      · constructor <;> nlinarith [mul_nonneg hs.1 hA.le,
          mul_nonneg (sub_nonneg.mpr hs.2) hA.le]
      · constructor <;> nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hlr.le),
          mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hlr.le)]
      · simp only [smul_smul]
        module

theorem IsHorizontalRectangle.hasRectangularBase {C : RuledApproximation.Cylinder}
    (hC : IsHorizontalRectangle C) : HasRectangularBase C := by
  obtain ⟨q,A,l,r,hA,hlr,_,hbase⟩ := hC
  unfold HasRectangularBase
  rw [hbase]
  exact rectangle_isRectangle hA hlr

end CylinderCovering.BeamStrip

end

end OAI
