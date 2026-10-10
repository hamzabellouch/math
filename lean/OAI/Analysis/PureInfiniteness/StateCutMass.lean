import OAI.Analysis.CStarAlgebra.PureInfiniteness.Cutoffs
import OAI.Analysis.TracialSplitting.MatrixNormalization

namespace OAI

/-! Quantitative preservation of state mass under the spectral cut used in
the product-state excision argument. -/

noncomputable section
open scoped ComplexOrder

namespace WeakPureInfiniteness

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem state_square_cut_pos (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1 = 1)
    (e : A) (he : 0 ≤ e) (hmass : 3 / 4 < (φ e).re) :
    0 < (φ (MainGap.cut (e * e) (1 / 4))).re := by
  have hs := PositiveLinearMap.norm_map_star_mul_sq_le φ (1 : A) e
  simp only [star_one, one_mul, hφ, norm_one, he.isSelfAdjoint.star_eq] at hs
  have hp : 0 ≤ e * e := by simpa only [he.isSelfAdjoint.star_eq] using star_mul_self_nonneg e
  have hr : (φ (e * e)).re = ‖φ (e * e)‖ := by
    exact congrArg Complex.re (Complex.eq_coe_norm_of_nonneg (map_nonneg φ hp))
  have hn := Complex.re_le_norm (φ e)
  have hsq : (3 / 4 : ℝ) ^ 2 < (φ (e * e)).re := by
    rw [hr]
    nlinarith [norm_nonneg (φ e)]
  have hcut := MainGap.norm_sub_cut_le hp (show (0 : ℝ) ≤ 1 / 4 by norm_num)
  have hb := (Complex.re_le_norm (φ (e * e - MainGap.cut (e * e) (1 / 4)))).trans
    ((CurrentMain.state_norm_le φ hφ _).trans hcut)
  rw [map_sub, Complex.sub_re] at hb
  nlinarith

end WeakPureInfiniteness

end

end OAI
