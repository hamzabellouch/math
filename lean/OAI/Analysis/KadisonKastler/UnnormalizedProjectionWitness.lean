import OAI.Analysis.KadisonKastler.NormalizedCornerGeometry

namespace OAI

/-! # Returning the projection estimates to the original corner vectors -/

namespace KadisonKastler

open NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem norm_apply_normalize_sq (T : H →L[ℂ] H) (x : H) :
    ‖T x‖^2=‖x‖^2*‖T (normalize x)‖^2 := by
  calc
    _ = ‖T (‖x‖ • normalize x)‖^2 := by rw [norm_smul_normalize]
    _ = _ := by
      rw [ContinuousLinearMap.map_smul_of_tower,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg x),mul_pow]

theorem projection_witness_unnormalize
    (J : H ≃ₗᵢ⋆[ℂ] H) (x y : H) (p : H →L[ℂ] H)
    (hx : ‖x‖≤1) (hy : ‖y‖≤1) (hy' : 1/2≤‖y‖^2)
    (θ δ : ℝ) (hθ : 1/2≤θ) (hδ : 0 < δ)
    (hm : θ*(‖p (normalize x)‖^2+‖p (normalize y)‖^2) <
      16384*‖centralVectorDefect J (normalize y) p‖^2)
    (hd : ‖centralVectorDefect J (normalize x) p‖^2 <
      (δ/2)*‖centralVectorDefect J (normalize y) p‖^2) :
    ‖p x‖^2+‖p y‖^2 < 65536*‖centralVectorDefect J y p‖^2 ∧
      ‖centralVectorDefect J x p‖^2 < δ*‖centralVectorDefect J y p‖^2 := by
  let D : H →L[ℂ] H := p-conjugationOperator J (star p)
  have he (z : H) : centralVectorDefect J z p=D z := rfl
  simp only [he] at hm hd ⊢
  have hxx : ‖x‖^2≤1 := by nlinarith only [norm_nonneg x,hx]
  have hyy : ‖y‖^2≤1 := by nlinarith only [norm_nonneg y,hy]
  have hpx := norm_apply_normalize_sq p x
  have hpy := norm_apply_normalize_sq p y
  have hDx := norm_apply_normalize_sq D x
  have hDy := norm_apply_normalize_sq D y
  have hpx' : ‖p x‖^2≤‖p (normalize x)‖^2 := by
    rw [hpx]
    exact mul_le_of_le_one_left (sq_nonneg _) hxx
  have hpy' : ‖p y‖^2≤‖p (normalize y)‖^2 := by
    rw [hpy]
    exact mul_le_of_le_one_left (sq_nonneg _) hyy
  have hDx' : ‖D x‖^2≤‖D (normalize x)‖^2 := by
    rw [hDx]
    exact mul_le_of_le_one_left (sq_nonneg _) hxx
  have hDy' : ‖D (normalize y)‖^2≤2*‖D y‖^2 := by
    have hh := mul_le_mul_of_nonneg_right hy' (sq_nonneg ‖D (normalize y)‖)
    rw [← hDy] at hh
    linarith only [hh]
  constructor
  · have hmass := sq_nonneg ‖p (normalize x)‖
    have hmass' := sq_nonneg ‖p (normalize y)‖
    have hθmass := mul_le_mul_of_nonneg_right hθ (add_nonneg hmass hmass')
    have hn : ‖p (normalize x)‖^2+‖p (normalize y)‖^2 <
        32768*‖D (normalize y)‖^2 := by linarith only [hθmass,hm]
    linarith only [hpx',hpy',hn,hDy']
  · have hh := mul_le_mul_of_nonneg_left hDy' (show 0≤δ/2 by positivity)
    nlinarith only [hDx',hd,hh]

end

end KadisonKastler

end OAI
