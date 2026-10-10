import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorTailEquation

namespace OAI

/-! The precise constant matrix and normalized nonlinear increment in the exterior error equation. -/

open scoped BoundedContinuousFunction
namespace DefocusingNLS

noncomputable def radialExteriorErrorMatrix (ν : ℂ) : (ℂ × ℂ) →L[ℝ] (ℂ × ℂ) :=
  (ContinuousLinearMap.snd ℝ ℂ ℂ).prod
    (-((2*ν+10) • ContinuousLinearMap.snd ℝ ℂ ℂ +
      (ν*(ν+10)) • ContinuousLinearMap.fst ℝ ℂ ℂ))

noncomputable def radialExteriorMatrixBound (ν : ℂ) : ℝ :=
  1+‖2*ν+10‖+‖ν*(ν+10)‖

theorem radialExteriorMatrixBound_pos (ν : ℂ) : 0 < radialExteriorMatrixBound ν := by
  unfold radialExteriorMatrixBound
  positivity

theorem radialExteriorErrorMatrix_norm (ν : ℂ) (v : ℂ × ℂ) :
    ‖radialExteriorErrorMatrix ν v‖ ≤ radialExteriorMatrixBound ν*‖v‖ := by
  change max ‖v.2‖ ‖-((2*ν+10)*v.2+(ν*(ν+10))*v.1)‖ ≤ _
  apply max_le
  · calc
      _ ≤ ‖v‖ := norm_snd_le v
      _ ≤ radialExteriorMatrixBound ν*‖v‖ := by
        unfold radialExteriorMatrixBound
        nlinarith [norm_nonneg (2*ν+10),norm_nonneg (ν*(ν+10)),norm_nonneg v]
  · rw [norm_neg]
    calc
      _ ≤ ‖(2*ν+10)*v.2‖+‖(ν*(ν+10))*v.1‖ := norm_add_le _ _
      _ = ‖2*ν+10‖*‖v.2‖+‖ν*(ν+10)‖*‖v.1‖ := by rw [norm_mul,norm_mul]
      _ ≤ ‖2*ν+10‖*‖v‖+‖ν*(ν+10)‖*‖v‖ := by
        gcongr
        · exact norm_snd_le v
        · exact norm_fst_le v
      _ ≤ radialExteriorMatrixBound ν*‖v‖ := by
        unfold radialExteriorMatrixBound
        nlinarith [norm_nonneg v]

noncomputable def radialExteriorWeightedIncrement (κ : ℝ) (N : ℂ → ℂ)
    (f : ℝ → ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  (Real.exp (κ*t) : ℂ)*(N (f t+(Real.exp (-κ*t) : ℂ)*z)-N (f t))

theorem radialExteriorWeightedIncrement_difference (κ L : ℝ)
    (N : ℂ → ℂ) (hLip : ∀ z w, ‖N z-N w‖ ≤ L*‖z-w‖)
    (f : ℝ → ℂ) (t : ℝ) (z w : ℂ) :
    ‖radialExteriorWeightedIncrement κ N f t z-
      radialExteriorWeightedIncrement κ N f t w‖ ≤ L*‖z-w‖ := by
  have he : Real.exp (κ*t)*Real.exp (-κ*t)=1 := by
    rw [← Real.exp_add]
    simp
  unfold radialExteriorWeightedIncrement
  rw [← mul_sub,sub_sub_sub_cancel_right,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (κ*t)*(L*‖f t+(Real.exp (-κ*t) : ℂ)*z-
        (f t+(Real.exp (-κ*t) : ℂ)*w)‖) :=
      mul_le_mul_of_nonneg_left (hLip _ _) (Real.exp_nonneg _)
    _ = L*‖z-w‖ := by
      rw [add_sub_add_left_eq_sub,← mul_sub,norm_mul,Complex.norm_real,
        Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      calc
        _ = (Real.exp (κ*t)*Real.exp (-κ*t))*(L*‖z-w‖) := by ring
        _ = _ := by rw [he,one_mul]

noncomputable def radialExteriorErrorField (κ : ℝ) (ν : ℂ) (N : ℂ → ℂ)
    (f : ℝ → ℂ) (r : ℝ →ᵇ ℂ × ℂ) (t : ℝ) (z : ℂ × ℂ) : ℂ × ℂ :=
  radialExteriorErrorMatrix ν z + (0,radialExteriorWeightedIncrement κ N f t z.1) + r t

theorem radialExteriorErrorField_continuous (κ : ℝ) (ν : ℂ) (N : ℂ → ℂ)
    (hN : Continuous N) (f : ℝ → ℂ) (hf : Continuous f) (r : ℝ →ᵇ ℂ × ℂ) :
    Continuous (Function.uncurry (radialExteriorErrorField κ ν N f r)) := by
  unfold radialExteriorErrorField radialExteriorWeightedIncrement Function.uncurry
  fun_prop

theorem radialExteriorErrorField_zero (κ : ℝ) (ν : ℂ) (N : ℂ → ℂ)
    (f : ℝ → ℂ) (r : ℝ →ᵇ ℂ × ℂ) (t : ℝ) :
    radialExteriorErrorField κ ν N f r t 0=r t := by
  simp [radialExteriorErrorField,radialExteriorWeightedIncrement]

theorem radialExteriorErrorField_difference (κ L : ℝ) (hL : 0 ≤ L) (ν : ℂ)
    (N : ℂ → ℂ) (hLip : ∀ z w, ‖N z-N w‖ ≤ L*‖z-w‖)
    (f : ℝ → ℂ) (r : ℝ →ᵇ ℂ × ℂ) (t : ℝ) (z w : ℂ × ℂ) :
    ‖radialExteriorErrorField κ ν N f r t z-radialExteriorErrorField κ ν N f r t w‖ ≤
      (radialExteriorMatrixBound ν+L)*‖z-w‖ := by
  have he : radialExteriorErrorField κ ν N f r t z-radialExteriorErrorField κ ν N f r t w =
      radialExteriorErrorMatrix ν (z-w) +
        (0,radialExteriorWeightedIncrement κ N f t z.1-
          radialExteriorWeightedIncrement κ N f t w.1) := by
    simp only [radialExteriorErrorField,map_sub]
    rw [show ((0 : ℂ),radialExteriorWeightedIncrement κ N f t z.1-
        radialExteriorWeightedIncrement κ N f t w.1) =
      (0,radialExteriorWeightedIncrement κ N f t z.1)-
        (0,radialExteriorWeightedIncrement κ N f t w.1) by simp]
    abel
  rw [he]
  calc
    _ ≤ ‖radialExteriorErrorMatrix ν (z-w)‖+
        ‖(0,radialExteriorWeightedIncrement κ N f t z.1-
          radialExteriorWeightedIncrement κ N f t w.1)‖ := norm_add_le _ _
    _ ≤ radialExteriorMatrixBound ν*‖z-w‖+L*‖z-w‖ := by
      apply add_le_add (radialExteriorErrorMatrix_norm ν (z-w))
      rw [Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)]
      exact (radialExteriorWeightedIncrement_difference κ L N hLip f t z.1 w.1).trans
        (mul_le_mul_of_nonneg_left (norm_fst_le (z-w)) hL)
    _ = _ := by ring

end DefocusingNLS

end OAI
