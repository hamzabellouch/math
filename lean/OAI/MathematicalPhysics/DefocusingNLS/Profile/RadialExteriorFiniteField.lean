import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorCutoff
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorFieldDifference

namespace OAI

/-! A global clipped vector field around the free exterior path on a finite interval. -/

namespace DefocusingNLS

noncomputable def radialExteriorFiniteField (ν : ℂ) (n : ℕ) (m : ℝ → ℂ) (δ : ℝ)
    (t : ℝ) (z : ℂ × ℂ) : ℂ × ℂ :=
  (0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*z.2)+radialExteriorErrorMatrix ν z+
    (0,radialExteriorCutoffPower n (m t) δ z.1)

theorem radialExteriorFiniteField_continuous (ν : ℂ) (n : ℕ) (m : ℝ → ℂ)
    (hm : Continuous m) (δ : ℝ) :
    Continuous (Function.uncurry (radialExteriorFiniteField ν n m δ)) := by
  unfold radialExteriorFiniteField radialExteriorCutoffPower oddPowerNonlinearity
    radialComplexClamp radialAmplitudeClamp Function.uncurry
  fun_prop

theorem radialExteriorFiniteField_eq (ν : ℂ) (n : ℕ) (m : ℝ → ℂ) (δ t : ℝ)
    (z : ℂ × ℂ) (hz : ‖z.1-m t‖ ≤ δ) :
    radialExteriorFiniteField ν n m δ t z=
      (z.2,-(2*ν+10+Complex.I*(Real.exp (2*t)/2 : ℝ))*z.2-
        ν*(ν+10)*z.1+oddPowerNonlinearity n z.1) := by
  rw [radialExteriorFiniteField,radialExteriorCutoffPower_eq n (m t) δ z.1 hz]
  apply Prod.ext
  all_goals simp [radialExteriorErrorMatrix]
  ring

theorem radialExteriorFiniteField_difference (ν : ℂ) (n : ℕ) (m : ℝ → ℂ)
    (δ ρ t : ℝ) (hδ : 0 ≤ δ) (hρ : ‖m t‖+2*δ ≤ ρ) (z w : ℂ × ℂ) :
    ‖radialExteriorFiniteField ν n m δ t z-radialExteriorFiniteField ν n m δ t w‖ ≤
      (radialExteriorMatrixBound ν+Real.exp (2*t)/2+
        2*(2*(n : ℝ)+1)*ρ^(2*n))*‖z-w‖ := by
  have hρ0 : 0 ≤ ρ := (by positivity : 0 ≤ ‖m t‖+2*δ).trans hρ
  have hsplit : radialExteriorFiniteField ν n m δ t z-radialExteriorFiniteField ν n m δ t w=
      radialExteriorErrorMatrix ν (z-w)+(0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(z-w).2)+
        (0,radialExteriorCutoffPower n (m t) δ z.1-radialExteriorCutoffPower n (m t) δ w.1) := by
    rw [map_sub]
    apply Prod.ext
    all_goals simp [radialExteriorFiniteField]
    ring
  have hd : ‖((0 : ℂ),-Complex.I*(Real.exp (2*t)/2 : ℝ)*(z-w).2)‖ ≤
      Real.exp (2*t)/2*‖z-w‖ := by
    rw [Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)]
    simp only [norm_mul,norm_neg,Complex.norm_I,one_mul,
      Complex.norm_real,Real.norm_eq_abs]
    rw [abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_snd_le (z-w)) (by positivity)
  have hn : ‖((0 : ℂ),radialExteriorCutoffPower n (m t) δ z.1-
      radialExteriorCutoffPower n (m t) δ w.1)‖ ≤ 2*(2*(n : ℝ)+1)*ρ^(2*n)*‖z-w‖ := by
    simp only [Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)]
    apply (radialExteriorCutoffPower_difference n (m t) δ hδ z.1 w.1).trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hρ _) (by positivity)
    · exact norm_fst_le (z-w)
    · positivity
    · positivity
  rw [hsplit]
  calc
    _ ≤ ‖radialExteriorErrorMatrix ν (z-w)‖+
        ‖((0 : ℂ),-Complex.I*(Real.exp (2*t)/2 : ℝ)*(z-w).2)‖+
        ‖((0 : ℂ),radialExteriorCutoffPower n (m t) δ z.1-radialExteriorCutoffPower n (m t) δ w.1)‖ :=
      @norm_add₃_le (ℂ × ℂ) _ _ _ _
    _ ≤ radialExteriorMatrixBound ν*‖z-w‖+Real.exp (2*t)/2*‖z-w‖+
        2*(2*(n : ℝ)+1)*ρ^(2*n)*‖z-w‖ := add_le_add (add_le_add (radialExteriorErrorMatrix_norm ν (z-w)) hd) hn
    _ = _ := by ring


theorem radialExteriorFiniteField_linear_difference (ν μ : ℂ) (n : ℕ) (m : ℝ → ℂ)
    (δ ρ t : ℝ) (hδ : 0 ≤ δ) (hρ : ‖m t‖+2*δ ≤ ρ) (z : ℂ × ℂ) :
    ‖radialExteriorFiniteField ν n m δ t z-
      ((0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*z.2)+radialExteriorErrorMatrix μ z)‖ ≤
        radialExteriorMatrixDifference ν μ*‖z‖+ρ^(2*n+1) := by
  have he : radialExteriorFiniteField ν n m δ t z-
      ((0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*z.2)+radialExteriorErrorMatrix μ z)=
      (radialExteriorErrorMatrix ν z-radialExteriorErrorMatrix μ z)+
        (0,radialExteriorCutoffPower n (m t) δ z.1) := by
    unfold radialExteriorFiniteField
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add (radialExteriorErrorMatrix_difference ν μ z)
  rw [Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)]
  simp only [radialExteriorCutoffPower,radial_oddPower_norm]
  exact pow_le_pow_left₀ (norm_nonneg _)
    ((radialComplexClamp_bound (m t) δ hδ z.1).trans hρ) _

end DefocusingNLS

end OAI
