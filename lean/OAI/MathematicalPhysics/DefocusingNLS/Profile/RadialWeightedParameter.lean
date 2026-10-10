import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorNonlinearTail

namespace OAI

/-! Parameter perturbations of the weighted nonlinear tail increment. -/

namespace DefocusingNLS

theorem radialWeightedIncrement_base_lipschitz
    (n : ℕ) (m : ℂ) (δ κ T W C M : ℝ)
    (hδ : 0 ≤ δ) (hκ : 0 ≤ κ) (hW : 0 ≤ W) (hC : 0 ≤ C)
    (hM : ‖m‖+δ ≤ M) (hsmall : Real.exp (-κ*T)*W ≤ δ/2)
    (hmixed : ∀ a b h : ℂ, ‖a‖ ≤ M → ‖b‖ ≤ M → ‖h‖ ≤ M →
      ‖(oddPowerNonlinearity n (a+h)-oddPowerNonlinearity n a)-
        (oddPowerNonlinearity n (b+h)-oddPowerNonlinearity n b)‖ ≤
          C*‖a-b‖*‖h‖)
    (f g : ℝ → ℂ) (t : ℝ) (z : ℂ)
    (hf : ‖f t-m‖ ≤ δ/2) (hg : ‖g t-m‖ ≤ δ/2) (hz : ‖z‖ ≤ W) :
    ‖radialExteriorWeightedIncrement κ (radialExteriorCutoffPower n m δ) f t z-
      radialExteriorWeightedIncrement κ (radialExteriorCutoffPower n m δ) g t z‖ ≤
      (2*radialExteriorCutoffRate n m δ*Real.exp (κ*T)+C*W)*‖f t-g t‖ := by
  let L := radialExteriorCutoffRate n m δ
  have hL : 0 ≤ L := radialExteriorCutoffRate_nonneg n m δ
  have hLip := radialExteriorCutoffPower_difference n m δ hδ
  let h : ℂ := (Real.exp (-κ*t) : ℂ)*z
  have hn : ‖h‖=Real.exp (-κ*t)*‖z‖ := by
    simp only [h,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (κ*t)*Real.exp (-κ*t)=1 := by
    rw [← Real.exp_add]
    simp
  have heq : radialExteriorWeightedIncrement κ (radialExteriorCutoffPower n m δ) f t z-
      radialExteriorWeightedIncrement κ (radialExteriorCutoffPower n m δ) g t z =
      (Real.exp (κ*t) : ℂ)*
        ((radialExteriorCutoffPower n m δ (f t+h)-radialExteriorCutoffPower n m δ (f t))-
          (radialExteriorCutoffPower n m δ (g t+h)-radialExteriorCutoffPower n m δ (g t))) := by
    unfold radialExteriorWeightedIncrement
    dsimp [h]
    ring
  rw [heq,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  by_cases ht : T ≤ t
  · have hh : ‖h‖ ≤ δ/2 := calc
      _ = Real.exp (-κ*t)*‖z‖ := hn
      _ ≤ Real.exp (-κ*T)*W := mul_le_mul
        (Real.exp_le_exp.mpr (by nlinarith)) hz (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ _ := hsmall
    have hfh : ‖f t+h-m‖ ≤ δ := calc
      _ = ‖(f t-m)+h‖ := by congr 1; ring
      _ ≤ ‖f t-m‖+‖h‖ := norm_add_le _ _
      _ ≤ _ := by linarith
    have hgh : ‖g t+h-m‖ ≤ δ := calc
      _ = ‖(g t-m)+h‖ := by congr 1; ring
      _ ≤ ‖g t-m‖+‖h‖ := norm_add_le _ _
      _ ≤ _ := by linarith
    rw [radialExteriorCutoffPower_eq n m δ _ hfh,
      radialExteriorCutoffPower_eq n m δ _ (hf.trans (by linarith)),
      radialExteriorCutoffPower_eq n m δ _ hgh,
      radialExteriorCutoffPower_eq n m δ _ (hg.trans (by linarith))]
    have hfa : ‖f t‖ ≤ M := calc
      _ ≤ ‖f t-m‖+‖m‖ := norm_le_norm_sub_add _ _
      _ ≤ _ := by linarith
    have hga : ‖g t‖ ≤ M := calc
      _ ≤ ‖g t-m‖+‖m‖ := norm_le_norm_sub_add _ _
      _ ≤ _ := by linarith
    have hha : ‖h‖ ≤ M := by linarith [norm_nonneg m]
    calc
      _ ≤ Real.exp (κ*t)*(C*‖f t-g t‖*‖h‖) :=
        mul_le_mul_of_nonneg_left (hmixed _ _ _ hfa hga hha) (Real.exp_pos _).le
      _ = C*‖f t-g t‖*‖z‖ := by rw [hn]; calc
        _ = (Real.exp (κ*t)*Real.exp (-κ*t))*(C*‖f t-g t‖*‖z‖) := by ring
        _ = _ := by rw [he,one_mul]
      _ ≤ C*‖f t-g t‖*W := mul_le_mul_of_nonneg_left hz (by positivity)
      _ = (C*W)*‖f t-g t‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (mul_nonneg (mul_nonneg (by norm_num) hL)
          (Real.exp_pos _).le)) (norm_nonneg _)
  · have hb : ‖(radialExteriorCutoffPower n m δ (f t+h)-radialExteriorCutoffPower n m δ (f t))-
        (radialExteriorCutoffPower n m δ (g t+h)-radialExteriorCutoffPower n m δ (g t))‖ ≤
        2*L*‖f t-g t‖ := by
      have hh : (radialExteriorCutoffPower n m δ (f t+h)-radialExteriorCutoffPower n m δ (f t))-
          (radialExteriorCutoffPower n m δ (g t+h)-radialExteriorCutoffPower n m δ (g t)) =
          (radialExteriorCutoffPower n m δ (f t+h)-radialExteriorCutoffPower n m δ (g t+h))-
            (radialExteriorCutoffPower n m δ (f t)-radialExteriorCutoffPower n m δ (g t)) := by ring
      rw [hh]
      apply (norm_sub_le _ _).trans
      have h₁ := hLip (f t+h) (g t+h)
      have h₂ := hLip (f t) (g t)
      rw [add_sub_add_right_eq_sub] at h₁
      change ‖_‖ ≤ L*‖f t-g t‖ at h₁ h₂
      linarith
    calc
      _ ≤ Real.exp (κ*t)*(2*L*‖f t-g t‖) :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _ ≤ Real.exp (κ*T)*(2*L*‖f t-g t‖) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
      _ = (2*L*Real.exp (κ*T))*‖f t-g t‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (mul_nonneg hC hW)) (norm_nonneg _)

end DefocusingNLS

end OAI
