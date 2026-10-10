import OAI.NumberTheory.JointDickman.Amplification.GeometricSampledIntegral

namespace OAI

/-! # A uniform small loss for the bounded major-arc frequency slope -/

namespace JointDickman

theorem histogram_frequency_loss_bound {B m : ℕ} (hB : 1 ≤ B)
    {M₁ M₂ D₁ D₂ b R β : ℝ}
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hb : 0 ≤ b) (hR : 0 ≤ R) (hβ : |β| ≤ R) :
    let L₁ := (D₁+2*Real.pi*|β| * M₁)*((B : ℝ)*(b*Real.exp 1))
    let L₂ := (D₂+2*Real.pi*|β| * M₂)*((B : ℝ)*(b*Real.exp 1))
    let K := 2*(b*Real.exp 1)*((D₁+2*Real.pi*R*M₁)*M₂+M₁*(D₂+2*Real.pi*R*M₂))+2*M₁*M₂
    2*channelMesh (channelFineCount m B)*(L₁*M₂+M₁*L₂)+2*M₁*M₂*(B : ℝ)^(-(1/80 : ℝ)) ≤
      K*((B : ℝ)*channelMesh (channelFineCount m B)+(B : ℝ)^(-(1/200 : ℝ))) := by
  dsimp only
  let C := 2*(b*Real.exp 1)*((D₁+2*Real.pi*R*M₁)*M₂+M₁*(D₂+2*Real.pi*R*M₂))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hδ : 0 ≤ channelMesh (channelFineCount m B) := by unfold channelMesh; positivity
  have hL₁ : D₁+2*Real.pi*|β| * M₁ ≤ D₁+2*Real.pi*R*M₁ := by
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hβ (by positivity : 0 ≤ 2*Real.pi)) hM₁)
  have hL₂ : D₂+2*Real.pi*|β| * M₂ ≤ D₂+2*Real.pi*R*M₂ := by
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hβ (by positivity : 0 ≤ 2*Real.pi)) hM₂)
  have hlin : 2*channelMesh (channelFineCount m B)*
      ((D₁+2*Real.pi*|β| * M₁)*((B : ℝ)*(b*Real.exp 1))*M₂+
        M₁*((D₂+2*Real.pi*|β| * M₂)*((B : ℝ)*(b*Real.exp 1)))) ≤
      C*((B : ℝ)*channelMesh (channelFineCount m B)) := by
    calc
      _ ≤ 2*channelMesh (channelFineCount m B)*
          ((D₁+2*Real.pi*R*M₁)*((B : ℝ)*(b*Real.exp 1))*M₂+
            M₁*((D₂+2*Real.pi*R*M₂)*((B : ℝ)*(b*Real.exp 1)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL₁ (by positivity)) hM₂)
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL₂ (by positivity)) hM₁)
      _ = _ := by dsimp [C]; ring
  have hpow : (B : ℝ)^(-(1/80 : ℝ)) ≤ (B : ℝ)^(-(1/200 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hB) (by norm_num)
  calc
    _ ≤ C*((B : ℝ)*channelMesh (channelFineCount m B))+2*M₁*M₂*(B : ℝ)^(-(1/200 : ℝ)) :=
      add_le_add hlin (mul_le_mul_of_nonneg_left hpow (by positivity))
    _ ≤ _ := by
      change _ ≤ (C+2*M₁*M₂)*_
      nlinarith [mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg B) (-(1/200 : ℝ))),
        mul_nonneg (show 0 ≤ 2*M₁*M₂ by positivity)
          (mul_nonneg (Nat.cast_nonneg B) hδ)]

end JointDickman

end OAI
