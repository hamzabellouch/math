import OAI.NumberTheory.CubicMoment.Estimates.TypeIOuter

namespace OAI

/-! The length and level powers in the Type-I height estimate. -/
noncomputable section
namespace CubicFirstMoment

lemma typeI_principal_scaling {R U : ℝ} (hR : 0 < R) (hU : 0 < U) (ε : ℝ) :
    U^(1/2+ε)*(2*R)^(1/4+2*ε)*R =
      2^(1/4+2*ε)*(R*U)^(1/2+ε)*R^(3/4+ε) := by
  have hp : R^(1/4+2*ε)*R = R^(1/2+ε)*R^(3/4+ε) := by
    calc
      _ = R^(1/4+2*ε)*R^(1:ℝ) := by rw [Real.rpow_one]
      _ = R^((1/4+2*ε)+1) := (Real.rpow_add hR _ _).symm
      _ = R^((1/2+ε)+(3/4+ε)) := by congr 1; ring
      _ = _ := Real.rpow_add hR _ _
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hR.le,
    Real.mul_rpow hR.le hU.le]
  calc
    _ = 2^(1/4+2*ε)*U^(1/2+ε)*(R^(1/4+2*ε)*R) := by ring
    _ = _ := by rw [hp]; ring

lemma typeI_residue_scaling {R U : ℝ} (hR : 0 < R) (hU : 0 < U) :
    U^(5/6:ℝ)*R^(-1/6:ℝ)*R = (R*U)^(5/6:ℝ) := by
  have hp : R^(-1/6:ℝ)*R = R^(5/6:ℝ) := by
    calc
      _ = R^(-1/6:ℝ)*R^(1:ℝ) := by rw [Real.rpow_one]
      _ = R^((-1/6:ℝ)+1) := (Real.rpow_add hR _ _).symm
      _ = _ := by norm_num
  rw [Real.mul_rpow hR.le hU.le]
  calc
    _ = U^(5/6:ℝ)*(R^(-1/6:ℝ)*R) := by ring
    _ = _ := by rw [hp]; ring

lemma typeI_level_mass_scaling {R U : ℝ} (hR : 0 < R) (hU : 0 < U)
    (C E ε T L : ℝ) (D : ℕ) :
    (C*U^(1/2+ε)*(2*R)^(1/4+2*ε)*Real.sqrt T+
      E*U^(5/6:ℝ)*R^(-1/6:ℝ)/T^D)*(R*L) =
      (C*2^(1/4+2*ε))*(R*U)^(1/2+ε)*R^(3/4+ε)*Real.sqrt T*L+
        E*(R*U)^(5/6:ℝ)*L/T^D := by
  calc
    _ = C*(U^(1/2+ε)*(2*R)^(1/4+2*ε)*R)*Real.sqrt T*L+
        E*(U^(5/6:ℝ)*R^(-1/6:ℝ)*R)*L/T^D := by ring
    _ = _ := by rw [typeI_principal_scaling hR hU,typeI_residue_scaling hR hU]; ring

lemma typeI_principal_power_bound {X R ε : ℝ} (hX : 0 < X) (hR : 0 < R)
    (hRX : R ≤ X) (hε : 0 ≤ ε) :
    X^(1/2+ε)*R^(3/4+ε) ≤ X^(1/2+2*ε)*R^(3/4:ℝ) := by
  rw [Real.rpow_add hR]
  have hb := Real.rpow_le_rpow hR.le hRX hε
  calc
    _ = (X^(1/2+ε)*R^ε)*R^(3/4:ℝ) := by ring
    _ ≤ (X^(1/2+ε)*X^ε)*R^(3/4:ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hX.le _))
        (Real.rpow_nonneg hR.le _)
    _ = _ := by rw [← Real.rpow_add hX]; congr 2; ring

end CubicFirstMoment

end

end OAI
