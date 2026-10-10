import OAI.NumberTheory.DirichletL.Reflection.CommonMeasure
import OAI.NumberTheory.DirichletL.Inversion.TerminalWidths
import OAI.NumberTheory.DirichletL.Inversion.KernelSourceUniform

namespace OAI

namespace SevenEighths.InverseReflectedNormalization
open InverseTerminalWidths
noncomputable section

def outsideScalar (Z v ell el S₀ B₀ Td : ℝ) : ℝ :=
  Z ^ (-v/2-ell-el/3-(S₀+B₀)/2) *
    InverseKernelSourceUniform.smallScalar (Z ^ (v+3*ell+el-Td))

theorem smallScalar_rpow {Z : ℝ} (hZ : 1 ≤ Z) (d : ℝ) :
    InverseKernelSourceUniform.smallScalar (Z ^ (-d)) = Z ^ (-max 0 d/4) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  unfold InverseKernelSourceUniform.smallScalar
  rw [← Real.rpow_mul hZ0.le]
  by_cases hd : 0 ≤ d
  · rw [max_eq_right hd, min_eq_right]
    · congr 1; ring
    · calc
        Z ^ (-d * (1/4:ℝ)) ≤ Z ^ (0:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
        _ = 1 := Real.rpow_zero _
  · have hd' : d ≤ 0 := le_of_not_ge hd
    rw [max_eq_left hd', neg_zero, zero_div, Real.rpow_zero, min_eq_left]
    calc
      1 = Z ^ (0:ℝ) := (Real.rpow_zero _).symm
      _ ≤ Z ^ (-d*(1/4:ℝ)) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

theorem outsideScalar_square {Z : ℝ} (hZ : 1 ≤ Z) (v ell el S₀ B₀ Td : ℝ) :
    outsideScalar Z v ell el S₀ B₀ Td ^ 2 =
      Z ^ (-v-2*ell-2*el/3-S₀-B₀-max 0 (Td-v-3*ell-el)/2) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  unfold outsideScalar
  rw [show v+3*ell+el-Td = -(Td-v-3*ell-el) by ring, smallScalar_rpow hZ,
    ← Real.rpow_add hZ0, ← Real.rpow_mul_natCast hZ0.le]
  congr 1
  ring

theorem row_shape {Z : ℝ} (hZ : 1 ≤ Z) (H v ell : ℝ) :
    Z^H + Z^v*Z^ell ≤ 2*Z^(max H (v+ell)) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  rw [← Real.rpow_add hZ0]
  have h1 := Real.rpow_le_rpow_of_exponent_le hZ (le_max_left H (v+ell))
  have h2 := Real.rpow_le_rpow_of_exponent_le hZ (le_max_right H (v+ell))
  linarith

theorem cubic_shape {Z : ℝ} (hZ : 1 ≤ Z) (v za : ℝ) :
    Z^v + Z^za + (Z^v*Z^za)^(2/3:ℝ) ≤ 3*Z^(v+za-hybridSaving v za) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hv : hybridSaving v za ≤ v := min_le_left _ _
  have hz : hybridSaving v za ≤ za := (min_le_right _ _).trans (min_le_left _ _)
  have ht : hybridSaving v za ≤ (v+za)/3 := (min_le_right _ _).trans (min_le_right _ _)
  rw [← Real.rpow_add hZ0, ← Real.rpow_mul hZ0.le]
  have h1 := Real.rpow_le_rpow_of_exponent_le hZ (show v ≤ v+za-hybridSaving v za by linarith)
  have h2 := Real.rpow_le_rpow_of_exponent_le hZ (show za ≤ v+za-hybridSaving v za by linarith)
  have h3 := Real.rpow_le_rpow_of_exponent_le hZ (show (v+za)*(2/3:ℝ) ≤ v+za-hybridSaving v za by linarith)
  linarith

theorem reflected_exponent_identity (H v ell el S₀ B₀ Td za ε : ℝ) :
    (-v-2*ell-2*el/3-S₀-B₀-max 0 (Td-v-3*ell-el)/2) +
      (H+v+ell+za)*ε + max H (v+ell) + ell + (v+za-hybridSaving v za) =
    reflectedExponent 0 H S₀ B₀ za v ell el Td + ε*(H+v+ell+za) := by
  unfold reflectedExponent
  ring

theorem normalized_hybrid_shape {Z : ℝ} (hZ : 1 ≤ Z)
    (H v ell el S₀ B₀ Td za ε : ℝ) :
    (outsideScalar Z v ell el S₀ B₀ Td)^2 *
      ((Z^H*Z^v*Z^ell*Z^za)^ε * (Z^H+Z^v*Z^ell)*Z^ell*
        (Z^v+Z^za+(Z^v*Z^za)^(2/3:ℝ))) ≤
      6*Z^(reflectedExponent 0 H S₀ B₀ za v ell el Td + ε*(H+v+ell+za)) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hp : (Z^H*Z^v*Z^ell*Z^za)^ε = Z^((H+v+ell+za)*ε) := by
    rw [← Real.rpow_add hZ0,← Real.rpow_add hZ0,← Real.rpow_add hZ0,
      ← Real.rpow_mul hZ0.le]
  have hb := mul_le_mul (row_shape hZ H v ell) (cubic_shape hZ v za)
    (by positivity : 0 ≤ Z^v+Z^za+(Z^v*Z^za)^(2/3:ℝ)) (by positivity)
  have hh := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ (outsideScalar Z v ell el S₀ B₀ Td)^2 *
      (Z^H*Z^v*Z^ell*Z^za)^ε * Z^ell by positivity)
  calc
    _ ≤ (outsideScalar Z v ell el S₀ B₀ Td)^2 *
        (Z^H*Z^v*Z^ell*Z^za)^ε * Z^ell *
        ((2*Z^(max H (v+ell)))*(3*Z^(v+za-hybridSaving v za))) := by
      nlinarith only [hh]
    _ = 6*Z^(reflectedExponent 0 H S₀ B₀ za v ell el Td + ε*(H+v+ell+za)) := by
      rw [outsideScalar_square hZ,hp]
      calc
        _ = 6*(Z^(-v-2*ell-2*el/3-S₀-B₀-max 0 (Td-v-3*ell-el)/2) *
          Z^((H+v+ell+za)*ε) * Z^(max H (v+ell)) * Z^ell *
          Z^(v+za-hybridSaving v za)) := by ring
        _ = _ := by
          rw [← Real.rpow_add hZ0,← Real.rpow_add hZ0,← Real.rpow_add hZ0,
            ← Real.rpow_add hZ0,reflected_exponent_identity]

end
end SevenEighths.InverseReflectedNormalization

end OAI
