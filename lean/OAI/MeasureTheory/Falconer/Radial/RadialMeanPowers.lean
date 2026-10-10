import OAI.MeasureTheory.Falconer.Radial.RadialCollisionMean
import OAI.MeasureTheory.Falconer.Angular.AngularUniformAbsorption

namespace OAI

/-! # The logarithmic radial mean loss is absorbed by a small scale power -/

namespace Falconer

theorem dyadic_radial_power_cancel (g k : ℕ) (q : ℝ) :
    ((2:ℝ)^g)^q*(1/(2:ℝ)^(g+k))^q = ((2:ℝ)^k)^(-q) := by
  calc
    _ = (((2:ℝ)^g)*(1/(2:ℝ)^(g+k)))^q :=
      (Real.mul_rpow (by positivity) (by positivity)).symm
    _ = (1/(2:ℝ)^k)^q := by congr 1; rw [pow_add]; field_simp
    _ = _ := by rw [one_div,Real.inv_rpow (by positivity),Real.rpow_neg (by positivity)]

theorem eventually_radial_mean_coefficient {D η q : ℝ} (hD : 1 ≤ D) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ g k : ℕ, k ≤ N →
      (2*((2:ℝ)^N)^η*(3*D)^q*(1/(2:ℝ)^(g+k))^q)*
        (2:ℝ)^q*(((2:ℝ)^N)^η*((2:ℝ)^g)^q+
          (k:ℝ)*(((2:ℝ)^N)^η*((2:ℝ)^g)^q*(2:ℝ)^q)) ≤
      ((2:ℝ)^N)^(3*η)*((2:ℝ)^k)^(-q) := by
  let B := 2*(3*D)^q*(2:ℝ)^q
  let C := B*(1+(2:ℝ)^q)
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨N₀,hN₀⟩ := PlanarFalconer.fixed_linear_subpower C hC hη
  refine ⟨N₀,fun N hN g k hk => ?_⟩
  let R : ℝ := (2:ℝ)^N
  have hR : 0 < R := by dsimp [R]; positivity
  have hcoef : B*(1+(k:ℝ)*(2:ℝ)^q) ≤ R^η := by
    apply le_trans ?_ (hN₀ N hN)
    have hkn : (k:ℝ) ≤ N := by exact_mod_cast hk
    have hp : 0 ≤ (2:ℝ)^q := by positivity
    have hnum : 1+(k:ℝ)*(2:ℝ)^q ≤ (1+(2:ℝ)^q)*(1+2*(N:ℝ)) := by
      nlinarith [show (0:ℝ) ≤ N from Nat.cast_nonneg N]
    exact (mul_le_mul_of_nonneg_left hnum hB).trans_eq (by dsimp [C]; ring)
  calc
    _ = (B*(1+(k:ℝ)*(2:ℝ)^q))*(R^η*R^η)*
        (((2:ℝ)^g)^q*(1/(2:ℝ)^(g+k))^q) := by dsimp [B,R]; ring
    _ = (B*(1+(k:ℝ)*(2:ℝ)^q))*R^(2*η)*((2:ℝ)^k)^(-q) := by
      rw [dyadic_radial_power_cancel,← Real.rpow_add hR,show η+η = 2*η by ring]
    _ ≤ R^η*R^(2*η)*((2:ℝ)^k)^(-q) := by gcongr
    _ = _ := by
      rw [← Real.rpow_add hR,show η+2*η = 3*η by ring]

end Falconer

end OAI
