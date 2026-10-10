import OAI.NumberTheory.Ostmann.Supply.BoundaryCoverageCounts
import OAI.NumberTheory.Ostmann.Supply.BoundaryCoverageWeightScale

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Supply
open Filter

theorem eventually_boundary_weighted_scale (d : Decomposition) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ X : ℕ in atTop, ∀ M U : ℝ, 0 ≤ M →
      M ≤ (X:ℝ)^(1/100:ℝ) → (X:ℝ)^(-(1/100:ℝ)) ≤ U →
      (boundaryPairCount d X:ℝ)*M ≤ η*U*(X:ℝ)/Real.log (X:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := eventually_boundaryPairCount_le d
  have hsmall := (isLittleO_log_rpow_rpow_atTop (5:ℝ)
    (by norm_num : (0:ℝ)<3/100)).bound (show 0<η/(2*C^2) by positivity)
  have hnat : Tendsto (fun X:ℕ => (X:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcount,hnat.eventually hsmall,eventually_ge_atTop 2] with X hcount hsmall hX
  have hp : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
  have hl : 0<Real.log (X:ℝ) := Real.log_pos (by exact_mod_cast (show 1<X by omega))
  norm_num only [Real.rpow_ofNat] at hsmall
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hl.le 5),
    abs_of_nonneg (Real.rpow_nonneg hp.le _)] at hsmall
  intro M U hM hMpow hU
  have hpowers : (X:ℝ)^(19/20:ℝ)*(X:ℝ)^(1/100:ℝ) =
      (X:ℝ)^(24/25:ℝ) := by rw [←Real.rpow_add hp]; norm_num
  have hb : (boundaryPairCount d X:ℝ)*M ≤
      2*C^2*(X:ℝ)^(24/25:ℝ)*Real.log (X:ℝ)^4 := by
    have hb := mul_le_mul hcount hMpow hM (by positivity)
    calc
      _ ≤ (2*C^2*(X:ℝ)^(19/20:ℝ)*Real.log (X:ℝ)^4)*(X:ℝ)^(1/100:ℝ) := hb
      _ = 2*C^2*((X:ℝ)^(19/20:ℝ)*(X:ℝ)^(1/100:ℝ))*Real.log (X:ℝ)^4 := by ring
      _ = _ := by rw [hpowers]
  have hsum : (X:ℝ)^(24/25:ℝ)*(X:ℝ)^(3/100:ℝ) =
      (X:ℝ)^(-(1/100:ℝ))*(X:ℝ) := by
    calc
      _ = (X:ℝ)^(99/100:ℝ) := by rw [←Real.rpow_add hp]; norm_num
      _ = (X:ℝ)^(-(1/100:ℝ))*(X:ℝ)^(1:ℝ) := by
        rw [←Real.rpow_add hp]; norm_num
      _ = _ := by rw [Real.rpow_one]
  have hfinal : (2*C^2*(X:ℝ)^(24/25:ℝ)) *
      ((η/(2*C^2))*(X:ℝ)^(3/100:ℝ)) =
      η*(X:ℝ)^(-(1/100:ℝ))*(X:ℝ) := by
    calc
      _ = η*((X:ℝ)^(24/25:ℝ)*(X:ℝ)^(3/100:ℝ)) := by field_simp
      _ = _ := by rw [hsum]; ring
  have hs := mul_le_mul_of_nonneg_left hsmall
    (show 0≤2*C^2*(X:ℝ)^(24/25:ℝ) by positivity)
  rw [hfinal] at hs
  apply (le_div_iff₀ hl).mpr
  calc
    _ ≤ (2*C^2*(X:ℝ)^(24/25:ℝ)*Real.log (X:ℝ)^4)*Real.log (X:ℝ) :=
      mul_le_mul_of_nonneg_right hb hl.le
    _ = (2*C^2*(X:ℝ)^(24/25:ℝ))*Real.log (X:ℝ)^5 := by ring
    _ ≤ η*(X:ℝ)^(-(1/100:ℝ))*(X:ℝ) := hs
    _ ≤ η*U*(X:ℝ) := by gcongr

end Ostmann.Supply

end

end OAI
