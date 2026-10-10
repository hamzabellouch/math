import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.CellScaleBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.FreshInnerCountsBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis

 def cellDensityMassConstant : ℝ := (tfPatchCapConstant/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*(64*(Real.pi*4/3))
lemma cellDensityMassConstant_pos : 0 < cellDensityMassConstant := by
  unfold cellDensityMassConstant
  have hK := tfKinetic_pos
  have hC := tfPatchCapConstant_pos
  positivity

lemma cell_density_mass_bound {a m R : ℝ} (ha : 0 < a) (haR : a ≤ R) (h3 : 1/a^3 ≤ m) :
    localPatchDensityCap R*((4*a)^3*(Real.pi*4/3)) ≤ cellDensityMassConstant*m := by
  have hR := lt_of_lt_of_le ha haR
  let C := (tfPatchCapConstant/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)
  have hc : 0 ≤ C := by dsimp [C]; exact Real.rpow_nonneg (div_nonneg tfPatchCapConstant_pos.le (mul_nonneg (by norm_num) tfKinetic_pos.le)) _
  have hscale : localPatchDensityCap R = C/R^6 := by
    unfold localPatchDensityCap
    have he : tfPatchCapConstant/R^4/((5/3:ℝ)*tfKinetic) = (tfPatchCapConstant/((5/3:ℝ)*tfKinetic))/R^4 := by ring
    rw [he,cap_reaction_scale (div_nonneg tfPatchCapConstant_pos.le (mul_nonneg (by norm_num) tfKinetic_pos.le)) hR]
  have hh : localPatchDensityCap R ≤ C/a^6 := by
    rw [hscale]
    gcongr
  calc _ ≤ (C/a^6)*((4*a)^3*(Real.pi*4/3)) := by gcongr
       _ = cellDensityMassConstant*(1/a^3) := by unfold cellDensityMassConstant; dsimp [C]; field_simp; ring
       _ ≤ cellDensityMassConstant*m := mul_le_mul_of_nonneg_left h3 cellDensityMassConstant_pos.le

lemma cell_count_rpow_scale {a m B C P : ℝ} (ha : 0 < a) (hm : 1 ≤ m)
    (h3 : 1/a^3 ≤ m) (hB : 0 ≤ B) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hBC : B ≤ C*P*m^2) :
    B^(2/3:ℝ) ≤ C^(2/3:ℝ)*P^(2/3:ℝ)*a*m^2 := by
  have hm0 := le_trans zero_le_one hm
  have hh := Real.rpow_le_rpow hB hBC (by norm_num : (0:ℝ) ≤ 2/3)
  have he : (C*P*m^2)^(2/3:ℝ) = C^(2/3:ℝ)*P^(2/3:ℝ)*m^(4/3:ℝ) := by
    rw [Real.mul_rpow (mul_nonneg hC hP) (sq_nonneg m),Real.mul_rpow hC hP,
      ←Real.rpow_natCast,←Real.rpow_mul hm0]
    norm_num
  rw [he] at hh
  calc _ ≤ C^(2/3:ℝ)*P^(2/3:ℝ)*m^(4/3:ℝ) := hh
       _ ≤ C^(2/3:ℝ)*P^(2/3:ℝ)*(a*m^2) :=
         mul_le_mul_of_nonneg_left (cell_four_thirds_bound ha hm h3) (by positivity)
       _ = _ := by ring

end CoulombAtom

end

end OAI
