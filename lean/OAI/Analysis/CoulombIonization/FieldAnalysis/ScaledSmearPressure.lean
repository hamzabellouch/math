import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.Vartheta

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators unitInterval

namespace CoulombNeumann
variable {N : ℕ}

lemma vartheta_even (x : CubeSpace) : vartheta (-x) = vartheta x :=
  vartheta_radial (norm_neg x)
lemma varthetaScaled_even (b : ℝ) (x : CubeSpace) : varthetaScaled b (-x) = varthetaScaled b x :=
  varthetaScaled_radial b (norm_neg x)

def physicalSmear (b : ℝ) (x : Fin N → CubeSpace) (y : CubeSpace) : ℝ :=
  ∑ i, varthetaScaled b (y-x i)

lemma physicalSmear_nonneg {b : ℝ} (hb : 0 < b) (x : Fin N → CubeSpace) (y : CubeSpace) :
    0 ≤ physicalSmear b x y := Finset.sum_nonneg (fun _ _ => varthetaScaled_nonneg hb _)
lemma physicalSmear_le {b : ℝ} (hb : 0 < b) (x : Fin N → CubeSpace) (y : CubeSpace) :
    physicalSmear b x y ≤ (N:ℝ)*b⁻¹^3 := by
  exact (Finset.sum_le_sum (fun _ _ => varthetaScaled_le hb _)).trans_eq (by simp)
lemma physicalSmear_measurable (b : ℝ) :
    Measurable (fun p : (Fin N → CubeSpace) × CubeSpace => physicalSmear b p.1 p.2) := by
  unfold physicalSmear
  apply Finset.measurable_sum
  intro i _
  exact (varthetaScaled_measurable b).comp
    (measurable_snd.sub ((measurable_pi_apply i).comp measurable_fst))

lemma physicalSmear_scaled (b : ℝ) (x : Fin N → CubeSpace) (y : CubeSpace) :
    physicalSmear b x y = b⁻¹^3*varthetaSmear (fun i => b⁻¹ • x i) (b⁻¹ • y) := by
  unfold physicalSmear varthetaScaled varthetaSmear
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_sub]
  congr 1
  simpa only [neg_sub] using (vartheta_even (b⁻¹ • x i-b⁻¹ • y))

lemma inverse_cube_rpow {b : ℝ} (hb : 0 < b) : (b⁻¹^3)^(5/3:ℝ) = b⁻¹^5 := by
  rw [←Real.rpow_natCast_mul (by positivity : 0 ≤ b⁻¹)]
  norm_num

lemma physicalSmear_rpow {b : ℝ} (hb : 0 < b) (x : Fin N → CubeSpace) (y : CubeSpace) :
    physicalSmear b x y^(5/3:ℝ) = b⁻¹^5*varthetaSmear (fun i => b⁻¹ • x i) (b⁻¹ • y)^(5/3:ℝ) := by
  rw [physicalSmear_scaled,Real.mul_rpow (by positivity)
    (show 0 ≤ varthetaSmear (fun i => b⁻¹ • x i) (b⁻¹ • y) from
      Finset.sum_nonneg (fun _ _ => vartheta_nonneg _)),inverse_cube_rpow hb]

lemma physicalSmear_pressure_integrable {b : ℝ} (hb : 0 < b) (x : Fin N → CubeSpace) :
    Integrable (fun y => physicalSmear b x y^(5/3:ℝ)) := by
  simp_rw [physicalSmear_rpow hb]
  exact ((varthetaSmear_pressure (fun i => b⁻¹ • x i)).1.comp_smul (inv_ne_zero hb.ne')).const_mul _

lemma integral_physicalSmear_pressure {b : ℝ} (hb : 0 < b) (x : Fin N → CubeSpace) :
    (∫ y, physicalSmear b x y^(5/3:ℝ)) = b⁻¹^2*(∫ y, varthetaSmear (fun i => b⁻¹ • x i) y^(5/3:ℝ)) := by
  simp_rw [physicalSmear_rpow hb]
  rw [integral_const_mul,Measure.integral_comp_smul_of_nonneg volume
    (fun y => varthetaSmear (fun i => b⁻¹ • x i) y^(5/3:ℝ)) b⁻¹ (hR := by positivity)]
  simp only [finrank_euclideanSpace_fin,smul_eq_mul]
  field_simp [hb.ne']

def physicalPressure (b : ℝ) (x : Fin N → CubeSpace) : ℝ :=
  ∫ y, physicalSmear b x y^(5/3:ℝ)

def physicalPressureAverage (b : ℝ) (x : Fin N → CubeSpace) : ℝ :=
  b⁻¹^2*radialPressureAverage (fun i => b⁻¹ • x i)

lemma physicalPressure_measurable (b : ℝ) : Measurable (physicalPressure (N := N) b) :=
  ((physicalSmear_measurable b).pow_const _).stronglyMeasurable.integral_prod_right.measurable
lemma physicalPressure_nonneg {b : ℝ} (hb : 0 < b) (x : Fin N → CubeSpace) :
    0 ≤ physicalPressure b x :=
  integral_nonneg (fun y => Real.rpow_nonneg (physicalSmear_nonneg hb x y) _)
lemma physicalPressureAverage_measurable (b : ℝ) : Measurable (physicalPressureAverage (N := N) b) := by
  apply measurable_const.mul
  apply radialPressureAverage_measurable.comp
  exact Measurable.of_eval (fun i => (measurable_pi_apply i).const_smul b⁻¹)
lemma physicalPressureAverage_nonneg (b : ℝ) (x : Fin N → CubeSpace) : 0 ≤ physicalPressureAverage b x :=
  mul_nonneg (sq_nonneg _) (radialPressureAverage_nonneg _)
lemma physicalPressureAverage_le (b : ℝ) (x : Fin N → CubeSpace) :
    physicalPressureAverage b x ≤ b⁻¹^2*(N:ℝ)^(5/3:ℝ) :=
  mul_le_mul_of_nonneg_left (radialPressureAverage_le _) (sq_nonneg _)

theorem physicalPressure_le_average {b : ℝ} (hb : 0 < b) (x : Fin N → CubeSpace) :
    physicalPressure b x ≤ physicalPressureAverage b x := by
  unfold physicalPressure physicalPressureAverage
  rw [integral_physicalSmear_pressure hb]
  exact mul_le_mul_of_nonneg_left (varthetaSmear_pressure _).2 (sq_nonneg _)

end CoulombNeumann

end

end OAI
