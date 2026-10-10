import OAI.Geometry.TranslativeCovering.WitnessConstruction

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace ResidualCaps
open Set Metric SphericalLaw

noncomputable def unit {n : ℕ} (x : Space n) (hx : x ≠ 0) : Sphere n :=
  ⟨‖x‖⁻¹ • x,by simp [norm_smul,(norm_pos_iff.mpr hx).ne']⟩

lemma cap_unit {n : ℕ} (x : Space n) (hx : x ≠ 0) (t : ℝ) :
    cap (unit x hx).val (t/‖x‖) = cap x t := by
  ext u
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  simp only [cap,unit,mem_ofPred_eq,inner_smul_right,abs_mul,abs_inv,abs_of_nonneg (norm_nonneg x)]
  rw [mul_comm,← div_eq_mul_inv,div_lt_div_iff_of_pos_right hn]

lemma angle_unit {n : ℕ} (x y : Space n) (hx : x ≠ 0) (hy : y ≠ 0) :
    ProjectiveCaps.angle (unit x hx).val (unit y hy).val = ProjectiveCaps.angle x y := by
  have hnx : 0 < ‖x‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hx)
  have hny : 0 < ‖y‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hy)
  simp only [unit,ProjectiveCaps.angle,InnerProductGeometry.angle_smul_left_of_pos _ _ hnx,
    ← smul_neg,InnerProductGeometry.angle_smul_right_of_pos _ _ hny]

lemma cap_monotone_threshold {n : ℕ} (x : Space n) {t s : ℝ} (ht : t ≤ s) : cap x s ⊆ cap x t :=
  fun _ h => ht.trans_lt h
end ResidualCaps

end OAI
