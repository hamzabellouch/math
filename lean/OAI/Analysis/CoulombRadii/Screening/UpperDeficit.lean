import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.NewtonInterior

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

def atomicInnerFieldConstant : ℝ :=
  2*atomicBudgetRecursionC^2*Real.sqrt atomicCountConstant*(100000:ℝ)^4+2501*atomicTailConstant
lemma atomicInnerFieldConstant_nonneg : 0 ≤ atomicInnerFieldConstant := by
  unfold atomicInnerFieldConstant
  exact add_nonneg (by positivity) (mul_nonneg (by norm_num) atomicTailConstant_nonneg)

lemma atomic_inner_field_shell_bound {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hm : mass ψ=1)
    {E δ : ℝ} (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ)
    (hδ : 0 ≤ δ) {h : ℝ} (hh : 0 < h) {y : Space} (hy : y∈radialShell h) :
    atomicInnerField S ψ h y ≤ atomicInnerFieldConstant*screenMass δ h/h := by
  have hlo : h ≤ ‖y‖ := by simpa only [radialShell,Metric.mem_ball,dist_zero_right,not_lt] using hy.2
  have hhi : ‖y‖ ≤ 2*h := (by simpa only [radialShell,Metric.mem_ball,dist_zero_right] using hy.1 : ‖y‖ < 2*h).le
  have hy0 : y≠0 := norm_pos_iff.mp (hh.trans_le hlo)
  have ha := atomicCellScale_pos hy0
  have hlowa : h/100000 ≤ atomicCellScale y := by dsimp only [atomicCellScale]; linarith
  have hhigha : atomicCellScale y ≤ h*100000 := by dsimp only [atomicCellScale]; linarith
  have hc := screenMass_comparable hδ hh (show (1:ℝ) ≤ 100000 by norm_num) hlowa hhigha
  have hm0 := (screenMass_pos δ h).le
  have hunit : screenFieldUnit δ atomicCountConstant (atomicCellScale y) ≤
      Real.sqrt atomicCountConstant*(100000:ℝ)^4*screenMass δ h/h := by
    calc
      _ ≤ (Real.sqrt atomicCountConstant*((100000:ℝ)^3*screenMass δ h))/(atomicCellScale y) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg _)) ha.le
      _ ≤ (Real.sqrt atomicCountConstant*((100000:ℝ)^3*screenMass δ h))/(h/100000) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hlowa
      _ = _ := by field_simp
  have H := atomic_inner_field_bound S hatom ψ hψ hm hE hstate hδ hh hy0
  apply H.trans
  have HH := mul_le_mul_of_nonneg_left hunit (show 0 ≤ 2*atomicBudgetRecursionC^2 by positivity)
  have he : atomicInnerFieldConstant*screenMass δ h/h=
      2*atomicBudgetRecursionC^2*(Real.sqrt atomicCountConstant*(100000:ℝ)^4*screenMass δ h/h)+
      2501*atomicTailConstant*screenMass δ h/h := by unfold atomicInnerFieldConstant; ring
  rw [he]
  exact add_le_add HH le_rfl

theorem atomic_inner_deficit_upper {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hm : mass ψ=1)
    {E δ : ℝ} (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ)
    (hδ : 0 ≤ δ) {h : ℝ} (hh : 0 < h) :
    totalCharge S-expectedPopulation ψ (Metric.ball 0 h) ≤
      2*atomicInnerFieldConstant*screenMass δ h := by
  have hm0 := (screenMass_pos δ h).le
  have hR : 0 ≤ 2*atomicInnerFieldConstant*screenMass δ h :=
    mul_nonneg (mul_nonneg (by norm_num) atomicInnerFieldConstant_nonneg) hm0
  by_cases hd : totalCharge S-expectedPopulation ψ (Metric.ball 0 h) ≤ 0
  · exact hd.trans hR
  have hd0 := (not_le.mp hd).le
  have hAttr : Integrable (fun y => attraction S y*radialShellDensity h y) := by
    simp_rw [attraction_atomic S hatom,div_eq_mul_inv,mul_assoc]
    exact (radialShellMoment_integrable h).const_mul (totalCharge S)
  have hCore := restrictedCorePotential_mul_integrable ψ (A:=Metric.ball 0 h) measurableSet_ball _ (radialShellDensity_integrable h)
  have hInt : Integrable (fun y => atomicInnerField S ψ h y*radialShellDensity h y) := by
    convert hAttr.sub hCore using 1
    first | rfl | (ext y; simp only [atomicInnerField,Pi.sub_apply]; ring)
  have hAv : (totalCharge S-expectedPopulation ψ (Metric.ball 0 h))*radialShellMoment h ≤
      (atomicInnerFieldConstant*screenMass δ h/h)*(∫ y,radialShellDensity h y) := by
    rw [←atomicInnerField_shell_average S hatom ψ hh,←integral_const_mul]
    apply integral_mono hInt ((radialShellDensity_integrable h).const_mul _)
    intro y
    by_cases hy : y∈radialShell h
    · exact mul_le_mul_of_nonneg_right (atomic_inner_field_shell_bound S hatom ψ hψ hm hE hstate hδ hh hy)
        (radialShellDensity_nonneg h y)
    · simp only [radialShellDensity,indicator_of_notMem hy,mul_zero,le_refl]
  have hb := radialShellMoment_lower hh
  have hmass : 0 < ∫ y,radialShellDensity h y := by rw [radialShellDensity_mass hh]; positivity
  have hfrac : 0 < (∫ y,radialShellDensity h y)/(2*h) := div_pos hmass (by positivity)
  calc
    _ ≤ ((totalCharge S-expectedPopulation ψ (Metric.ball 0 h))*radialShellMoment h)/
        ((∫ y,radialShellDensity h y)/(2*h)) :=
      (le_div_iff₀ hfrac).mpr (mul_le_mul_of_nonneg_left hb hd0)
    _ ≤ ((atomicInnerFieldConstant*screenMass δ h/h)*(∫ y,radialShellDensity h y))/
        ((∫ y,radialShellDensity h y)/(2*h)) := div_le_div_of_nonneg_right hAv hfrac.le
    _ = _ := by field_simp [hh.ne',hmass.ne']

end Coulomb
end

end
end

end OAI
