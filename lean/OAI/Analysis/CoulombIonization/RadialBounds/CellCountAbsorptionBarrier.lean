import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.CellCountFeedbackBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped ContDiff

namespace CoulombAtom
open CoulombAnalysis

 def cellBootstrapCollar : ℝ := min (1/8) ((1/(4*cellCountLeadingConstant))^2)
lemma cellBootstrapCollar_pos : 0 < cellBootstrapCollar := by
  have hA := cellCountLeadingConstant_pos
  unfold cellBootstrapCollar
  positivity
lemma cellBootstrapCollar_le : cellBootstrapCollar ≤ 1/8 := by unfold cellBootstrapCollar; exact min_le_left (1/8:ℝ) ((1/(4*cellCountLeadingConstant))^2)
lemma cellBootstrapCollar_absorb : cellCountLeadingConstant*Real.sqrt cellBootstrapCollar ≤ 1/4 := by
  have hA := cellCountLeadingConstant_pos
  have hh : Real.sqrt cellBootstrapCollar ≤ 1/(4*cellCountLeadingConstant) :=
    Real.sqrt_le_iff.mpr ⟨by positivity,by unfold cellBootstrapCollar; exact min_le_right (1/8:ℝ) ((1/(4*cellCountLeadingConstant))^2)⟩
  calc _ ≤ cellCountLeadingConstant*(1/(4*cellCountLeadingConstant)) := mul_le_mul_of_nonneg_left hh hA.le
       _ = 1/4 := by field_simp

lemma count_sublinear_absorption {P C : ℝ} (hP : 1 ≤ P) (hC : 0 ≤ C)
    (hh : P ≤ 1+P/4+C*(P^(2/3:ℝ)+Real.sqrt P+1)) :
    P ≤ (4*(1+3*C)/3)^3 := by
  have hP0 : 0 ≤ P := le_trans zero_le_one hP
  have hv : 1 ≤ P^(2/3:ℝ) := Real.one_le_rpow hP (by norm_num)
  have hs : Real.sqrt P ≤ P^(2/3:ℝ) := by
    rw [Real.sqrt_eq_rpow]
    apply Real.rpow_le_rpow_of_exponent_le hP
    norm_num
  have hW : P^(2/3:ℝ)+Real.sqrt P+1 ≤ 3*P^(2/3:ℝ) := by linarith
  have hCW := mul_le_mul_of_nonneg_left hW hC
  have hlin : P ≤ (4*(1+3*C)/3)*P^(2/3:ℝ) := by nlinarith
  have hp := pow_le_pow_left₀ hP0 hlin 3
  have he : (P^(2/3:ℝ))^3 = P^2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hP0]
    norm_num
  rw [mul_pow,he] at hp
  have hpow : P*P^2 ≤ (4*(1+3*C)/3)^3*P^2 := by nlinarith only [hp]
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos (by linarith : 0 < P))).mp hpow

 def cellUniversalCountConstant (d : ℝ) : ℝ :=
    (4*(1+3*cellCountErrorConstant cellBootstrapCollar d)/3)^3
lemma cellUniversalCountConstant_one_le {d : ℝ} (hd : 0 ≤ d) : 1 ≤ cellUniversalCountConstant d := by
  have hC := cellCountErrorConstant_nonneg cellBootstrapCollar_pos hd
  have ht : 1 ≤ 4*(1+3*cellCountErrorConstant cellBootstrapCollar d)/3 := by linarith
  have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) ht 3
  simpa [cellUniversalCountConstant] using hh

 theorem priced_cell_supremum_bound {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g) (hgs : tsupport g ⊆ Metric.ball 0 1) :
    localCountSupremum ψ (max (corePriceExcess Z lam ψ) 0) ≤ cellUniversalCountConstant (packetDirichlet g) := by
  let P := localCountSupremum ψ (max (corePriceExcess Z lam ψ) 0)
  have hP : 1 ≤ P := localCountSupremum_one_le ψ _
  have hP0 : 0 ≤ P := le_trans zero_le_one hP
  have hh := cell_supremum_feedback hψ hm cellBootstrapCollar_pos cellBootstrapCollar_le hZ hlam hg hcg hgn hr hgs
  have ha := mul_le_mul_of_nonneg_right cellBootstrapCollar_absorb hP0
  apply count_sublinear_absorption hP (cellCountErrorConstant_nonneg cellBootstrapCollar_pos (packetDirichlet_nonneg g))
  dsimp only at hh
  change P ≤ 1+cellCountLeadingConstant*Real.sqrt cellBootstrapCollar*P+_ at hh
  linarith only [hh,ha]

end CoulombAtom

end

end OAI
