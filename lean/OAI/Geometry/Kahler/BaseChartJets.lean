import OAI.Geometry.Kahler.BaseChartLow

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

def chartScale (k : ℕ) (δ : ℝ) : ℝ :=
  if (k:ℝ)*δ ≤ 1 then Real.sqrt ((k:ℝ)*δ) else Real.exp (-(k:ℝ)*δ/16)

lemma logarithmicTest_chart_jets (a : ℝ) {ε : ℝ} (he : ε ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {D : ℝ}, 1 ≤ D → ∀ {k : ℕ}, 1 ≤ k →
      ∀ {P : Finset Sphere}, ProjectivelySeparated (D/Real.sqrt k) P →
      ∀ {r : ℝ}, 0 ≤ r → r < 1 → ∀ U : Base ≃ₗᵢ[ℂ] Base,
      ‖iteratedFDeriv ℝ n (logarithmicTest a ε P k ∘ centeredChart r U) 0‖ ≤ C*chartScale k (1-r) := by
  obtain ⟨B,hB,hBlow⟩ := peak_chart_low
  let B' := B+2*gaussianConstant
  have hB' : 0 ≤ B' := by dsimp [B']; linarith [gaussianConstant_pos]
  obtain ⟨C,hC,hCb⟩ := regularizedLog_positive_jet_bound a he (by norm_num : (0:ℝ) < 1/32)
    gaussianConstant_pos.le hB' hn
  refine ⟨C,hC,?_⟩
  intro D hD k hk P hP r hr hr1 U
  let f := peakPolynomial P k ∘ centeredChart r U
  have hf : AnalyticOnNhd ℂ f (Metric.ball (0:Base) (1/32)) := by
    intro z hz
    have hzb : z ∈ ball := by
      have hz' : ‖z‖ < 1/32 := by simpa using hz
      change ‖z‖ < 1
      linarith
    exact (peakPolynomial_analytic P k _ (mem_univ _)).comp
      (centeredChart_analyticAt U (centeredChart_den_ne_zero hr hr1 hzb))
  have hfc : ‖f 0‖ ≤ gaussianConstant := by
    apply (peak_global_bound hD hk hP _).trans
    apply mul_le_of_le_one_right gaussianConstant_pos.le
    exact pow_le_one₀ (norm_nonneg _) (centeredChart_zero_mem hr hr1 U).le
  have hkδ : 0 < (k:ℝ)*(1-r) := mul_pos (by exact_mod_cast (show 0 < k by omega)) (by linarith)
  by_cases hlow : (k:ℝ)*(1-r) ≤ 1
  · rw [chartScale,ite_eq_left hlow]
    apply hCb f 0 (Real.sqrt ((k:ℝ)*(1-r))) hf hfc (Real.sqrt_pos.mpr hkδ) (Real.sqrt_le_one.mpr hlow)
    intro z hz
    apply (hBlow hD hk hP hr hr1 hlow U z (by simpa using hz)).trans
    exact mul_le_mul_of_nonneg_right (by dsimp [B']; linarith [gaussianConstant_pos]) (Real.sqrt_nonneg _)
  · rw [chartScale,ite_eq_right hlow]
    apply hCb f 0 (Real.exp (-(k:ℝ)*(1-r)/16)) hf hfc (Real.exp_pos _)
      (Real.exp_le_one_iff.mpr (by nlinarith))
    intro z hz
    have hb := peak_chart_high hD hk hP hr hr1 U (by simpa using hz : ‖z‖ < (1/32:ℝ))
    have hb0 := peak_chart_high hD hk hP hr hr1 U (z := 0) (by simp)
    apply (norm_sub_le _ _).trans
    dsimp [f,Function.comp_def]
    dsimp [B']
    nlinarith [Real.exp_pos (-(k:ℝ)*(1-r)/16)]

end PinchedHartogs.BaseConstruction

end

end OAI
