import OAI.Geometry.Kahler.BaseHessianJet

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

lemma testSeries_chart_summable_jets (a : ℝ) {ε D : ℝ} (he : ε ≠ 0) (hD : 1 ≤ D)
    {Q : ℕ} (hQ : 2 ≤ Q) (P : ℕ → Finset Sphere)
    (hP : ∀ j, ProjectivelySeparated (D/Real.sqrt (Q^(j+1):ℕ)) (P (Q^(j+1))))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (U : Base ≃ₗᵢ[ℂ] Base) (n : ℕ) :
    Summable (fun j => iteratedFDeriv ℝ n (logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) ∘ centeredChart r U) 0) := by
  obtain ⟨C,hC,hb⟩ := logarithmicTest_chart_local_jets a he hD hr hr1 n
  apply Summable.of_norm_bounded
    ((summable_lacunary (by linarith : 0 ≤ 1-(1-r)/16) (by linarith : 1-(1-r)/16 < 1) hQ).mul_left C)
  intro j
  exact hb _ (Nat.one_le_pow _ _ (by omega)) _ (hP j) U 0 (Metric.mem_ball_self (by norm_num))

lemma testSeries_chart_uniform_jets (a : ℝ) {ε D : ℝ} (he : ε ≠ 0) (hD : 1 ≤ D)
    {Q : ℕ} (hQ : 2 ≤ Q) (P : ℕ → Finset Sphere)
    (hP : ∀ j, ProjectivelySeparated (D/Real.sqrt (Q^(j+1):ℕ)) (P (Q^(j+1))))
    {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → r < 1 → ∀ U : Base ≃ₗᵢ[ℂ] Base,
      ‖iteratedFDeriv ℝ n ((fun y => ∑' j, logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) y) ∘ centeredChart r U) 0‖ ≤ C := by
  obtain ⟨C,hC,hCb⟩ := logarithmicTest_chart_jets a he hn
  obtain ⟨B,hB,hBb⟩ := chartScale_sum_uniform hQ
  refine ⟨C*B,mul_nonneg hC hB,?_⟩
  intro r hr hr1 U
  let f := fun j => iteratedFDeriv ℝ n (logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) ∘ centeredChart r U) 0
  have hs : Summable (fun j => C*chartScale (Q^(j+1)) (1-r)) :=
    (chartScale_summable hQ (by linarith : 0 < 1-r)).mul_left C
  have hb (j : ℕ) : ‖f j‖ ≤ C*chartScale (Q^(j+1)) (1-r) :=
    hCb hD (Nat.one_le_pow _ _ (by omega)) (hP j) hr hr1 U
  have hnS := Summable.of_nonneg_of_le (fun j => norm_nonneg (f j)) hb hs
  rw [testSeries_chart_iteratedFDeriv a he hD hQ P hP hr hr1 U n]
  exact (norm_tsum_le_tsum_norm hnS).trans ((hnS.tsum_le_tsum hb hs).trans (by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (hBb (1-r) (by linarith)) hC))

lemma testSeries_chart_psh (a : ℝ) {ε D : ℝ} (he : ε ≠ 0) (hD : 1 ≤ D)
    {Q : ℕ} (hQ : 2 ≤ Q) (P : ℕ → Finset Sphere)
    (hP : ∀ j, ProjectivelySeparated (D/Real.sqrt (Q^(j+1):ℕ)) (P (Q^(j+1))))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (U : Base ≃ₗᵢ[ℂ] Base) (v : Base) :
    0 ≤ (∑ i, ∑ j, baseHessian
      ((fun y => ∑' l, logarithmicTest a ε (P (Q^(l+1))) (Q^(l+1)) y) ∘ centeredChart r U) 0 i j * v i * star (v j)).re := by
  have hf := chartWeight_contDiffAt (testSeries_contDiffOn a he hD hQ P hP) hr hr1 U
  rw [baseHessian_value_eq_jet hf, testSeries_chart_iteratedFDeriv a he hD hQ P hP hr hr1 U 2,
    (realHessianValueJet v).map_tsum (testSeries_chart_summable_jets a he hD hQ P hP hr hr1 U 2)]
  apply tsum_nonneg
  intro l
  rw [← baseHessian_value_eq_jet (logarithmicTest_chart_contDiffAt a he _ _ hr hr1 U (by change ‖(0:Base)‖ < 1; simp))]
  apply regularizedLog_holomorphic_psh a he
  exact (peakPolynomial_analytic _ _ _ (mem_univ _)).comp
    (centeredChart_analyticAt U (z := 0) (by simp))

end PinchedHartogs.BaseConstruction

end

end OAI
