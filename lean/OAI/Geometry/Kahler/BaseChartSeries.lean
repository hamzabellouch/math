import OAI.Geometry.Kahler.BaseLocalSmoothSeriesOn

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

lemma logarithmicTest_chart_contDiffAt (a : ℝ) {ε : ℝ} (he : ε ≠ 0)
    (P : Finset Sphere) (k : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (U : Base ≃ₗᵢ[ℂ] Base) {z : Base} (hz : z ∈ ball) :
    ContDiffAt ℝ ∞ (logarithmicTest a ε P k ∘ centeredChart r U) z :=
  (logarithmicTest_contDiff a he P k).contDiffAt.comp z
    ((centeredChart_analyticAt U (centeredChart_den_ne_zero hr hr1 hz)).contDiffAt.restrict_scalars ℝ)

lemma logarithmicTest_chart_local_jets (a : ℝ) {ε D r : ℝ} (he : ε ≠ 0)
    (hD : 1 ≤ D) (hr : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ), 1 ≤ k → ∀ P : Finset Sphere,
      ProjectivelySeparated (D/Real.sqrt k) P → ∀ U : Base ≃ₗᵢ[ℂ] Base,
      ∀ z ∈ Metric.ball (0:Base) (1/64),
      ‖iteratedFDeriv ℝ n (logarithmicTest a ε P k ∘ centeredChart r U) z‖ ≤ C*(1-(1-r)/16)^k := by
  have hG := gaussianConstant_pos
  let R := 1-(1-r)/16
  have hR : 0 < R := by dsimp [R]; linarith
  have hR1 : R < 1 := by dsimp [R]; linarith
  have hpb (k : ℕ) (hk : 1 ≤ k) (P : Finset Sphere)
      (hP : ProjectivelySeparated (D/Real.sqrt k) P) (U : Base ≃ₗᵢ[ℂ] Base)
      (z : Base) (hz : ‖z‖ < 1/32) :
      ‖peakPolynomial P k (centeredChart r U z)‖ ≤ gaussianConstant*R^k :=
    (peak_global_bound hD hk hP _).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (chart_norm_deficit hr hr1 U hz) k) gaussianConstant_pos.le)
  by_cases hn : n=0
  · subst n
    obtain ⟨C,hC,hCb⟩ := regularizedLog_lipschitz_bound a he gaussianConstant_pos.le
    refine ⟨C*gaussianConstant,by positivity,?_⟩
    intro k hk P hP U z hz
    have hp := hpb k hk P hP U z (by
      have hz' : ‖z‖ < 1/64 := by simpa using hz
      linarith)
    have hpG : ‖peakPolynomial P k (centeredChart r U z)‖ ≤ gaussianConstant :=
      hp.trans (mul_le_of_le_one_right gaussianConstant_pos.le (pow_le_one₀ hR.le hR1.le))
    rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs]
    exact (hCb _ hpG).trans ((mul_le_mul_of_nonneg_left hp hC).trans_eq (by ring))
  · obtain ⟨C,hC,hCb⟩ := regularizedLog_positive_jet_bound a he (by norm_num : (0:ℝ)<1/64)
      gaussianConstant_pos.le (by positivity : 0 ≤ 2*gaussianConstant) (by omega : 1 ≤ n)
    refine ⟨C,hC,?_⟩
    intro k hk P hP U z hz
    have hz' : ‖z‖ < 1/64 := by simpa using hz
    have hsub (x : Base) (hx : x ∈ Metric.ball z (1/64)) : ‖x‖ < 1/32 := by
      have hh := dist_triangle x z 0
      have hx' : dist x z < 1/64 := hx
      simp only [dist_zero_right] at hh
      linarith
    have hf : AnalyticOnNhd ℂ (peakPolynomial P k ∘ centeredChart r U) (Metric.ball z (1/64)) := by
      intro x hx
      have hxb : x ∈ ball := by change ‖x‖ < 1; linarith [hsub x hx]
      exact (peakPolynomial_analytic P k _ (mem_univ _)).comp
        (centeredChart_analyticAt U (centeredChart_den_ne_zero hr hr1 hxb))
    have hp := hpb k hk P hP U z (by linarith)
    have hpG : ‖peakPolynomial P k (centeredChart r U z)‖ ≤ gaussianConstant :=
      hp.trans (mul_le_of_le_one_right gaussianConstant_pos.le (pow_le_one₀ hR.le hR1.le))
    apply hCb _ z (R^k) hf hpG (pow_pos hR _) (pow_le_one₀ hR.le hR1.le)
    intro x hx
    apply (norm_sub_le _ _).trans
    dsimp only [Function.comp_apply]
    linarith [hpb k hk P hP U x (hsub x hx)]

lemma testSeries_chart_iteratedFDeriv (a : ℝ) {ε D : ℝ} (he : ε ≠ 0) (hD : 1 ≤ D)
    {Q : ℕ} (hQ : 2 ≤ Q) (P : ℕ → Finset Sphere)
    (hP : ∀ j, ProjectivelySeparated (D/Real.sqrt (Q^(j+1):ℕ)) (P (Q^(j+1))))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (U : Base ≃ₗᵢ[ℂ] Base) (n : ℕ) :
    iteratedFDeriv ℝ n ((fun y => ∑' j, logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) y) ∘ centeredChart r U) 0 =
      ∑' j, iteratedFDeriv ℝ n (logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) ∘ centeredChart r U) 0 := by
  choose C hC hb using (fun n => logarithmicTest_chart_local_jets a he hD hr hr1 n)
  have hs := summable_lacunary (by linarith : 0 ≤ 1-(1-r)/16) (by linarith : 1-(1-r)/16 < 1) hQ
  exact local_iteratedFDeriv_tsum_on
    (fun j z hz => logarithmicTest_chart_contDiffAt a he _ _ hr hr1 U
      (by
        have hz' : ‖z‖ < 1/64 := by simpa using hz
        change ‖z‖ < 1
        linarith))
    Metric.isOpen_ball (convex_ball (0:Base) (1/64)).isPreconnected
    (fun n => hs.mul_left (C n))
    (fun n j z hz => hb n _ (Nat.one_le_pow _ _ (by omega)) _ (hP j) U z hz) n
    (Metric.mem_ball_self (by norm_num))

end PinchedHartogs.BaseConstruction

end

end OAI
