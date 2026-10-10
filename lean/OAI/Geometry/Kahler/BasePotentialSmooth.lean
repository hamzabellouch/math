import OAI.Geometry.Kahler.BaseLocalSmoothSeries

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

lemma lacunary_degree_ge {Q : ℕ} (hQ : 2 ≤ Q) (j : ℕ) : j+1 ≤ Q^(j+1) := by
  have hh : j+1 ≤ 2^(j+1) := (Nat.lt_two_pow_self (n := j+1)).le
  exact hh.trans (Nat.pow_le_pow_left hQ _)

lemma summable_lacunary {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1) {Q : ℕ} (hQ : 2 ≤ Q) :
    Summable (fun j : ℕ => R^(Q^(j+1))) := by
  apply Summable.of_nonneg_of_le (fun j => pow_nonneg hR _) _
    ((summable_geometric_of_lt_one hR hR1).mul_right R)
  intro j
  rw [← pow_succ]
  exact pow_le_pow_of_le_one hR hR1.le (lacunary_degree_ge hQ j)

lemma logarithmicTest_local_jets (a : ℝ) {ε D r R : ℝ} (he : ε ≠ 0) (hD : 1 ≤ D)
    (hr : 0 ≤ r) (hrR : r < R) (hR1 : R < 1) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ), 1 ≤ k → ∀ P : Finset Sphere,
      ProjectivelySeparated (D/Real.sqrt k) P → ∀ z ∈ Metric.ball (0:Base) r,
      ‖iteratedFDeriv ℝ n (logarithmicTest a ε P k) z‖ ≤ C*R^k := by
  have hR : 0 < R := lt_of_le_of_lt hr hrR
  have hG : 0 < gaussianConstant := gaussianConstant_pos
  by_cases hn : n=0
  · subst n
    obtain ⟨C,hC,hCb⟩ := regularizedLog_lipschitz_bound a he hG.le
    refine ⟨C*gaussianConstant,by positivity,?_⟩
    intro k hk P hP z hz
    have hzn : ‖z‖ ≤ R := (show ‖z‖ < r by simpa using hz).le.trans hrR.le
    have hp := (peak_global_bound hD hk hP z).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hzn _) hG.le)
    have hpG : ‖peakPolynomial P k z‖ ≤ gaussianConstant := hp.trans (by
      exact mul_le_of_le_one_right hG.le (pow_le_one₀ hR.le hR1.le))
    rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs]
    exact (hCb _ hpG).trans ((mul_le_mul_of_nonneg_left hp hC).trans_eq (by ring))
  · let ρ : ℝ := (R-r)/2
    have hρ : 0 < ρ := by dsimp [ρ]; linarith
    obtain ⟨C,hC,hCb⟩ := regularizedLog_positive_jet_bound a he hρ hG.le
      (by positivity : 0 ≤ 2*gaussianConstant) (by omega : 1 ≤ n)
    refine ⟨C,hC,?_⟩
    intro k hk P hP z hz
    have hzn : ‖z‖ < r := by simpa using hz
    have hpr (x : Base) (hx : ‖x‖ ≤ R) : ‖peakPolynomial P k x‖ ≤ gaussianConstant*R^k :=
      (peak_global_bound hD hk hP x).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx _) hG.le)
    have hnormz := hpr z (by linarith)
    have hpG : ‖peakPolynomial P k z‖ ≤ gaussianConstant := hnormz.trans
      (mul_le_of_le_one_right hG.le (pow_le_one₀ hR.le hR1.le))
    apply hCb (peakPolynomial P k) z (R^k) ((peakPolynomial_analytic P k).mono (subset_univ _)) hpG
      (pow_pos hR _) (pow_le_one₀ hR.le hR1.le)
    intro x hx
    have hdist : dist x z < ρ := hx
    have htriangle := dist_triangle x z 0
    have hxR : ‖x‖ ≤ R := by rw [dist_zero_right,dist_zero_right] at htriangle; dsimp [ρ] at hdist; linarith
    exact (norm_sub_le _ _).trans (by linarith [hpr x hxR])

lemma testSeries_contDiffOn (a : ℝ) {ε D : ℝ} (he : ε ≠ 0) (hD : 1 ≤ D)
    {Q : ℕ} (hQ : 2 ≤ Q) (P : ℕ → Finset Sphere)
    (hP : ∀ j, ProjectivelySeparated (D/Real.sqrt (Q^(j+1):ℕ)) (P (Q^(j+1)))) :
    ContDiffOn ℝ ∞ (fun z => ∑' j, logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) z) ball := by
  intro z hz
  have hz1 : ‖z‖ < 1 := hz
  let r := (‖z‖+1)/2
  let R := (r+1)/2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [R]; linarith
  have hR1 : R < 1 := by dsimp [R]; linarith
  have hzR : z ∈ Metric.ball 0 r := by simpa [r] using (by linarith : ‖z‖ < (‖z‖+1)/2)
  choose C hC hb using (fun n => logarithmicTest_local_jets a he hD hr hrR hR1 n)
  have hs := local_contDiff_tsum (fun j => logarithmicTest_contDiff a he _ _)
    Metric.isOpen_ball (convex_ball (0:Base) r).isPreconnected
    (fun n => (summable_lacunary (hr.trans hrR.le) hR1 hQ).mul_left (C n))
    (fun n j y hy => hb n (Q^(j+1)) (Nat.one_le_pow _ _ (by omega)) _ (hP j) y hy)
  exact (hs.contDiffAt (Metric.isOpen_ball.mem_nhds hzR)).contDiffWithinAt

lemma basePotential_contDiffOn (a L : ℝ) {ε D : ℝ} (he : ε ≠ 0) (hD : 1 ≤ D)
    {Q : ℕ} (hQ : 2 ≤ Q) (P : ℕ → Finset Sphere)
    (hP : ∀ j, ProjectivelySeparated (D/Real.sqrt (Q^(j+1):ℕ)) (P (Q^(j+1)))) :
    ContDiffOn ℝ ∞ (basePotential P a ε L Q) ball := by
  apply ContDiffOn.add (fun z hz => (psi_contDiffAt hz).contDiffWithinAt)
  exact contDiffOn_const.mul (testSeries_contDiffOn a he hD hQ P hP)

end PinchedHartogs.BaseConstruction

end

end OAI
