import OAI.Geometry.Kahler.BaseTestSystem

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma logarithmicTest_value_bound (a : ℝ) {ε D : ℝ} (he : ε ≠ 0) (hD : 1 ≤ D) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, 1 ≤ k → ∀ P : Finset Sphere,
      ProjectivelySeparated (D/Real.sqrt k) P → ∀ z : Base, ‖z‖ ≤ 1 →
      ‖logarithmicTest a ε P k z‖ ≤ B*‖z‖^k := by
  obtain ⟨C,hC,hCb⟩ := regularizedLog_lipschitz_bound a he gaussianConstant_pos.le
  refine ⟨C*gaussianConstant,mul_nonneg hC gaussianConstant_pos.le,?_⟩
  intro k hk P hP z hz
  have hp := peak_global_bound hD hk hP z
  have hpG : ‖peakPolynomial P k z‖ ≤ gaussianConstant :=
    hp.trans (mul_le_of_le_one_right gaussianConstant_pos.le (pow_le_one₀ (norm_nonneg _) hz))
  exact (hCb _ hpG).trans ((mul_le_mul_of_nonneg_left hp hC).trans_eq (by ring))

lemma logarithmicTest_sphere_bound (a : ℝ) {ε D : ℝ} (he : ε ≠ 0) (hD : 1 ≤ D) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, 1 ≤ k → ∀ P : Finset Sphere,
      ProjectivelySeparated (D/Real.sqrt k) P → ∀ r ∈ Icc (0:ℝ) 1, ∀ ξ : Sphere,
      ‖logarithmicTest a ε P k ((r:ℂ) • (ξ:Base))‖ ≤ B*r^k := by
  obtain ⟨B,hB,hBb⟩ := logarithmicTest_value_bound a he hD
  refine ⟨B,hB,?_⟩
  intro k hk P hP r hr ξ
  have hn : ‖(r:ℂ) • (ξ:Base)‖=r := by simp [norm_smul,abs_of_nonneg hr.1]
  simpa only [hn] using hBb k hk P hP ((r:ℂ) • (ξ:Base)) (by simpa only [hn] using hr.2)

lemma logarithmicTest_integral_series (a : ℝ) {ε D : ℝ} (he : ε ≠ 0) (hD : 1 ≤ D)
    {Q : ℕ} (hQ : 2 ≤ Q) (P : ℕ → Finset Sphere)
    (hP : ∀ j, ProjectivelySeparated (D/Real.sqrt (Q^(j+1):ℕ)) (P (Q^(j+1))))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (μ : Measure Sphere) [IsProbabilityMeasure μ] :
    Summable (fun j => ∫ ξ : Sphere,
      logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) ((r:ℂ) • (ξ:Base)) ∂μ) ∧
    (∫ ξ : Sphere, (∑' j, logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) ((r:ℂ) • (ξ:Base))) ∂μ) =
      ∑' j, ∫ ξ : Sphere, logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) ((r:ℂ) • (ξ:Base)) ∂μ := by
  let f := fun j (ξ : Sphere) => logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) ((r:ℂ) • (ξ:Base))
  have hi (j : ℕ) : Integrable (f j) μ := continuous_integrable
    ((logarithmicTest_contDiff a he _ _).continuous.comp ((continuous_subtype_val : Continuous (fun ξ : Sphere => (ξ:Base))).const_smul (r:ℂ)))
  obtain ⟨B,hB,hBb⟩ := logarithmicTest_sphere_bound a he hD
  have hb (j : ℕ) (ξ : Sphere) : ‖f j ξ‖ ≤ B*r^(Q^(j+1)) :=
    hBb _ (Nat.one_le_pow _ _ (by omega)) _ (hP j) r ⟨hr,hr1.le⟩ ξ
  have hn (j : ℕ) : (∫ ξ, ‖f j ξ‖ ∂μ) ≤ B*r^(Q^(j+1)) := by
    have hh := integral_mono (hi j).norm
      (integrable_const (B*r^(Q^(j+1)))) (fun ξ => hb j ξ)
    simpa using hh
  have hs : Summable (fun j => ∫ ξ, ‖f j ξ‖ ∂μ) := Summable.of_nonneg_of_le
    (fun j => integral_nonneg (fun ξ => norm_nonneg _)) hn ((summable_lacunary hr hr1 hQ).mul_left B)
  exact ⟨Summable.of_norm_bounded hs (fun j => norm_integral_le_integral_norm _),
    (integral_tsum_of_summable_integral_norm hi hs).symm⟩

end PinchedHartogs.BaseConstruction

end

end OAI
