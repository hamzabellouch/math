import OAI.Geometry.Kahler.BaseNegativeThreshold

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma logarithmicTest_scaled (a ε r : ℝ) (P : Finset Sphere) (k : ℕ) (ξ : Sphere) :
    logarithmicTest a ε P k ((r:ℂ) • (ξ:Base)) =
      regularizedLog 1 ε (((a:ℂ)*(r:ℂ)^k)*peakPolynomial P k ξ) := by
  rw [logarithmicTest,peakPolynomial_homogeneous,regularizedLog_scale]
  congr 1
  ring

lemma logarithmicTest_later_comparison {a : ℝ} (ha : 0 ≤ a) (pr : RadialProfiles a)
    {Q M i N : ℕ} (hQ : 2 ≤ Q) (hM : M+2 < Q) (hi : 1 ≤ i) (hiN : i ≤ N)
    (P : ℕ → Finset Sphere) {D : ℝ} (hD : 1 ≤ D)
    (hP : ProjectivelySeparated (D/Real.sqrt (Q^i:ℕ)) (P (Q^i)))
    {ε θ r : ℝ} (he : ε ≠ 0) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hb : ∀ q ∈ Icc 0 (a*gaussianConstant), q/logFactor q ε ≤ θ)
    (hposi : ∀ ξ : Sphere, 0 ≤ density Q pr.R pr.f pr.b P i ξ)
    (hposN : ∀ ξ : Sphere, 0 ≤ density Q pr.R pr.f pr.b P N ξ)
    [IsProbabilityMeasure (densityMeasure (density Q pr.R pr.f pr.b P i))]
    [IsProbabilityMeasure (densityMeasure (density Q pr.R pr.f pr.b P N))] :
    |(∫ ξ : Sphere, logarithmicTest a ε (P (Q^i)) (Q^i) ((r:ℂ) • (ξ:Base)) ∂densityMeasure (density Q pr.R pr.f pr.b P N))-
      (∫ ξ : Sphere, logarithmicTest a ε (P (Q^i)) (Q^i) ((r:ℂ) • (ξ:Base)) ∂densityMeasure (density Q pr.R pr.f pr.b P i))| ≤
      4*θ^(M+1)/(1-θ) := by
  simp_rw [logarithmicTest_scaled]
  apply density_log_comparison pr hQ hM hiN P he hθ hθ1 _ _ hposi hposN
  intro ξ
  rw [logNormalized,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (logFactor_pos _ _)]
  apply hb _
  constructor
  · exact norm_nonneg _
  · rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Complex.norm_real,
      Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hr]
    have hk : 1 ≤ Q^i := (show 1 ≤ Q by omega).trans
      (le_self_pow (by omega) (Nat.ne_of_gt hi))
    calc a*r^(Q^i)*‖peakPolynomial (P (Q^i)) (Q^i) ξ‖ ≤ a*1*gaussianConstant :=
          mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_one₀ hr hr1) ha)
            (peak_sphere_bound hD hk hP ξ) (norm_nonneg _) (by positivity)
         _ = _ := by ring

end PinchedHartogs.BaseConstruction

end

end OAI
