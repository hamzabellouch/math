import OAI.Geometry.Kahler.BaseGaussian

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma peak_global_bound {D : ℝ} (hD : 1 ≤ D) {k : ℕ} (hk : 1 ≤ k)
    {P : Finset Sphere} (hP : ProjectivelySeparated (D/Real.sqrt k) P) (z : Base) :
    ‖peakPolynomial P k z‖ ≤ gaussianConstant*‖z‖^k := by
  by_cases hz : z=0
  · subst z
    simp [peakPolynomial_zero P (by omega : k ≠ 0),show k ≠ 0 by omega]
  have hzn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  let ξ : Sphere := ⟨(‖z‖:ℂ)⁻¹ • z, by
    simp only [Metric.mem_sphere,dist_zero_right,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_norm]
    field_simp⟩
  have he : (‖z‖:ℂ) • (ξ:Base) = z := by
    exact smul_inv_smul₀ (by exact_mod_cast hzn : (‖z‖:ℂ) ≠ 0) z
  rw [← he,peakPolynomial_homogeneous,norm_mul,norm_pow]
  have hh := peak_sphere_bound hD hk hP ξ
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ ‖(‖z‖:ℂ)‖^k by positivity)
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_norm,he,mul_comm] using hm

lemma norm_coordinate_integral (k : ℕ) :
    (∫ ξ, ‖(ξ:Base) 0‖^k ∂sigma) = 2/(k+2:ℝ) := by
  let f : C(unitInterval,ℝ) := ⟨fun t => (Real.sqrt (t:ℝ))^k,by fun_prop⟩
  have hf := radial_continuous_integral f
  have he : ∀ ξ : Sphere, f (radialUnit ξ) = ‖(ξ:Base) 0‖^k := by
    intro ξ
    simp [f,radialUnit,radialU,Complex.normSq_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)]
  simp_rw [he] at hf
  rw [hf]
  change (∫ t : unitInterval, (Real.sqrt (t:ℝ))^k) = _
  rw [unitInterval.volume_def,integral_subtype_comap measurableSet_Icc (fun t : ℝ => (Real.sqrt t)^k)]
  have hr : ∀ t ∈ Icc (0:ℝ) 1, (Real.sqrt t)^k = t^((k:ℝ)/2) := by
    intro t ht
    rw [Real.sqrt_eq_rpow,← Real.rpow_natCast,← Real.rpow_mul ht.1]
    congr 1
    ring
  rw [setIntegral_congr_fun measurableSet_Icc hr,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),integral_rpow (Or.inl (by nlinarith [Nat.cast_nonneg (α := ℝ) k] : -1 < (k:ℝ)/2))]
  rw [Real.one_rpow,Real.zero_rpow (by positivity : (k:ℝ)/2+1 ≠ 0)]
  field_simp
  ring

lemma single_peak_integral (p : Sphere) (k : ℕ) :
    (∫ ξ, ‖bracket (ξ:Base) (p:Base)‖^k ∂sigma) = 2/(k+2:ℝ) := by
  have h := sigma_integral_unitary (adaptedIsometry p) (fun ξ : Sphere => ‖(ξ:Base) 0‖^k)
  simpa only [sphereAction_coe,adaptedIsometry_zero,norm_coordinate_integral] using h

lemma peak_integral_bound (P : Finset Sphere) (k : ℕ) :
    (∫ ξ, ‖peakPolynomial P k (ξ:Base)‖ ∂sigma) ≤ 2*P.card/(k+2:ℝ) := by
  have hcont : Continuous (fun ξ : Sphere => ‖peakPolynomial P k (ξ:Base)‖) :=
    ((peakPolynomial_analytic P k).continuous.comp continuous_subtype_val).norm
  have hpc : ∀ p ∈ P, Continuous (fun ξ : Sphere => ‖bracket (ξ:Base) (p:Base)‖^k) := by
    intro p hp
    exact (((bracket_analytic (p:Base)).continuous.comp continuous_subtype_val).norm).pow k
  calc
    _ ≤ ∫ ξ, ∑ p ∈ P, ‖bracket (ξ:Base) (p:Base)‖^k ∂sigma := by
      apply integral_mono (continuous_integrable hcont)
        (continuous_integrable (continuous_finsetSum _ hpc))
      intro ξ
      exact (norm_sum_le _ _).trans_eq (by simp only [norm_pow])
    _ = ∑ p ∈ P, ∫ ξ, ‖bracket (ξ:Base) (p:Base)‖^k ∂sigma := MeasureTheory.integral_finsetSum _ (fun p hp => continuous_integrable (hpc p hp))
    _ = _ := by simp only [single_peak_integral,Finset.sum_const,nsmul_eq_mul]; ring

end PinchedHartogs.BaseConstruction

end

end OAI
