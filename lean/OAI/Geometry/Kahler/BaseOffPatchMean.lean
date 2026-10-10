import OAI.Geometry.Kahler.BasePatchDecomposition

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
namespace PinchedHartogs.BaseConstruction

lemma regularized_peak_phase_mean {a ε ρ : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ ρ) (hε : ε ≠ 0)
    (P : Finset Sphere) {k : ℕ} (hk : 0 < k) (ξ : Sphere) :
    (∫ z : Circle, regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k (phaseAction z ξ)) ∂circleMeasure)=
      Real.log (logFactor (a*ρ*‖peakPolynomial P k ξ‖) ε)-Real.log (1+ε^2) := by
  have he : ∀ z : Circle, regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k (phaseAction z ξ))=
      regularizedLog 1 ε ((z:ℂ)^k*((a:ℂ)*(ρ:ℂ)*peakPolynomial P k ξ)) := by
    intro z
    rw [regularizedLog_rescale,phaseAction_coe,peakPolynomial_homogeneous]
    congr 1
    ring
  simp_rw [he]
  rw [circle_regularized_complex_mean hε _ hk]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hr]

lemma regularized_peak_phase_mean_bound {a ε ρ : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ ρ) (hr1 : ρ ≤ 1)
    (hε : ε ≠ 0) (P : Finset Sphere) {k : ℕ} (hk : 0 < k) (ξ : Sphere)
    (hsmall : a*‖peakPolynomial P k ξ‖ ≤ 1/2) :
    (∫ z : Circle, regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k (phaseAction z ξ)) ∂circleMeasure) ≤
      a*ε^2*‖peakPolynomial P k ξ‖ := by
  rw [regularized_peak_phase_mean ha hr hε P hk ξ]
  let n := ‖peakPolynomial P k ξ‖
  let q := a*ρ*n
  have hn : 0 ≤ n := norm_nonneg _
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqn : q ≤ a*n := by dsimp [q]; nlinarith [mul_nonneg ha hn]
  have hq1 : q ≤ 1/2 := hqn.trans hsmall
  have hsq : q^2 ≤ 1/4 := by nlinarith
  have hh := logFactor_small_mean_bound (ε := ε) hsq
  change Real.log (logFactor q ε)-Real.log (1+ε^2) ≤ a*ε^2*n
  apply hh.trans
  have hq2 : 2*q^2 ≤ a*n := by nlinarith
  nlinarith [mul_nonneg (sq_nonneg ε) (sub_nonneg.mpr hq2)]

lemma regularized_peak_phase_mean_continuous {a ε ρ : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ ρ)
    (hε : ε ≠ 0) (P : Finset Sphere) {k : ℕ} (hk : 0 < k) :
    Continuous (fun ξ : Sphere => ∫ z : Circle,
      regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k (phaseAction z ξ)) ∂circleMeasure) := by
  simp_rw [regularized_peak_phase_mean ha hr hε P hk]
  have hP : Continuous (fun ξ : Sphere => peakPolynomial P k ξ) :=
    (peakPolynomial_analytic P k).continuous.comp continuous_subtype_val
  have hL : Continuous (fun ξ : Sphere => logFactor (a*ρ*‖peakPolynomial P k ξ‖) ε) :=
    logFactor_continuous.comp ((continuous_const.mul hP.norm).prodMk continuous_const)
  exact (hL.log (fun ξ => (logFactor_pos _ _).ne')).sub continuous_const

lemma peak_off_set_integral {a ε ρ : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ ρ) (hr1 : ρ ≤ 1)
    (hε : ε ≠ 0) (P : Finset Sphere) {k : ℕ} (hk : 0 < k)
    {s : Set Sphere} (hs : MeasurableSet s)
    (hinv : ∀ z ξ, phaseAction z ξ ∈ s ↔ ξ ∈ s)
    (hsmall : ∀ ξ ∈ s, a*‖peakPolynomial P k ξ‖ ≤ 1/2) :
    (∫ ξ in s, regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ) ∂sigma) ≤
      2*a*ε^2*(P.card:ℝ)/k := by
  let V : Sphere → ℝ := fun ξ => regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ)
  have hP : Continuous (fun ξ : Sphere => peakPolynomial P k ξ) :=
    (peakPolynomial_analytic P k).continuous.comp continuous_subtype_val
  have hV : Continuous V := (regularizedLog_contDiff a hε).continuous.comp (continuous_const.mul hP)
  have hA : Continuous (fun ξ : Sphere => ∫ z : Circle, V (phaseAction z ξ) ∂circleMeasure) :=
    regularized_peak_phase_mean_continuous ha hr hε P hk
  have hN : Continuous (fun ξ : Sphere => a*ε^2*‖peakPolynomial P k ξ‖) := continuous_const.mul hP.norm
  change (∫ ξ in s, V ξ ∂sigma) ≤ _
  rw [sigma_phase_average_restrict hV hs hinv]
  calc
    _ ≤ ∫ ξ in s, a*ε^2*‖peakPolynomial P k ξ‖ ∂sigma := by
      apply setIntegral_mono_on (compact_continuous_integrable hA) (compact_continuous_integrable hN) hs
      intro ξ hξ
      exact regularized_peak_phase_mean_bound ha hr hr1 hε P hk ξ (hsmall ξ hξ)
    _ ≤ ∫ ξ, a*ε^2*‖peakPolynomial P k ξ‖ ∂sigma := by
      apply setIntegral_le_integral (compact_continuous_integrable hN)
      exact Eventually.of_forall (fun ξ => by positivity)
    _ = a*ε^2*(∫ ξ, ‖peakPolynomial P k ξ‖ ∂sigma) := integral_const_mul _ _
    _ ≤ a*ε^2*(2*(P.card:ℝ)/(k+2)) := by
      gcongr
      exact peak_integral_bound P k
    _ ≤ _ := by
      have hk0 : (0:ℝ) < k := by exact_mod_cast hk
      have hm : 2*(P.card:ℝ)/(k+2:ℝ) ≤ 2*(P.card:ℝ)/k := by gcongr; linarith
      have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ a*ε^2 by positivity)
      convert! hh using 1; ring

end PinchedHartogs.BaseConstruction

end

end OAI
