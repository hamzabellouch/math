import OAI.Geometry.Kahler.BaseLogApproximation

namespace OAI

universe uKahler12650_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma logNormalized_unit_mul (ε : ℝ) {c : ℂ} (hc : ‖c‖=1) (v : ℂ) :
    logNormalized ε (c*v)=c*logNormalized ε v := by
  simp only [logNormalized,norm_mul,hc,one_mul,mul_div_assoc]

lemma logMean_unit_mul (ε : ℝ) {c : ℂ} (hc : ‖c‖=1) (v : ℂ) :
    logMean ε (c*v)=logMean ε v := by simp only [logMean,norm_mul,hc,one_mul]

lemma logNormalized_peak_phase (ε : ℝ) (c : ℂ) (P : Finset Sphere) (k n : ℕ) :
    ∀ z : Circle, ∀ ξ : Sphere,
      (logNormalized ε (c*peakPolynomial P k (phaseAction z ξ)))^n =
        phaseChar (k*n) z*(logNormalized ε (c*peakPolynomial P k ξ))^n := by
  intro z ξ
  rw [phaseAction_coe,peakPolynomial_homogeneous]
  have he : c*((z:ℂ)^k*peakPolynomial P k ξ)=(z:ℂ)^k*(c*peakPolynomial P k ξ) := by ring
  rw [he,logNormalized_unit_mul ε (by rw [norm_pow,z.norm_coe,one_pow] : ‖(z:ℂ)^k‖=1),mul_pow,← pow_mul]
  simp only [← Nat.cast_mul,phaseChar,zpow_natCast,Circle.coe_pow]

lemma logMean_peak_phase (ε : ℝ) (c : ℂ) (P : Finset Sphere) (k : ℕ) :
    ∀ z : Circle, ∀ ξ : Sphere,
      (logMean ε (c*peakPolynomial P k (phaseAction z ξ)):ℂ) =
        phaseChar (0:ℕ) z*(logMean ε (c*peakPolynomial P k ξ):ℂ) := by
  intro z ξ
  rw [phaseAction_coe,peakPolynomial_homogeneous]
  have he : c*((z:ℂ)^k*peakPolynomial P k ξ)=(z:ℂ)^k*(c*peakPolynomial P k ξ) := by ring
  rw [he,logMean_unit_mul ε (by rw [norm_pow,z.norm_coe,one_pow] : ‖(z:ℂ)^k‖=1)]
  simp

lemma probability_integral_error {X : Type uKahler12650_1} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    {E : ℝ} (h : ∀ x, |f x-g x| ≤ E) : |(∫ x,f x ∂μ)-(∫ x,g x ∂μ)| ≤ E := by
  rw [← integral_sub hf hg,← Real.norm_eq_abs]
  calc
    _ ≤ ∫ x, ‖f x-g x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, E ∂μ := integral_mono (hf.sub hg).norm (integrable_const E)
      (fun x => by simpa only [Real.norm_eq_abs] using h x)
    _ = E := by simp

end PinchedHartogs.BaseConstruction

end

end OAI
