import OAI.Geometry.Kahler.BasePatches

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff ENNReal
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma norm_derivative_complex {c : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hc : HasDerivAt c v t) (h0 : c t ≠ 0) :
    HasDerivAt (fun s => ‖c s‖) ((v/(c t)).re*‖c t‖) t := by
  have hn : ‖c t‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have hh := hc.norm_sq.sqrt (pow_ne_zero 2 hn)
  have he : (fun s => Real.sqrt (‖c s‖^2)) = fun s => ‖c s‖ := by funext s; exact Real.sqrt_sq (norm_nonneg _)
  rw [he] at hh
  convert! hh using 1
  rw [Real.sqrt_sq (norm_nonneg _)]
  simp only [Complex.div_re,Complex.normSq_eq_norm_sq,real_inner_eq_re_inner ℂ,RCLike.inner_apply]
  field_simp
  change _ = (v*star (c t)).re
  simp [Complex.mul_re]

lemma phase_derivative_complex {c : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hc : HasDerivAt c v t) (h0 : c t ≠ 0) :
    HasDerivAt (fun s => c s/(‖c s‖:ℂ))
      ((Complex.I*(v/(c t)).im)*(c t/(‖c t‖:ℂ))) t := by
  have hn : (‖c t‖:ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h0
  have hr := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (norm_derivative_complex hc h0)
  have hh := hc.div hr hn
  convert! hh using 1
  simp only [Function.comp_def,Complex.ofRealCLM_apply,Complex.ofReal_mul]
  have hsplit : v/(c t) = ((v/(c t)).re:ℂ)+Complex.I*((v/(c t)).im:ℂ) := by
    apply Complex.ext <;> simp
  have hv : v = (((v/(c t)).re:ℂ)+Complex.I*((v/(c t)).im:ℂ))*c t := by rw [← hsplit,div_mul_cancel₀ _ h0]
  nth_rewrite 2 [hv]
  field_simp
  ring

lemma centralPoint_curve_derivative (p : Sphere) {γ : ℝ → Base} {v : Base} {t : ℝ}
    (hγ : HasDerivAt γ v t) (h0 : bracket (γ t) (p:Base) ≠ 0) :
    HasDerivAt (fun s => centralPoint p (γ s))
      ((bracket v (p:Base)/bracket (γ t) (p:Base)).im • (Complex.I • centralPoint p (γ t))) t := by
  have hc : HasDerivAt (fun s => bracket (γ s) (p:Base)) (bracket v (p:Base)) t := by
    exact (((innerSL ℂ (p:Base)).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt t hγ
  convert! (phase_derivative_complex hc h0).smul_const (p:Base) using 1
  rw [← Complex.coe_smul]
  simp only [centralPoint,smul_smul]
  congr 1
  ring

lemma densityHeight_curve_derivative (k : ℕ) (p : Sphere) {γ : ℝ → Base} {v : Base} {t : ℝ}
    (hγ : HasDerivAt γ v t) (h0 : bracket (γ t) (p:Base) ≠ 0) :
    HasDerivAt (fun s => densityHeight k p (γ s))
      (-(k:ℝ)*(bracket v (p:Base)/bracket (γ t) (p:Base)).re) t := by
  have hc : HasDerivAt (fun s => bracket (γ s) (p:Base)) (bracket v (p:Base)) t := by
    exact (((innerSL ℂ (p:Base)).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt t hγ
  convert! ((norm_derivative_complex hc h0).log (norm_ne_zero_iff.mpr h0)).const_mul (-(k:ℝ)) using 1
  simp [mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr h0)]

lemma centralValue_curve_derivative {W : Base → ℝ} (hW : Differentiable ℝ W)
    (p : Sphere) {γ : ℝ → Base} {v : Base} {t : ℝ}
    (hγ : HasDerivAt γ v t) (h0 : bracket (γ t) (p:Base) ≠ 0) :
    HasDerivAt (fun s => W (centralPoint p (γ s)))
      ((bracket v (p:Base)/bracket (γ t) (p:Base)).im * phaseDerivative W (centralPoint p (γ t))) t := by
  convert! (hW _).hasFDerivAt.comp_hasDerivAt t (centralPoint_curve_derivative p hγ h0) using 1
  simp only [map_smul,smul_eq_mul,phaseDerivative]

end PinchedHartogs.BaseConstruction

end

end OAI
