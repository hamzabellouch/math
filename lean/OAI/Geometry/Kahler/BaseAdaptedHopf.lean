import OAI.Geometry.Kahler.BaseRadialSubstitution

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

def adaptedHopf (p : Sphere) (t : unitInterval) (z : Circle × Circle) : Sphere :=
  sphereAction (adaptedIsometry p).symm (hopf (t,z))

lemma adaptedHopf_continuous (p : Sphere) : Continuous (fun x : unitInterval × (Circle × Circle) => adaptedHopf p x.1 x.2) :=
  (sphereAction (adaptedIsometry p).symm).continuous.comp hopf_continuous

lemma adaptedHopf_integral {F : Sphere → ℂ} (hF : Continuous F) (p : Sphere) :
    (∫ ξ, F ξ ∂sigma) = ∫ t : unitInterval, ∫ z, F (adaptedHopf p t z) ∂torusMeasure := by
  rw [← sigma_integral_unitary (adaptedIsometry p).symm F]
  exact hopf_integral_complex (hF.comp (sphereAction _).continuous)

lemma adaptedHopf_bracket (p : Sphere) (t : unitInterval) (z : Circle × Circle) :
    bracket (adaptedHopf p t z : Base) (p:Base)=(z.1:ℂ)*(Real.sqrt (t:ℝ):ℂ) := by
  rw [← adaptedIsometry_zero]
  simp only [adaptedHopf,sphereAction_coe,LinearIsometryEquiv.apply_symm_apply,hopf,torusAction_zero,radialSphere_zero]

lemma adaptedHopf_bracket_norm (p : Sphere) (t : unitInterval) (z : Circle × Circle) :
    ‖bracket (adaptedHopf p t z : Base) (p:Base)‖=Real.sqrt (t:ℝ) := by
  rw [adaptedHopf_bracket,norm_mul,z.1.norm_coe,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]

lemma adaptedHopf_phase (p : Sphere) (t : unitInterval) (ht : 0 < (t:ℝ)) (z : Circle × Circle) :
    bracket (adaptedHopf p t z : Base) (p:Base)/(‖bracket (adaptedHopf p t z : Base) (p:Base)‖:ℂ)=(z.1:ℂ) := by
  rw [adaptedHopf_bracket_norm,adaptedHopf_bracket,mul_div_cancel_right₀]
  exact_mod_cast Real.sqrt_ne_zero'.mpr ht

lemma adaptedHopf_height (k : ℕ) (p : Sphere) (t : unitInterval) (z : Circle × Circle) :
    densityHeight k p (adaptedHopf p t z) = -(k:ℝ)/2*Real.log (t:ℝ) := by
  rw [densityHeight,adaptedHopf_bracket_norm,Real.log_sqrt t.property.1]
  ring

lemma adaptedHopf_correction_expansion {W : Base → ℝ} (hW : Differentiable ℝ W)
    (k : ℕ) (f b : ℝ → ℝ) (p : Sphere) (t : unitInterval) (ht : 0 < (t:ℝ))
    (s : Finset ℤ) (a : ℤ → ℂ) (he : ∀ z : Circle, (W ((z:ℂ) • (p:Base)):ℂ)=phaseSum s a z)
    (z : Circle × Circle) :
    densityCorrectionRaw k f b W p (adaptedHopf p t z) =
      (∑ n ∈ s, ((t:ℝ)⁻¹:ℂ)*a n*
        ((f (-(k:ℝ)/2*Real.log (t:ℝ))-(n:ℝ)/k*b (-(k:ℝ)/2*Real.log (t:ℝ))):ℂ)*phaseChar ((k:ℤ)+n) z.1).re := by
  have hT := phaseDerivative_expansion hW p s a he z.1
  rw [densityCorrectionRaw_eq_re,adaptedHopf_phase p t ht z,adaptedHopf_bracket_norm,Real.sq_sqrt t.property.1,adaptedHopf_height]
  have hcentral : centralPoint p (adaptedHopf p t z)=(z.1:ℂ) • (p:Base) := by
    rw [centralPoint,adaptedHopf_phase p t ht z]
  rw [hcentral]
  push_cast
  rw [he,hT]
  unfold phaseSum
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [phaseChar_add]
  simp only [phaseChar,Circle.coe_zpow,zpow_natCast]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

lemma phase_shifted_real_moment (s : Finset ℤ) (a : ℤ → ℂ) (k : ℤ) (N : ℕ)
    (hs : ∀ n ∈ s, 0 < k+n) :
    (∫ z : Circle, phaseChar N z*((∑ n ∈ s, a n*phaseChar (k+n) z).re:ℂ) ∂circleMeasure) =
      if (N:ℤ)-k ∈ s then star (a ((N:ℤ)-k))/2 else 0 := by
  classical
  have he : ∀ z : Circle, phaseChar N z*((∑ n ∈ s, a n*phaseChar (k+n) z).re:ℂ) =
      ∑ n ∈ s, phaseChar N z*((a n*phaseChar (k+n) z).re:ℂ) := by
    intro z
    simp only [Complex.re_sum,Complex.ofReal_sum,Finset.mul_sum]
  simp_rw [he]
  rw [MeasureTheory.integral_finsetSum s (fun n hn => compact_continuous_integrable (by
    exact (phaseChar_continuous _).mul (Complex.continuous_ofReal.comp
      (Complex.continuous_re.comp (continuous_const.mul (phaseChar_continuous _))))))]
  have hsum : (∑ n ∈ s, ∫ z : Circle, phaseChar N z*((a n*phaseChar (k+n) z).re:ℂ) ∂circleMeasure) =
      ∑ n ∈ s, if k+n=(N:ℤ) then star (a n)/2 else 0 :=
    Finset.sum_congr rfl (fun n hn => phase_real_moment _ _ _ (hs n hn))
  rw [hsum]
  have hh : ∀ n : ℤ, k+n=(N:ℤ) ↔ n=(N:ℤ)-k := by intro n; omega
  simp_rw [hh]
  simp

end PinchedHartogs.BaseConstruction

end

end OAI
