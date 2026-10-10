import OAI.Geometry.Kahler.BasePhaseDerivatives

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

@[simp] lemma bracket_smul (c : ℂ) (z p : Base) : bracket (c • z) p = c*bracket z p := by
  simp [bracket]

lemma centralPoint_norm (p : Sphere) {ξ : Base} (hξ : bracket ξ (p:Base) ≠ 0) :
    ‖centralPoint p ξ‖=1 := by
  simp [centralPoint,norm_smul,Complex.norm_real,div_self (norm_ne_zero_iff.mpr hξ)]

lemma circle_bracket_norm (z : Circle) (ξ : Base) (p : Sphere) :
    ‖bracket ((z:ℂ) • ξ) (p:Base)‖ = ‖bracket ξ (p:Base)‖ := by simp [bracket_smul,z.norm_coe]

lemma centralPoint_phase (p : Sphere) (z : Circle) (ξ : Base) :
    centralPoint p ((z:ℂ) • ξ) = (z:ℂ) • centralPoint p ξ := by
  unfold centralPoint
  rw [circle_bracket_norm,bracket_smul,smul_smul]
  congr 1
  ring

lemma densityHeight_phase (k : ℕ) (p : Sphere) (z : Circle) (ξ : Base) :
    densityHeight k p ((z:ℂ) • ξ) = densityHeight k p ξ := by simp only [densityHeight,circle_bracket_norm]

lemma densityCorrectionRaw_eq_re (k : ℕ) (f b : ℝ → ℝ) (W : Base → ℝ) (p : Sphere) (ξ : Base) :
    densityCorrectionRaw k f b W p ξ =
      (((‖bracket ξ (p:Base)‖^2)⁻¹:ℝ) *
        (bracket ξ (p:Base)/(‖bracket ξ (p:Base)‖:ℂ))^k *
        ((f (densityHeight k p ξ)*W (centralPoint p ξ):ℝ) + Complex.I*
          (b (densityHeight k p ξ)/k*phaseDerivative W (centralPoint p ξ):ℝ))).re := by
  simp only [densityCorrectionRaw,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,
    zero_add,add_zero,sub_zero,one_mul]
  ring

lemma densityCorrectionRaw_phase_expansion (k : ℕ) (f b : ℝ → ℝ) {W : Base → ℝ}
    (hW : Differentiable ℝ W) (p : Sphere) (ξ : Base) (hξ : bracket ξ (p:Base) ≠ 0)
    (s : Finset ℤ) (a : ℤ → ℂ)
    (he : ∀ z : Circle, (W ((z:ℂ) • centralPoint p ξ):ℂ) = phaseSum s a z) (z : Circle) :
    densityCorrectionRaw k f b W p ((z:ℂ) • ξ) =
      (∑ n ∈ s,
        (((‖bracket ξ (p:Base)‖^2)⁻¹:ℝ) *
          (bracket ξ (p:Base)/(‖bracket ξ (p:Base)‖:ℂ))^k * a n *
          ((f (densityHeight k p ξ) - (n:ℝ)/k*b (densityHeight k p ξ):ℝ):ℂ)) *
          phaseChar ((k:ℤ)+n) z).re := by
  let q : Sphere := ⟨centralPoint p ξ,by simpa only [Metric.mem_sphere,dist_zero_right] using centralPoint_norm p hξ⟩
  have hT := phaseDerivative_expansion hW q s a he z
  rw [densityCorrectionRaw_eq_re,circle_bracket_norm,bracket_smul,centralPoint_phase,densityHeight_phase]
  have hph : ((z:ℂ)*bracket ξ (p:Base)/(‖bracket ξ (p:Base)‖:ℂ))^k =
      (z:ℂ)^k*(bracket ξ (p:Base)/(‖bracket ξ (p:Base)‖:ℂ))^k := by rw [mul_div_assoc,mul_pow]
  rw [hph]
  change (phaseDerivative W ((z:ℂ) • centralPoint p ξ):ℂ) = _ at hT
  push_cast
  rw [he,hT]
  unfold phaseSum
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [phaseChar_add]
  simp only [phaseChar,Circle.coe_zpow,zpow_natCast]
  have hi : Complex.I*Complex.I = -1 := Complex.I_mul_I
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

end PinchedHartogs.BaseConstruction

end

end OAI
