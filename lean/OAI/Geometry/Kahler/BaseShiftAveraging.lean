import OAI.Geometry.Kahler.BaseLaterComparison

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma root_invariant_shift_sum {k ℓ : ℕ} (hk : 0 < k) (hl : ℓ < k)
    {V : Circle → ℂ} (hi : Integrable V circleMeasure)
    (hV : ∀ z, V (Circle.exp (2*Real.pi/k)*z)=V z)
    (s : Finset ℤ) (b : ℤ → ℂ) (hband : ∀ n ∈ s, |n| ≤ (ℓ:ℤ)) :
    (∫ z, V z*(∑ n ∈ s, b n*phaseChar ((k:ℤ)+n) z) ∂circleMeasure) =
      (∫ z, V z*phaseChar k z ∂circleMeasure)*(if 0 ∈ s then b 0 else 0) := by
  have hki : Integrable (fun z => V z*phaseChar k z) circleMeasure :=
    hi.mul_bdd (phaseChar_continuous _).aestronglyMeasurable
      (Eventually.of_forall (fun z => (phaseChar_norm _ z).le))
  have hkiV : ∀ z, V (Circle.exp (2*Real.pi/k)*z)*phaseChar k (Circle.exp (2*Real.pi/k)*z)=V z*phaseChar k z := by
    intro z
    rw [hV,phaseChar_mul,phaseChar_root hk,one_mul]
  have hh := root_invariant_phaseSum hk hl hki hkiV s b hband
  rw [phaseSum_mean] at hh
  convert hh using 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    simp only [phaseSum,Finset.mul_sum,phaseChar_add]
    apply Finset.sum_congr rfl
    intro n hn
    ring)

lemma phase_real_integral {V : Circle → ℝ} {A : Circle → ℂ}
    (hi : Integrable (fun z => (V z:ℂ)*A z) circleMeasure) :
    (∫ z, V z*(A z).re ∂circleMeasure)=(∫ z, (V z:ℂ)*A z ∂circleMeasure).re := by
  have he : (∫ z, ((V z:ℂ)*A z).re ∂circleMeasure)=(∫ z, (V z:ℂ)*A z ∂circleMeasure).re := integral_re hi
  simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using he

lemma correction_orbit_averaging {k ℓ : ℕ} (hk : 0 < k) (hl : ℓ < k)
    (R : ℝ) (f b : ℝ → ℝ) {W : Base → ℝ} (hd : Differentiable ℝ W)
    (hb : PhaseBandwidth W ℓ) (hm : ∀ p : Sphere, (∫ z : Circle, W ((z:ℂ) • (p:Base)) ∂circleMeasure)=1)
    (p ξ : Sphere) {V : Circle → ℝ} (hVc : Continuous V)
    (hV : ∀ z, V (Circle.exp (2*Real.pi/k)*z)=V z) :
    (∫ z, V z*densityCorrection k R f b W p ((z:ℂ) • (ξ:Base)) ∂circleMeasure)=
      (∫ z, V z*densityCorrection k R f b (fun _ => 1) p ((z:ℂ) • (ξ:Base)) ∂circleMeasure) := by
  classical
  by_cases hpatch : Real.exp (-R/k) < ‖bracket (ξ:Base) (p:Base)‖
  swap
  · simp only [densityCorrection,circle_bracket_norm,ite_eq_right hpatch,mul_zero,integral_zero]
  have hξ : bracket (ξ:Base) (p:Base) ≠ 0 := norm_pos_iff.mp (lt_trans (Real.exp_pos _) hpatch)
  let q : Sphere := ⟨centralPoint p ξ,by simpa only [Metric.mem_sphere,dist_zero_right] using centralPoint_norm p hξ⟩
  obtain ⟨s,a,hs,he⟩ := hb q
  have hmean : (if 0 ∈ s then a 0 else 0)=1 := by
    rw [← phaseSum_mean]
    simp_rw [← he]
    rw [integral_complex_ofReal,hm,Complex.ofReal_one]
  have hz : 0 ∈ s := by by_contra hz; simp [hz] at hmean
  have ha0 : a 0=1 := by simpa [hz] using hmean
  let C : ℂ := (((‖bracket (ξ:Base) (p:Base)‖^2)⁻¹:ℝ):ℂ)*
    (bracket (ξ:Base) (p:Base)/(‖bracket (ξ:Base) (p:Base)‖:ℂ))^k
  let A : ℤ → ℂ := fun n => C*a n*((f (densityHeight k p ξ)-(n:ℝ)/k*b (densityHeight k p ξ):ℝ):ℂ)
  have hex : ∀ z : Circle, densityCorrection k R f b W p ((z:ℂ) • (ξ:Base))=
      (∑ n ∈ s, A n*phaseChar ((k:ℤ)+n) z).re := by
    intro z
    rw [densityCorrection,circle_bracket_norm,ite_eq_left hpatch]
    exact densityCorrectionRaw_phase_expansion k f b hd p ξ hξ s a he z
  have hcA : Continuous (fun z : Circle => ∑ n ∈ s, A n*phaseChar ((k:ℤ)+n) z) :=
    continuous_finsetSum _ (fun n _ => continuous_const.mul (phaseChar_continuous _))
  have hvi : Integrable (fun z : Circle => (V z:ℂ)) circleMeasure := compact_continuous_integrable (Complex.continuous_ofReal.comp hVc)
  have hhv := root_invariant_shift_sum hk hl hvi (fun z => congrArg Complex.ofReal (hV z)) s A hs
  rw [ite_eq_left hz] at hhv
  have hzero : A 0=C*(f (densityHeight k p ξ):ℂ) := by simp [A,ha0]
  rw [hzero] at hhv
  have heone : ∀ z : Circle, densityCorrection k R f b (fun _ => 1) p ((z:ℂ) • (ξ:Base))=
      ((C*(f (densityHeight k p ξ):ℂ))*phaseChar k z).re := by
    intro z
    rw [densityCorrection,circle_bracket_norm,ite_eq_left hpatch,densityCorrectionRaw_eq_re,
      circle_bracket_norm,bracket_smul,densityHeight_phase]
    have hfder : phaseDerivative (fun _ : Base => (1:ℝ)) (centralPoint p ((z:ℂ) • (ξ:Base)))=0 := by
      simp only [phaseDerivative,(hasFDerivAt_const (1:ℝ) _).fderiv,zero_apply]
    rw [hfder]
    simp only [mul_one,mul_zero,Complex.ofReal_zero,add_zero]
    have hchar : phaseChar (k:ℤ) z=(z:ℂ)^k := by simp only [phaseChar,zpow_natCast,Circle.coe_pow]
    rw [hchar,mul_div_assoc,mul_pow]
    dsimp [C]
    congr 1
    ring
  simp_rw [hex,heone]
  rw [phase_real_integral (compact_continuous_integrable ((Complex.continuous_ofReal.comp hVc).mul hcA)),hhv]
  have hright := phase_real_integral (V := V) (A := fun z : Circle => (C*(f (densityHeight k p ξ):ℂ))*phaseChar k z)
    (compact_continuous_integrable ((Complex.continuous_ofReal.comp hVc).mul (continuous_const.mul (phaseChar_continuous _))))
  rw [hright]
  congr 1
  simp_rw [show ∀ z : Circle, (V z:ℂ)*((C*(f (densityHeight k p ξ):ℂ))*phaseChar k z)=
      ((V z:ℂ)*phaseChar k z)*(C*(f (densityHeight k p ξ):ℂ)) by intro z; ring]
  rw [integral_mul_const]

end PinchedHartogs.BaseConstruction

end

end OAI
