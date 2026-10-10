import OAI.Geometry.Kahler.BaseDensityTheorem

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

lemma circle_pow_surjective {k : ℕ} (hk : 0 < k) : Function.Surjective (fun z : Circle => z^k) := by
  intro z
  obtain ⟨x,rfl⟩ := Circle.exp_surjective z
  refine ⟨Circle.exp (x/k),?_⟩
  dsimp only
  rw [← Circle.exp_nsmul,nsmul_eq_mul]
  congr 1
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

lemma circle_pow_measurePreserving {k : ℕ} (hk : 0 < k) :
    MeasurePreserving (fun z : Circle => z^k) circleMeasure circleMeasure :=
  (powMonoidHom (α := Circle) k).measurePreserving (continuous_pow k) (circle_pow_surjective hk) rfl

lemma circle_pow_integral {k : ℕ} (hk : 0 < k) {F : Circle → ℝ} (hF : Continuous F) :
    (∫ z : Circle, F (z^k) ∂circleMeasure)=∫ z : Circle, F z ∂circleMeasure := by
  have hp := circle_pow_measurePreserving hk
  calc
    _ = ∫ z : Circle, F z ∂Measure.map (fun z : Circle => z^k) circleMeasure :=
      (integral_map hp.measurable.aemeasurable hF.aestronglyMeasurable).symm
    _ = _ := by rw [hp.map_eq]

lemma regularizedLog_rescale (a ε : ℝ) (v : ℂ) : regularizedLog a ε v=regularizedLog 1 ε ((a:ℂ)*v) := by
  simp only [regularizedLog,Complex.ofReal_one,one_mul]

lemma circle_regularized_mean {q ε : ℝ} (hq : 0 ≤ q) (hε : ε ≠ 0) :
    (∫ z : Circle, regularizedLog 1 ε ((q:ℂ)*(z:ℂ)) ∂circleMeasure)=
      Real.log (logFactor q ε)-Real.log (1+ε^2) := by
  simpa only [zero_mul,add_zero,mul_one,zero_div,sub_zero] using regularized_circle_moments hq hε 0

lemma circle_regularized_power_moments {q ε : ℝ} (hq : 0 ≤ q) (hε : ε ≠ 0)
    {k : ℕ} (hk : 0 < k) (f : ℝ) :
    (∫ z : Circle, regularizedLog 1 ε ((q:ℂ)*(z:ℂ)^k)*(1+f*((z:ℂ)^k).re) ∂circleMeasure)=
      Real.log (logFactor q ε)-Real.log (1+ε^2)-f*q/logFactor q ε := by
  have hc : Continuous (fun z : Circle => regularizedLog 1 ε ((q:ℂ)*(z:ℂ))*(1+f*(z:ℂ).re)) :=
    ((regularizedLog_contDiff 1 hε).continuous.comp (by fun_prop)).mul (by fun_prop)
  have he := circle_pow_integral hk hc
  simp only [Circle.coe_pow] at he
  rw [he,regularized_circle_moments hq hε]

lemma circle_regularized_complex_mean {ε : ℝ} (hε : ε ≠ 0) (v : ℂ) {k : ℕ} (hk : 0 < k) :
    (∫ z : Circle, regularizedLog 1 ε ((z:ℂ)^k*v) ∂circleMeasure)=
      Real.log (logFactor ‖v‖ ε)-Real.log (1+ε^2) := by
  by_cases hv : v=0
  · subst v
    simp only [mul_zero,regularizedLog_zero,integral_zero,norm_zero]
    have hh : logFactor 0 ε=1+ε^2 := by simpa using logFactor_equation 0 ε
    rw [hh,sub_self]
  have hn := norm_pos_iff.mpr hv
  let u : Circle := ⟨v/(‖v‖:ℂ),by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hn,div_self hn.ne']⟩
  have hu : (‖v‖:ℂ)*(u:ℂ)=v := by
    dsimp [u]
    have hnc : (‖v‖:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp [hnc]
  have hc : Continuous (fun z : Circle => regularizedLog 1 ε ((z:ℂ)*v)) :=
    (regularizedLog_contDiff 1 hε).continuous.comp (by fun_prop)
  have he := circle_pow_integral hk hc
  simp only [Circle.coe_pow] at he
  rw [he]
  have hm := integral_mul_right_eq_self (μ := circleMeasure)
    (fun z : Circle => regularizedLog 1 ε ((‖v‖:ℂ)*(z:ℂ))) u
  have heq : ∀ z : Circle, (‖v‖:ℂ)*((z*u:Circle):ℂ)=(z:ℂ)*v := by
    intro z
    rw [Circle.coe_mul,mul_left_comm,hu]
  simp_rw [heq] at hm
  rw [hm,circle_regularized_mean (norm_nonneg _) hε]

lemma logFactor_small_mean_bound {q ε : ℝ} (hq : q^2 ≤ 1/4) :
    Real.log (logFactor q ε)-Real.log (1+ε^2) ≤ 2*ε^2*q^2 := by
  let L := logFactor q ε
  have hL : 1 ≤ L := logFactor_one_le q ε
  have hp : 0 < L := logFactor_pos q ε
  have hA : 0 < 1+ε^2 := by positivity
  have he := logFactor_equation q ε
  change L+q^2/L=1+q^2+ε^2 at he
  have hle : q^2/L ≤ q^2 := div_le_self (sq_nonneg _) hL
  have hAL : 1+ε^2 ≤ L := by linarith
  have hpoly : (L-(1+ε^2))*(L-q^2)=q^2*ε^2 := by
    field_simp at he
    nlinarith
  have hdiff : L-(1+ε^2) ≤ 2*ε^2*q^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hAL) (show 0 ≤ L-q^2-1/2 by linarith)]
  have hlog := Real.log_le_sub_one_of_pos (div_pos hp hA)
  rw [Real.log_div hp.ne' hA.ne'] at hlog
  apply hlog.trans
  have hm : L-(1+ε^2) ≤ (2*ε^2*q^2)*(1+ε^2) :=
    hdiff.trans (le_mul_of_one_le_right (by positivity) (by nlinarith [sq_nonneg ε]))
  rw [div_sub_one hA.ne']
  exact (div_le_iff₀ hA).mpr hm

end PinchedHartogs.BaseConstruction

end

end OAI
