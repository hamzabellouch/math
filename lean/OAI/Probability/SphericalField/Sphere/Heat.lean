import Mathlib
import OAI.Probability.SphericalField.Sphere.RadialBands
import OAI.Probability.SphericalField.Heat.Entropic

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace SphericalPerceptron

def logSphericalExp (n : ℕ) (R : ℝ) (x : Spin (n+1)) : ℝ :=
  Real.log (sphericalExp n x R)

lemma sphericalExp_le_mul (n : ℕ) (R : ℝ) (x y : Spin (n+1)) :
    sphericalExp n x R ≤ Real.exp (|R| *‖x-y‖)*sphericalExp n y R := by
  unfold sphericalExp
  rw [← integral_const_mul]
  apply integral_mono (unitSphere_continuous_integrable (by fun_prop))
    (unitSphere_continuous_integrable (by fun_prop))
  intro u
  dsimp only
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hu : ‖(u:Spin (n+1))‖=1 := by simp
  have hh := abs_real_inner_le_norm (x-y) (u:Spin (n+1))
  rw [hu,mul_one,inner_sub_left] at hh
  have hm := mul_le_mul_of_nonneg_left hh (abs_nonneg R)
  rw [← abs_mul] at hm
  have hl := (le_abs_self (R*(inner ℝ x (u:Spin (n+1))-inner ℝ y (u:Spin (n+1))))).trans hm
  linarith

lemma logSphericalExp_lipschitz (n : ℕ) (R : ℝ) :
    LipschitzWith ⟨|R|,abs_nonneg R⟩ (logSphericalExp n R) := by
  have hle (x y : Spin (n+1)) : logSphericalExp n R x-logSphericalExp n R y ≤ |R| *‖x-y‖ := by
    have hx : 0 < sphericalExp n x R := lt_of_lt_of_le zero_lt_one (one_le_sphericalExp n x R)
    have hy : 0 < sphericalExp n y R := lt_of_lt_of_le zero_lt_one (one_le_sphericalExp n y R)
    have hh := Real.log_le_log hx (sphericalExp_le_mul n R x y)
    rw [Real.log_mul (Real.exp_pos _).ne' hy.ne',Real.log_exp] at hh
    change Real.log (sphericalExp n x R)-Real.log (sphericalExp n y R) ≤ _
    linarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |logSphericalExp n R x-logSphericalExp n R y| ≤ |R| *‖x-y‖
  apply abs_le.mpr
  constructor
  · have hh := hle y x
    rw [norm_sub_rev] at hh
    linarith
  · exact hle x y

lemma logSphericalExp_nonneg (n : ℕ) (R : ℝ) (x : Spin (n+1)) :
    0 ≤ logSphericalExp n R x := Real.log_nonneg (one_le_sphericalExp n x R)

lemma logSphericalExp_zero (n : ℕ) (R : ℝ) : logSphericalExp n R 0=0 := by
  simp [logSphericalExp,sphericalExp]

lemma integral_exp_inner_stdGaussian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (v : E) (a : ℝ) : (∫ x, Real.exp (a*inner ℝ v x) ∂stdGaussian E)=
      Real.exp (a^2*‖v‖^2/2) := by
  have H := mgf_gaussianReal ⟨(innerSL ℝ v).measurable.aemeasurable,
    IsGaussian.map_eq_gaussianReal (μ := stdGaussian E) (innerSL ℝ v)⟩ a
  simp only [integral_strongDual_stdGaussian,variance_dual_stdGaussian,innerSL_apply_norm,Real.coe_toNNReal (‖v‖^2) (sq_nonneg ‖v‖),zero_mul,zero_add] at H
  change (∫ x, Real.exp (a*inner ℝ v x) ∂stdGaussian E)=Real.exp (‖v‖^2*a^2/2) at H
  convert H using 1
  congr 1
  ring

lemma sphericalExp_gaussian_average (n : ℕ) (R σ : ℝ) (x : Spin (n+1)) :
    (∫ y, sphericalExp n (x+σ • y) R ∂stdGaussian (Spin (n+1)))=
      Real.exp (R^2*σ^2/2)*sphericalExp n x R := by
  let μ := stdGaussian (Spin (n+1))
  let ν := unitSphereLaw (n+1)
  have hI : Integrable (fun p : Spin (n+1)×Metric.sphere (0:Spin (n+1)) 1 =>
      Real.exp (R*inner ℝ (x+σ • p.1) (p.2:Spin (n+1)))) (μ.prod ν) := by
    apply (((gaussian_integrable_exp_norm μ (|R| *|σ|)).const_mul (Real.exp (|R| *‖x‖))).comp_fst ν).mono' (by fun_prop)
    exact ae_of_all _ fun p => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hu : ‖(p.2:Spin (n+1))‖=1 := by simp
      have hh := abs_real_inner_le_norm (x+σ • p.1) (p.2:Spin (n+1))
      rw [hu,mul_one] at hh
      have ht := norm_add_le x (σ • p.1)
      rw [norm_smul,Real.norm_eq_abs] at ht
      have hb := mul_le_mul_of_nonneg_left (hh.trans ht) (abs_nonneg R)
      rw [← abs_mul] at hb
      have hl := (le_abs_self (R*inner ℝ (x+σ • p.1) (p.2:Spin (n+1)))).trans hb
      nlinarith
  have H := integral_integral_swap (f := fun (y : Spin (n+1)) (u : Metric.sphere (0:Spin (n+1)) 1) =>
    Real.exp (R*inner ℝ (x+σ • y) (u:Spin (n+1)))) hI
  change (∫ y, ∫ u, Real.exp (R*inner ℝ (x+σ • y) (u:Spin (n+1))) ∂ν ∂μ)=_ at H
  change (∫ y, ∫ u, Real.exp (R*inner ℝ (x+σ • y) (u:Spin (n+1))) ∂ν ∂μ)=_
  rw [H]
  have he (u : Metric.sphere (0:Spin (n+1)) 1) :
      (∫ y : Spin (n+1), Real.exp (R*inner ℝ (x+σ • y) (u:Spin (n+1))) ∂μ)=
        Real.exp (R^2*σ^2/2)*Real.exp (R*inner ℝ x (u:Spin (n+1))) := by
    simp only [inner_add_left,real_inner_smul_left,mul_add,Real.exp_add]
    rw [integral_const_mul]
    have hh := integral_exp_inner_stdGaussian (u:Spin (n+1)) (R*σ)
    have hu : ‖(u:Spin (n+1))‖=1 := by simp
    rw [hu] at hh
    simp only [one_pow,mul_one] at hh
    have hinner : (fun y : Spin (n+1) => Real.exp (R*(σ*inner ℝ y (u:Spin (n+1)))))=
        (fun y => Real.exp ((R*σ)*inner ℝ (u:Spin (n+1)) y)) := by
      funext y
      rw [real_inner_comm y (u:Spin (n+1))]
      congr 1
      ring
    rw [hinner,hh,mul_pow]
    ring
  simp_rw [he]
  rw [integral_const_mul]
  rfl

lemma gaussianEntropic_logSphericalExp_one (n : ℕ) (R σ : ℝ) (x : Spin (n+1)) :
    gaussianEntropic (stdGaussian (Spin (n+1))) 1 σ (logSphericalExp n R) x=
      logSphericalExp n R x+R^2*σ^2/2 := by
  rw [gaussianEntropic_pos _ (logSphericalExp_lipschitz n R) (by norm_num)]
  simp only [one_mul,div_one,logSphericalExp]
  simp_rw [Real.exp_log (lt_of_lt_of_le zero_lt_one (one_le_sphericalExp n _ R))]
  rw [sphericalExp_gaussian_average,Real.log_mul (Real.exp_pos _).ne'
    (lt_of_lt_of_le zero_lt_one (one_le_sphericalExp n x R)).ne',Real.log_exp]
  ring

end SphericalPerceptron
end
end

end OAI
