import OAI.Geometry.RuledCovering.SingularEnergy

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma ceilingPolynomial_integral (p : ℝ) :
    (∫ b in Icc (-(1/2:ℝ)) (1/2), ceilingPolynomial p b) = (p+3)/120 := by
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : -(1/2:ℝ) ≤ 1/2)]
  have he : ceilingPolynomial p = fun b => (p/4)*b^2+(2-p)*b^4 := by
    funext b
    unfold ceilingPolynomial
    ring
  rw [he,intervalIntegral.integral_add ((by fun_prop : Continuous (fun b : ℝ => (p/4)*b^2)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun b : ℝ => (2-p)*b^4)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,integral_pow,integral_pow]
  norm_num
  ring

def angularEnergy (p eta : ℝ) : ℝ :=
  (1/4:ℝ)*(p+(2-p)*eta^2)^2+2*eta^2

lemma angularEnergy_continuous (p : ℝ) : Continuous (angularEnergy p) := by
  unfold angularEnergy
  fun_prop

lemma angularEnergy_integral (p : ℝ) :
    (∫ eta in (-1:ℝ)..1, angularEnergy p eta) = 2*(2*p^2+2*p+13)/15 := by
  have he : angularEnergy p = fun eta => p^2/4+(p*(2-p)/2+2)*eta^2+((2-p)^2/4)*eta^4 := by
    funext eta
    unfold angularEnergy
    ring
  have hI₁ : IntervalIntegrable (fun eta : ℝ => p^2/4+(p*(2-p)/2+2)*eta^2) volume (-1) 1 :=
    (by fun_prop : Continuous (fun eta : ℝ => p^2/4+(p*(2-p)/2+2)*eta^2)).intervalIntegrable _ _
  have hI₂ : IntervalIntegrable (fun eta : ℝ => ((2-p)^2/4)*eta^4) volume (-1) 1 :=
    (by fun_prop : Continuous (fun eta : ℝ => ((2-p)^2/4)*eta^4)).intervalIntegrable _ _
  rw [he,intervalIntegral.integral_add hI₁ hI₂,
    intervalIntegral.integral_add (intervalIntegrable_const)
      ((by fun_prop : Continuous (fun eta : ℝ => (p*(2-p)/2+2)*eta^2)).intervalIntegrable _ _),
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    integral_pow,integral_pow]
  norm_num
  ring

lemma singularEnergy_polar (p eta : ℝ) {r : ℝ} (hr : 0 < r) :
    singularEnergy p (vec2 (r*eta) r) = (1/4:ℝ)*(2*r)^(2*p-2)*angularEnergy p eta := by
  have he : (2*r) • vec2 (eta/2) (1/2) = vec2 (r*eta) r := by
    ext i
    fin_cases i
    · change (2*r)*(eta/2)=r*eta
      ring
    · change (2*r)*(1/2)=r
      ring
  have hv := singularField_smul p (show 0 < 2*r by positivity)
    (z := vec2 (eta/2) (1/2)) (by norm_num)
  rw [he,singularField_level] at hv
  have hpw : (2*r)^(2*p-2) = ((2*r)^(p-1))^2 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity)]
    congr 1
    ring
  unfold singularEnergy
  rw [hv,hpw]
  simp only [PiLp.smul_apply,smul_eq_mul,vec2_apply_zero,vec2_apply_one]
  unfold angularEnergy
  ring

lemma singularEnergy_slice_integral {p : ℝ} (hp : 1 < p) {r : ℝ} (hr : 0 ≤ r) :
    (∫ b in Icc (-r) r, singularEnergy p (vec2 b r)) =
      (2*r)^(2*p-1)/8 * (∫ eta in (-1:ℝ)..1, angularEnergy p eta) := by
  by_cases hr0 : r = 0
  · subst r
    simp [Real.zero_rpow (show 2*p-1 ≠ 0 by linarith)]
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (a := (-1:ℝ)) (b := 1) (fun b : ℝ => singularEnergy p (vec2 b r)) r
  simp only [smul_eq_mul,mul_neg_one,mul_one] at hs
  rw [← hs]
  have hi : (∫ eta in (-1:ℝ)..1, singularEnergy p (vec2 (r*eta) r)) =
      (1/4:ℝ)*(2*r)^(2*p-2)*(∫ eta in (-1:ℝ)..1, angularEnergy p eta) := by
    simp_rw [singularEnergy_polar p _ hrp]
    exact intervalIntegral.integral_const_mul _ _
  rw [hi,show 2*p-1=2*p-2+1 by ring,Real.rpow_add_one (by positivity : 2*r ≠ 0)]
  ring

lemma singular_radial_integral {p : ℝ} (hp : 0 < p) :
    (∫ r in (0:ℝ)..(1/2:ℝ), (2*r)^(2*p-1)) = 1/(4*p) := by
  have he := intervalIntegral.integral_comp_mul_left (a := (0:ℝ)) (b := (1/2:ℝ))
    (fun r : ℝ => r^(2*p-1)) (c := (2:ℝ)) (by norm_num)
  norm_num only [mul_zero,mul_one_div_cancel (by norm_num : (2:ℝ) ≠ 0),smul_eq_mul] at he
  rw [he,integral_rpow (Or.inl (by linarith : -1 < 2*p-1))]
  rw [show 2*p-1+1=2*p by ring,Real.one_rpow,Real.zero_rpow (by positivity : 2*p ≠ 0)]
  field_simp
  ring

lemma singularEnergy_integral {p : ℝ} (hp : 1 < p) :
    (∫ z in coneTriangle (1/2), singularEnergy p z) = (2*p^2+2*p+13)/(240*p) := by
  have hsub : coneTriangle (1/2) ⊆ coneTriangle 2 := fun z hz =>
    ⟨hz.1,hz.2.1.trans (by norm_num),hz.2.2⟩
  have heq : ∀ z : Plane, z ∈ coneTriangle (1/2) ↔
      z 1 ∈ Icc (0:ℝ) (1/2) ∧ z 0 ∈ Icc (-z 1) (z 1) := by
    intro z
    simp only [coneTriangle,mem_ofPred_eq,mem_Icc,← abs_le]
    tauto
  rw [plane_setIntegral_horizontal_interval (coneTriangle_isCompact (1/2)).measurableSet
    ((singularEnergy_integrable hp).mono_set hsub) (s := Icc (0:ℝ) (1/2))
    (l := fun r => -r) (u := id) measurableSet_Icc heq]
  have he : (∫ r in Icc (0:ℝ) (1/2), ∫ b in Icc (-r) r, singularEnergy p (vec2 b r)) =
      ∫ r in Icc (0:ℝ) (1/2), (2*r)^(2*p-1)/8*(∫ eta in (-1:ℝ)..1, angularEnergy p eta) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro r hr
    exact singularEnergy_slice_integral hp hr.1
  simp only [id_eq]
  rw [he,angularEnergy_integral p]
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1/2)]
  have hf : (fun r : ℝ => (2*r)^(2*p-1)/8*(2*(2*p^2+2*p+13)/15)) =
      fun r => (2*(2*p^2+2*p+13)/15/8)*(2*r)^(2*p-1) := by funext r; ring
  rw [hf,intervalIntegral.integral_const_mul,singular_radial_integral (by linarith : 0 < p)]
  field_simp
  ring

lemma singular_exact_coefficient {p : ℝ} (hp : 1 < p) :
    (∫ b in Icc (-(1/2:ℝ)) (1/2), ceilingPolynomial p b) -
      (∫ z in coneTriangle (1/2), singularEnergy p z)/2 = singularCoefficient p := by
  rw [ceilingPolynomial_integral,singularEnergy_integral hp]
  unfold singularCoefficient
  have hp0 : p ≠ 0 := by linarith
  field_simp
  ring

lemma energyCorrection_integrable {p : ℝ} (hp : 1 < p) (gamma c : ℝ) :
    IntegrableOn (energyCorrection p c) (singularDomain p gamma c) := by
  apply ((singularEnergy_integrable hp).mono_set (singularDomain_subset_cone p gamma c)).div_const 2 |>.mono'
    (energyCorrection_measurable p c).aestronglyMeasurable
  exact Filter.Eventually.of_forall (energyCorrection_norm p c)

lemma singular_weighted_integral_expansion {p : ℝ} (hp : 1 < p) (gamma c : ℝ) :
    (∫ z in singularDomain p gamma c, physicalWeight (Real.sqrt 2) (c • singularField p z)) =
      volume.real (singularDomain p gamma c)+c^2*(∫ z in singularDomain p gamma c, energyCorrection p c z) := by
  simp_rw [physicalWeight_energy_expansion]
  rw [integral_add (integrableOn_const (C := (1:ℝ)) (singularDomain_isCompact p gamma c).measure_lt_top.ne)
    ((energyCorrection_integrable hp gamma c).const_mul (c^2)),integral_const_mul]
  simp only [integral_const,smul_eq_mul,mul_one,measureReal_def,Measure.restrict_apply_univ]

end RuledApproximation

end

end OAI
