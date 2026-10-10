import OAI.Probability.PosteriorReplicas.Gaussian.GaussianGramMoment

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace PosteriorReplicas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma log_le_square_tangent {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    Real.log x ≤ Real.log a / 2 + x^2/(2*a) - 1/2 := by
  have h := Real.log_le_sub_one_of_pos (div_pos (sq_pos_of_pos hx) ha)
  rw [Real.log_div (ne_of_gt (sq_pos_of_pos hx)) ha.ne', Real.log_pow] at h
  norm_num at h
  nlinarith [show x^2/a = 2*(x^2/(2*a)) by field_simp]

omit [MeasurableSpace E] [BorelSpace E] in
lemma norm_gramSchmidt_le_norm [MeasurableSpace E] [BorelSpace E]
    {m : ℕ} (v : Fin m → E) (i : Fin m) :
    ‖gramSchmidt ℝ v i‖ ≤ ‖v i‖ := by
  rw [PosteriorRegression.gramSchmidt_eq_sub_starProjection,
    ← Submodule.starProjection_orthogonal_val]
  exact Submodule.norm_starProjection_apply_le _ _

def gramVolume {m : ℕ} (v : Fin m → E) : ℝ := Real.sqrt (Matrix.gram ℝ v).det

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gramVolume_eq_prod [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {m : ℕ} (v : Fin m → E) :
    gramVolume v = ∏ i, ‖gramSchmidt ℝ v i‖ := PosteriorRegression.sqrt_det_gram m v

@[fun_prop] lemma measurable_gramVolume {m : ℕ} : Measurable (gramVolume : (Fin m → E) → ℝ) := by
  change Measurable (fun v : Fin m → E => gramVolume v)
  simp_rw [gramVolume_eq_prod]
  exact Finset.measurable_prod _ (fun i _ => (PosteriorRegression.measurable_gramSchmidt i).norm)

lemma gramVolume_pos {m : ℕ} {v : Fin m → E} (hv : LinearIndependent ℝ v) :
    0 < gramVolume v := by
  rw [gramVolume_eq_prod]
  exact Finset.prod_pos fun i _ => norm_pos_iff.mpr (gramSchmidt_ne_zero i hv)

lemma log_gramVolume_eq_sum {m : ℕ} {v : Fin m → E} (hv : LinearIndependent ℝ v) :
    Real.log (gramVolume v) = ∑ i, Real.log ‖gramSchmidt ℝ v i‖ := by
  rw [gramVolume_eq_prod, Real.log_prod (fun i _ => norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i hv))]

lemma log_gramVolume_le_tangent {m : ℕ} {v : Fin m → E} (hv : LinearIndependent ℝ v)
    {a : ℝ} (ha : 0 < a) :
    Real.log (gramVolume v) ≤ ∑ i, (Real.log a/2 + ‖v i‖^2/(2*a) - 1/2) := by
  rw [log_gramVolume_eq_sum hv]
  apply Finset.sum_le_sum
  intro i _
  apply (log_le_square_tangent (norm_pos_iff.mpr (gramSchmidt_ne_zero i hv)) ha).trans
  have h := norm_gramSchmidt_le_norm v i
  have hsq : ‖gramSchmidt ℝ v i‖^2 ≤ ‖v i‖^2 := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr h
  exact sub_le_sub_right (add_le_add le_rfl (div_le_div_of_nonneg_right hsq (by positivity))) _

lemma abs_log_gramVolume_le {m : ℕ} {v : Fin m → E} (hv : LinearIndependent ℝ v) :
    |Real.log (gramVolume v)| ≤ (gramVolume v)⁻¹ + ∑ i, (‖v i‖^2+1) := by
  have hp := gramVolume_pos hv
  have hneg := Real.log_le_self (inv_pos.mpr hp).le
  rw [Real.log_inv] at hneg
  have hu := log_gramVolume_le_tangent hv (a := 1) (by norm_num)
  have hs : (∑ i, (Real.log (1:ℝ)/2+‖v i‖^2/(2*1)-1/2)) ≤ ∑ i, (‖v i‖^2+1) := by
    apply Finset.sum_le_sum
    intro i _
    simp only [Real.log_one, zero_div, zero_add, mul_one]
    nlinarith [sq_nonneg ‖v i‖]
  have hn : 0 ≤ ∑ i, (‖v i‖^2+1) := Finset.sum_nonneg (fun i _ => by positivity)
  exact abs_le.mpr ⟨by linarith, by linarith [inv_nonneg.mpr hp.le]⟩

lemma gaussian_integrable_norm_sq : Integrable (fun x : E => ‖x‖^2) (stdGaussian E) :=
  (IsGaussian.memLp_two_id (μ := stdGaussian E)).norm.integrable_sq

lemma gaussian_integral_norm_sq : (∫ x : E, ‖x‖^2 ∂stdGaussian E) = Module.finrank ℝ E := by
  let b := stdOrthonormalBasis ℝ E
  have hL (i : Fin (Module.finrank ℝ E)) :
      (∫ x : E, ⟪b i,x⟫^2 ∂stdGaussian E) = 1 := by
    have h := variance_eq_integral (μ := stdGaussian E)
      (X := fun x : E => ⟪b i,x⟫) (by fun_prop)
    have hmean : (∫ x : E, ⟪b i,x⟫ ∂stdGaussian E) = 0 :=
      integral_strongDual_stdGaussian (innerSL ℝ (b i))
    rw [hmean] at h
    simp only [sub_zero] at h
    rw [← h]
    change Var[⇑(innerSL ℝ (b i)); stdGaussian E] = 1
    rw [variance_dual_stdGaussian]
    simp [b.norm_eq_one]
  have hi (i : Fin (Module.finrank ℝ E)) :
      Integrable (fun x : E => ⟪b i,x⟫^2) (stdGaussian E) := by
    apply gaussian_integrable_norm_sq.mono' (by fun_prop)
    apply ae_of_all
    intro x
    have h := abs_real_inner_le_norm (b i) x
    rw [b.norm_eq_one, one_mul] at h
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg ⟪b i,x⟫) (norm_nonneg x)).mpr h
  simp_rw [← b.sum_sq_inner_right]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp only [hL, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

lemma gaussianPi_integrable_norm_sq {m : ℕ} (i : Fin m) :
    Integrable (fun v : Fin m → E => ‖v i‖^2) (Measure.pi fun _ => stdGaussian E) := by
  exact (measurePreserving_eval (fun _ : Fin m => stdGaussian E) i).integrable_comp
    gaussian_integrable_norm_sq.aestronglyMeasurable |>.mpr gaussian_integrable_norm_sq

lemma gaussianPi_integral_norm_sq {m : ℕ} (i : Fin m) :
    (∫ v : Fin m → E, ‖v i‖^2 ∂Measure.pi (fun _ => stdGaussian E)) = Module.finrank ℝ E := by
  have h := (measurePreserving_eval (fun _ : Fin m => stdGaussian E) i).map_eq
  have he := integral_map (μ := Measure.pi (fun _ : Fin m => stdGaussian E))
    (φ := Function.eval i) (f := fun x : E => ‖x‖^2)
    (measurable_pi_apply i).aemeasurable (by fun_prop)
  rw [h, gaussian_integral_norm_sq] at he
  exact he.symm

lemma gaussian_integrable_inv_gramVolume {m : ℕ} (hm : m+1 ≤ Module.finrank ℝ E) :
    Integrable (fun v : Fin m → E => (gramVolume v)⁻¹)
      (Measure.pi fun _ => stdGaussian E) := by
  refine ⟨(measurable_gramVolume.inv).aestronglyMeasurable, ?_⟩
  have hn : 0 ≤ᵐ[Measure.pi (fun _ : Fin m => stdGaussian E)]
      (fun v => (gramVolume v)⁻¹) := ae_of_all _ (fun v =>
    inv_nonneg.mpr (Real.sqrt_nonneg _))
  apply (hasFiniteIntegral_iff_ofReal hn).mpr
  have h := gaussian_gram_inverse_moment_centered (E := E) 1 m (by omega) (by omega)
  simp only [pow_one] at h
  exact h.trans_lt (lt_top_iff_ne_top.mpr (ENNReal.pow_ne_top (gaussianMomentConstant_ne_top 1)))

lemma gaussian_integrable_log_gramVolume {m : ℕ} (hm : m+1 ≤ Module.finrank ℝ E) :
    Integrable (fun v : Fin m → E => Real.log (gramVolume v))
      (Measure.pi fun _ => stdGaussian E) := by
  have hb : Integrable (fun v : Fin m → E => (gramVolume v)⁻¹ + ∑ i, (‖v i‖^2+1))
      (Measure.pi fun _ => stdGaussian E) :=
    (gaussian_integrable_inv_gramVolume hm).add
      (integrable_finsetSum _ (fun i _ => (gaussianPi_integrable_norm_sq i).add (integrable_const 1)))
  refine hb.mono' (measurable_gramVolume.log.aestronglyMeasurable) ?_
  filter_upwards [ae_gaussian_columns_independent (E := E) m (by omega)] with v hv
  exact abs_log_gramVolume_le hv

lemma gaussian_integral_log_gramVolume_le {m : ℕ} (hm : m+1 ≤ Module.finrank ℝ E) :
    (∫ v : Fin m → E, Real.log (gramVolume v) ∂Measure.pi (fun _ => stdGaussian E)) ≤
      (m : ℝ)/2 * Real.log ((Module.finrank ℝ E : ℝ)+1) := by
  let a : ℝ := (Module.finrank ℝ E : ℝ)+1
  have ha : 0 < a := by dsimp [a]; positivity
  have hi (i : Fin m) : Integrable (fun v : Fin m → E => Real.log a/2 + ‖v i‖^2/(2*a)-1/2)
      (Measure.pi fun _ => stdGaussian E) :=
    ((integrable_const _).add ((gaussianPi_integrable_norm_sq i).div_const _)).sub (integrable_const _)
  calc
    _ ≤ ∫ v : Fin m → E, ∑ i, (Real.log a/2+‖v i‖^2/(2*a)-1/2)
        ∂Measure.pi (fun _ => stdGaussian E) := by
      apply integral_mono_ae (gaussian_integrable_log_gramVolume hm) (integrable_finsetSum _ (fun i _ => hi i))
      filter_upwards [ae_gaussian_columns_independent (E := E) m (by omega)] with v hv
      exact log_gramVolume_le_tangent hv ha
    _ = ∑ _i : Fin m, (Real.log a/2 + (Module.finrank ℝ E : ℝ)/(2*a)-1/2) := by
      rw [integral_finsetSum _ (fun i _ => hi i)]
      apply Finset.sum_congr rfl
      intro i _
      have hid : Integrable (fun v : Fin m → E => ‖v i‖^2/(2*a))
          (Measure.pi fun _ => stdGaussian E) := (gaussianPi_integrable_norm_sq i).div_const _
      have hic : Integrable (fun _ : Fin m → E => Real.log a/2)
          (Measure.pi fun _ => stdGaussian E) := integrable_const _
      have hia : Integrable (fun v : Fin m → E => Real.log a/2 + ‖v i‖^2/(2*a))
          (Measure.pi fun _ => stdGaussian E) := hic.add hid
      rw [integral_sub hia (integrable_const (1/2 : ℝ)),
        integral_add hic hid]
      simp only [integral_div, gaussianPi_integral_norm_sq, integral_const, probReal_univ, one_smul]
    _ ≤ _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hdiv : (Module.finrank ℝ E : ℝ)/(2*a) ≤ 1/2 := by
        apply (div_le_iff₀ (by positivity : 0 < 2*a)).mpr
        dsimp [a]
        linarith
      dsimp [a]
      nlinarith [Nat.cast_nonneg (α := ℝ) m]

end PosteriorReplicas
end

end OAI
