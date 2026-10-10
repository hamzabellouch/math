import OAI.MeasureTheory.Falconer.Fourier.DescriptorInverseJets

namespace OAI

/-! # Scale-normalized jets of the complex angular multiplier

The multiplier is treated as an additional label. Its new derivative
order is charged to the inverse, and its available smoothness budget is
reduced by exactly that order.
-/

namespace Falconer.MaskJetIndex
open Set
open scoped ContDiff
variable {d : ℕ}

theorem value_const_mul (j : MaskJetIndex d) (c : ℂ) (f : Space d → ℂ)
    (hf : ContDiff ℝ ∞ f) (z : Space d) :
    j.value (fun w => c*f w) z = c*j.value f z := by
  change (iteratedFDeriv ℝ j.order (fun w => c • f w) z) j.vectors = _
  rw [iteratedFDeriv_const_smul_apply' (hf.of_le (by simp)).contDiffAt]
  rfl

theorem value_real_smul (j : MaskJetIndex d) (c : ℝ) (f : Space d → ℂ)
    (hf : ContDiff ℝ ∞ f) (z : Space d) :
    j.value (fun w => c • f w) z = c • j.value f z := by
  simp only [Complex.real_smul]
  exact j.value_const_mul c f hf z

noncomputable def scaledValue (j : MaskJetIndex d) (r : ℝ)
    (f : Space d → ℂ) (z : Space d) : ℂ :=
  r^j.order • j.value f z

theorem scaledValue_contDiff (j : MaskJetIndex d) (r : ℝ)
    (f : Space d → ℂ) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (j.scaledValue r f) :=
  (show ContDiff ℝ ∞ (fun z => r^j.order • j.value f z) from
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Space d => r^j.order)).smul
      (j.value_contDiff hf))

theorem scaledValue_ofReal (j : MaskJetIndex d) (r : ℝ)
    (f : Space d → ℝ) (hf : ContDiff ℝ ∞ f) (z : Space d) :
    j.scaledValue r (fun w => (f w : ℂ)) z = j.normalizedValue r f z := by
  rw [scaledValue,value_ofReal j f hf z]
  simp only [normalizedValue,Complex.real_smul,Complex.ofReal_mul]

theorem value_eq_inv_radius_scaled (j : MaskJetIndex d) (r : ℝ) (hr : r ≠ 0)
    (f : Space d → ℂ) (z : Space d) :
    j.value f z = (((r⁻¹)^j.order : ℝ) : ℂ) * j.scaledValue r f z := by
  simp only [scaledValue,Complex.real_smul,← mul_assoc,← Complex.ofReal_mul,← mul_pow,
    inv_mul_cancel₀ hr,one_pow,Complex.ofReal_one,one_mul]

private theorem norm_iteratedFDeriv_nested (f : Space d → ℂ)
    (k t : ℕ) (z : Space d) :
    ‖iteratedFDeriv ℝ t (iteratedFDeriv ℝ k f) z‖ =
      ‖iteratedFDeriv ℝ (k+t) f z‖ := by
  induction t generalizing k with
  | zero => simp
  | succ t ih =>
    rw [← norm_iteratedFDeriv_fderiv,fderiv_iteratedFDeriv,
      LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,ih]
    rw [show k+1+t = k+(t+1) by omega]

private noncomputable def jetEvaluation (j : MaskJetIndex d) :
    (ContinuousMultilinearMap ℝ (fun _ : Fin j.order => Space d) ℂ) →L[ℝ] ℂ where
  toFun L := L j.vectors
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_eval_const j.vectors

private theorem jetEvaluation_norm_le (j : MaskJetIndex d) : ‖jetEvaluation j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro L
  change ‖L j.vectors‖ ≤ 1*‖L‖
  have hp : (∏ i, ‖j.vectors i‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => j.norm_vectors i)
  simpa only [one_mul] using (L.le_opNorm j.vectors).trans
    (mul_le_of_le_one_right (norm_nonneg L) hp)

theorem norm_iteratedFDeriv_value_le (j : MaskJetIndex d) (f : Space d → ℂ)
    (hf : ContDiff ℝ ∞ f) (t : ℕ) (z : Space d) :
    ‖iteratedFDeriv ℝ t (j.value f) z‖ ≤ ‖iteratedFDeriv ℝ (j.order+t) f z‖ := by
  have hfd : ContDiff ℝ ∞ (iteratedFDeriv ℝ j.order f) :=
    hf.iteratedFDeriv_right (by simp)
  change ‖iteratedFDeriv ℝ t (jetEvaluation j ∘ iteratedFDeriv ℝ j.order f) z‖ ≤ _
  rw [(jetEvaluation j).iteratedFDeriv_comp_left hfd.contDiffAt (by simp)]
  calc
    _ ≤ ‖jetEvaluation j‖ * ‖iteratedFDeriv ℝ t (iteratedFDeriv ℝ j.order f) z‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ t (iteratedFDeriv ℝ j.order f) z‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (jetEvaluation_norm_le j)
    _ = _ := norm_iteratedFDeriv_nested f j.order t z

theorem norm_iteratedFDeriv_scaledValue_le (j : MaskJetIndex d) {r : ℝ} (hr : 0 ≤ r)
    (f : Space d → ℂ) (hf : ContDiff ℝ ∞ f) (t : ℕ) (z : Space d) :
    ‖iteratedFDeriv ℝ t (j.scaledValue r f) z‖ ≤
      r^j.order * ‖iteratedFDeriv ℝ (j.order+t) f z‖ := by
  change ‖iteratedFDeriv ℝ t (fun z => r^j.order • j.value f z) z‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' ((j.value_contDiff hf).of_le (by simp)).contDiffAt,
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hr _)]
  exact mul_le_mul_of_nonneg_left (j.norm_iteratedFDeriv_value_le f hf t z) (pow_nonneg hr _)

theorem angular_budget_shift (j : MaskJetIndex d) (f : Space d → ℂ)
    (hf : ContDiff ℝ ∞ f) {D : ℝ} (hD : 1 ≤ D) {L : ℕ} (hj : j.order ≤ L)
    (hbudget : ∀ k ≤ L, ∀ w : Sphere d, ‖iteratedFDeriv ℝ k f w‖ ≤ D^k) :
    ∀ t ≤ L-j.order, ∀ w : Sphere d,
      ‖iteratedFDeriv ℝ t (j.scaledValue D⁻¹ f) w‖ ≤ D^t := by
  intro t ht w
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  calc
    _ ≤ (D⁻¹)^j.order * ‖iteratedFDeriv ℝ (j.order+t) f w‖ :=
      j.norm_iteratedFDeriv_scaledValue_le (inv_nonneg.mpr hD0.le) f hf t w
    _ ≤ (D⁻¹)^j.order * D^(j.order+t) :=
      mul_le_mul_of_nonneg_left (hbudget _ (by omega) w) (pow_nonneg (inv_nonneg.mpr hD0.le) _)
    _ = D^t := by
      rw [pow_add,← mul_assoc,← mul_pow,inv_mul_cancel₀ hD0.ne',one_pow,one_mul]

end Falconer.MaskJetIndex

end OAI
