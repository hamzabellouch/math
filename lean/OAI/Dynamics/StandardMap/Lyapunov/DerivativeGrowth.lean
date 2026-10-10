import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Lyapunov.Subadditive
import OAI.Dynamics.StandardMap.Lyapunov.Definitions

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

@[simp] lemma tangentCoordinates_re (z : ℂ) : (tangentCoordinates z).re = z.re := rfl
@[simp] lemma tangentCoordinates_im (z : ℂ) : (tangentCoordinates z).im = z.re-z.im := rfl
@[simp] lemma tangentCoordinates_involutive (z : ℂ) :
    tangentCoordinates (tangentCoordinates z) = z := by
  apply Complex.ext <;> simp

lemma tangentCoordinates_wedge (z w : ℂ) :
    wedge (tangentCoordinates z) (tangentCoordinates w) = -wedge z w := by
  simp only [wedge, tangentCoordinates_re, tangentCoordinates_im]
  ring

lemma tangentCoordinates_norm_le : ‖tangentCoordinates‖ ≤ 3 := by
  apply tangentCoordinates.opNorm_le_bound (by norm_num)
  intro z
  have hr := Complex.abs_re_le_norm z
  have hi := Complex.abs_im_le_norm z
  calc
    ‖tangentCoordinates z‖ ≤ |z.re| + |z.re-z.im| := by
      simpa only [tangentCoordinates_re, tangentCoordinates_im]
        using Complex.norm_le_abs_re_add_abs_im (tangentCoordinates z)
    _ ≤ |z.re| + (|z.re|+|z.im|) := add_le_add le_rfl (abs_sub _ _)
    _ ≤ 3*‖z‖ := by linarith

@[simp] lemma standardDerivative_re (k : ℝ) (z : Torus) (v : ℂ) :
    (standardDerivative k z v).re = (torusPotential k z.1-1)*v.re+v.im := by
  simp only [standardDerivative, ContinuousLinearMap.comp_apply,
    tangentCoordinates_re, tangentCoordinates_im, transferStep_re]
  ring
@[simp] lemma standardDerivative_im (k : ℝ) (z : Torus) (v : ℂ) :
    (standardDerivative k z v).im = (torusPotential k z.1-2)*v.re+v.im := by
  simp only [standardDerivative, ContinuousLinearMap.comp_apply,
    tangentCoordinates_re, tangentCoordinates_im, transferStep_re, transferStep_im]
  ring

lemma standardDerivative_area (k : ℝ) (z : Torus) :
    PlaneAreaPreserving (standardDerivative k z) := by
  intro v w
  simp only [standardDerivative, ContinuousLinearMap.comp_apply, tangentCoordinates_wedge]
  rw [transferStep_area _ _ _, tangentCoordinates_wedge, neg_neg]

lemma standardInverseDerivative_area (k : ℝ) (z : Torus) :
    PlaneAreaPreserving (standardInverseDerivative k z) := by
  intro v w
  simp only [standardInverseDerivative, ContinuousLinearMap.comp_apply, tangentCoordinates_wedge]
  rw [transferStepInv_area _ _ _, tangentCoordinates_wedge, neg_neg]

lemma standardDerivativeProduct_area (k : ℝ) (z : Torus) (n : ℕ) :
    PlaneAreaPreserving (standardDerivativeProduct k z n) := by
  induction n with
  | zero => intro v w; rfl
  | succ n ih => exact (standardDerivative_area k _).comp ih

lemma standardDerivative_norm_ge_one (k : ℝ) (z : Torus) : 1 ≤ ‖standardDerivative k z‖ :=
  (standardDerivative_area k z).singular_pair.choose_spec.2.2.2.2
lemma standardInverseDerivative_norm_ge_one (k : ℝ) (z : Torus) :
    1 ≤ ‖standardInverseDerivative k z‖ :=
  (standardInverseDerivative_area k z).singular_pair.choose_spec.2.2.2.2
lemma standardDerivativeProduct_norm_ge_one (k : ℝ) (z : Torus) (n : ℕ) :
    1 ≤ ‖standardDerivativeProduct k z n‖ :=
  (standardDerivativeProduct_area k z n).singular_pair.choose_spec.2.2.2.2

lemma complexProjection_standardLift (k : ℝ) (z : ℂ) :
    complexProjection (standardLift k z) = standardMap k (complexProjection z) := by
  ext <;> simp [complexProjection, standardLift, standardMap]
lemma complexProjection_standardInverseLift (k : ℝ) (z : ℂ) :
    complexProjection (standardInverseLift k z) = inverseMap k (complexProjection z) := by
  ext <;> simp [complexProjection, standardInverseLift, inverseMap, kick,
    ← QuotientAddGroup.mk_sub]

lemma standardLift_inverse (k : ℝ) (z : ℂ) :
    standardLift k (standardInverseLift k z) = z := by
  apply Complex.ext <;> simp [standardLift, standardInverseLift]
lemma standardInverseLift_inverse (k : ℝ) (z : ℂ) :
    standardInverseLift k (standardLift k z) = z := by
  apply Complex.ext <;> simp [standardLift, standardInverseLift]

lemma continuous_transferStepInv : Continuous transferStepInv := by
  have he : transferStepInv = fun v =>
      (transferStepInv 0).comp ((transferStep (-v)).comp (transferStepInv 0)) := by
    funext v
    apply ContinuousLinearMap.ext
    intro z
    apply Complex.ext <;> simp; ring
  rw [he]
  exact continuous_const.clm_comp ((continuous_transferStep.comp continuous_neg).clm_comp continuous_const)

lemma continuous_standardDerivative (k : ℝ) : Continuous (standardDerivative k) :=
  continuous_const.clm_comp
    ((continuous_transferStep.comp ((continuous_torusPotential k).comp continuous_fst)).clm_comp
      continuous_const)

lemma continuous_inverseMap (k : ℝ) : Continuous (inverseMap k) :=
  (continuous_fst.sub continuous_snd).prodMk
    (continuous_snd.sub ((continuous_kick k).comp (continuous_fst.sub continuous_snd)))

lemma continuous_standardInverseDerivative (k : ℝ) : Continuous (standardInverseDerivative k) :=
  continuous_const.clm_comp
    ((continuous_transferStepInv.comp ((continuous_torusPotential k).comp
      (continuous_fst.comp (continuous_inverseMap k)))).clm_comp continuous_const)

lemma integrable_log_standardDerivative (k : ℝ) :
    Integrable (fun z => Real.log ‖standardDerivative k z‖) area :=
  ((continuous_standardDerivative k).norm.log (fun z =>
    ne_of_gt (lt_of_lt_of_le zero_lt_one (standardDerivative_norm_ge_one k z)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
lemma integrable_log_standardInverseDerivative (k : ℝ) :
    Integrable (fun z => Real.log ‖standardInverseDerivative k z‖) area :=
  ((continuous_standardInverseDerivative k).norm.log (fun z =>
    ne_of_gt (lt_of_lt_of_le zero_lt_one (standardInverseDerivative_norm_ge_one k z)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma recurrenceCoordinates_iterate (k : ℝ) (n : ℕ) (z : Torus) :
    recurrenceCoordinates ((standardMap k)^[n] z) =
      (torusStep k)^[n] (recurrenceCoordinates z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', standardMap_conjugacy, ih]
    rfl

lemma standardDerivativeProduct_conjugate (k : ℝ) (z : Torus) (n : ℕ) :
    standardDerivativeProduct k z n = tangentCoordinates.comp
      ((torusSegmentTransfer k (recurrenceCoordinates z) 0 n).comp tangentCoordinates) := by
  induction n with
  | zero =>
    apply ContinuousLinearMap.ext
    intro w
    simpa only [standardDerivativeProduct_zero, torusSegmentTransfer, transferProduct,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      (tangentCoordinates_involutive w).symm
  | succ n ih =>
    have hcoeff : torusSegmentCoefficient k (recurrenceCoordinates z) 0 (n+1) =
        torusPotential k ((standardMap k)^[n] z).1 := by
      unfold torusSegmentCoefficient
      simp only [Nat.cast_add, Nat.cast_one, zero_add, add_sub_cancel_right]
      rw [torusIter_nat_apply, ← recurrenceCoordinates_iterate]
      rfl
    apply ContinuousLinearMap.ext
    intro w
    simp only [standardDerivativeProduct_succ, ih, standardDerivative, torusSegmentTransfer,
      transferProduct, ContinuousLinearMap.comp_apply, tangentCoordinates_involutive, hcoeff]

lemma conjugate_norm_le (A : ℂ →L[ℝ] ℂ) :
    ‖tangentCoordinates.comp (A.comp tangentCoordinates)‖ ≤ 9*‖A‖ := by
  calc
    _ ≤ ‖tangentCoordinates‖ * (‖A‖ * ‖tangentCoordinates‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 3 * (‖A‖ * 3) := by gcongr <;> exact tangentCoordinates_norm_le
    _ = _ := by ring

lemma conjugate_norm_lower (A : ℂ →L[ℝ] ℂ) :
    ‖A‖ ≤ 9*‖tangentCoordinates.comp (A.comp tangentCoordinates)‖ := by
  convert conjugate_norm_le (tangentCoordinates.comp (A.comp tangentCoordinates)) using 1
  congr 1
  apply ContinuousLinearMap.ext
  intro z
  simp only [ContinuousLinearMap.comp_apply, tangentCoordinates_involutive]

lemma derivative_log_difference_bound (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) :
    |Real.log ‖standardDerivativeProduct k z n‖-
      Real.log ‖torusSegmentTransfer k (recurrenceCoordinates z) 0 n‖| ≤ Real.log 9 := by
  have hA : 0 < ‖torusSegmentTransfer k (recurrenceCoordinates z) 0 n‖ :=
    lt_of_lt_of_le zero_lt_one (torusSegmentTransfer_norm_bounds k hk _ _ _).1
  have hB : 0 < ‖standardDerivativeProduct k z n‖ :=
    lt_of_lt_of_le zero_lt_one (standardDerivativeProduct_norm_ge_one k z n)
  have h₁ := conjugate_norm_le (torusSegmentTransfer k (recurrenceCoordinates z) 0 n)
  have h₂ := conjugate_norm_lower (torusSegmentTransfer k (recurrenceCoordinates z) 0 n)
  rw [← standardDerivativeProduct_conjugate] at h₁ h₂
  have hlog₁ := Real.log_le_log hB h₁
  have hlog₂ := Real.log_le_log hA h₂
  rw [Real.log_mul (by norm_num) hA.ne'] at hlog₁
  rw [Real.log_mul (by norm_num) hB.ne'] at hlog₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end StandardMapEntropy

namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

lemma contDiff_standardLift (k : ℝ) : ContDiff ℝ ∞ (standardLift k) := by
  have hr : ContDiff ℝ ∞ (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have hi : ContDiff ℝ ∞ (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  have hs : ContDiff ℝ ∞ (fun z : ℂ => k*Real.sin (2*Real.pi*z.re)) :=
    contDiff_const.mul (contDiff_const.mul hr).sin
  exact Complex.equivRealProdCLM.symm.toContinuousLinearMap.contDiff.comp
    (((hr.add hi).add hs).prodMk (hi.add hs))

lemma contDiff_standardInverseLift (k : ℝ) : ContDiff ℝ ∞ (standardInverseLift k) := by
  have hr : ContDiff ℝ ∞ (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have hi : ContDiff ℝ ∞ (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  have hs : ContDiff ℝ ∞ (fun z : ℂ => k*Real.sin (2*Real.pi*(z.re-z.im))) :=
    contDiff_const.mul (contDiff_const.mul (hr.sub hi)).sin
  exact Complex.equivRealProdCLM.symm.toContinuousLinearMap.contDiff.comp
    ((hr.sub hi).prodMk (hi.sub hs))

@[simp] lemma complexPair_re (p : ℝ × ℝ) : (Complex.equivRealProdCLM.symm p).re = p.1 := rfl
@[simp] lemma complexPair_im (p : ℝ × ℝ) : (Complex.equivRealProdCLM.symm p).im = p.2 := rfl

lemma hasFDerivAt_standardLift (k : ℝ) (z : ℂ) :
    HasFDerivAt (standardLift k) (standardDerivative k (complexProjection z)) z := by
  have hr := Complex.reCLM.hasFDerivAt (x := z)
  have hi := Complex.imCLM.hasFDerivAt (x := z)
  have hs := ((hr.const_mul (2*Real.pi)).sin).const_mul k
  have hh := Complex.equivRealProdCLM.symm.toContinuousLinearMap.hasFDerivAt.comp z
    (((hr.add hi).add hs).prodMk (hi.add hs))
  convert! hh using 1; try rfl
  apply ContinuousLinearMap.ext
  intro w
  apply Complex.ext <;> simp [standardDerivative_re, standardDerivative_im, complexProjection,
    torusPotential, cosine_coe] <;> ring

lemma hasFDerivAt_standardInverseLift (k : ℝ) (z : ℂ) :
    HasFDerivAt (standardInverseLift k) (standardInverseDerivative k (complexProjection z)) z := by
  have hr := Complex.reCLM.hasFDerivAt (x := z)
  have hi := Complex.imCLM.hasFDerivAt (x := z)
  have hs := ((((hr.sub hi).const_mul (2*Real.pi)).sin).const_mul k)
  have hh := Complex.equivRealProdCLM.symm.toContinuousLinearMap.hasFDerivAt.comp z
    ((hr.sub hi).prodMk (hi.sub hs))
  convert! hh using 1; try rfl
  apply ContinuousLinearMap.ext
  intro w
  apply Complex.ext <;> simp [standardInverseDerivative, tangentCoordinates_re,
    tangentCoordinates_im, complexProjection, inverseMap, torusPotential,
    ← QuotientAddGroup.mk_sub, cosine_coe]; ring

theorem actual_derivative_certificate (k : ℝ) :
    (∀ z : ℂ, complexProjection (standardLift k z) = standardMap k (complexProjection z)) ∧
    (∀ z : ℂ, complexProjection (standardInverseLift k z) = inverseMap k (complexProjection z)) ∧
    ContDiff ℝ ∞ (standardLift k) ∧ ContDiff ℝ ∞ (standardInverseLift k) ∧
    (∀ z : ℂ, HasFDerivAt (standardLift k) (standardDerivative k (complexProjection z)) z) ∧
    (∀ z : ℂ, HasFDerivAt (standardInverseLift k)
      (standardInverseDerivative k (complexProjection z)) z) ∧
    Integrable (fun z => Real.log ‖standardDerivative k z‖) area ∧
    Integrable (fun z => Real.log ‖standardInverseDerivative k z‖) area :=
  ⟨complexProjection_standardLift k, complexProjection_standardInverseLift k,
    contDiff_standardLift k, contDiff_standardInverseLift k, hasFDerivAt_standardLift k,
    hasFDerivAt_standardInverseLift k, integrable_log_standardDerivative k,
    integrable_log_standardInverseDerivative k⟩

lemma complexProjection_iterate (k : ℝ) (n : ℕ) (z : ℂ) :
    complexProjection ((standardLift k)^[n] z) = (standardMap k)^[n] (complexProjection z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', complexProjection_standardLift, ih]

lemma hasFDerivAt_standardLift_iterate (k : ℝ) (n : ℕ) (z : ℂ) :
    HasFDerivAt ((standardLift k)^[n])
      (standardDerivativeProduct k (complexProjection z) n) z := by
  induction n with
  | zero => exact hasFDerivAt_id z
  | succ n ih =>
    have hh := (hasFDerivAt_standardLift k ((standardLift k)^[n] z)).comp z ih
    simpa only [complexProjection_iterate, ← Function.iterate_succ', standardDerivativeProduct] using hh

lemma derivative_rate_of_transfer_rate (k : ℝ) (hk : 0 ≤ k) (z : Torus) (l : ℝ)
    (hl : Tendsto
      (fun n : ℕ => Real.log ‖torusSegmentTransfer k (recurrenceCoordinates z) 0 n‖ / (n : ℝ))
      atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => Real.log ‖standardDerivativeProduct k z n‖ / (n : ℝ))
      atTop (𝓝 l) := by
  have hd : Tendsto (fun n : ℕ =>
      (Real.log ‖standardDerivativeProduct k z n‖ -
        Real.log ‖torusSegmentTransfer k (recurrenceCoordinates z) 0 n‖) / (n : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_)
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => Real.log 9 / (n : ℝ)) atTop (𝓝 0))
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (derivative_log_difference_bound k hk z n) (Nat.cast_nonneg _)
  have hh := hd.add hl
  simpa only [sub_div, sub_add_cancel, zero_add] using hh

noncomputable def standardLyapunov (k : ℝ) (hk : 0 ≤ k) (z : Torus) : ℝ :=
  transferLyapunov k hk (recurrenceCoordinates z)

lemma measurable_recurrenceCoordinates : Measurable recurrenceCoordinates :=
  measurable_fst.prodMk (measurable_fst.sub measurable_snd)

lemma measurable_standardLyapunov (k : ℝ) (hk : 0 ≤ k) :
    Measurable (standardLyapunov k hk) :=
  (transferLyapunov_limit k hk).1.comp measurable_recurrenceCoordinates

lemma integrable_standardLyapunov (k : ℝ) (hk : 0 ≤ k) :
    Integrable (standardLyapunov k hk) area :=
  measurePreserving_recurrenceCoordinates.integrable_comp_of_integrable
    (transferLyapunov_limit k hk).2.1

lemma standardLyapunov_nonneg (k : ℝ) (hk : 0 ≤ k) (z : Torus) :
    0 ≤ standardLyapunov k hk z := (transferLyapunov_limit k hk).2.2.1 _

lemma standardLyapunov_invariant (k : ℝ) (hk : 0 ≤ k) (z : Torus) :
    standardLyapunov k hk (standardMap k z) = standardLyapunov k hk z := by
  unfold standardLyapunov
  rw [standardMap_conjugacy]
  exact (transferLyapunov_limit k hk).2.2.2.1 _

lemma ae_standardLyapunov_rate (k : ℝ) (hk : 0 ≤ k) :
    ∀ᵐ z ∂area, Tendsto
      (fun n : ℕ => Real.log ‖standardDerivativeProduct k z n‖ / (n : ℝ))
      atTop (𝓝 (standardLyapunov k hk z)) := by
  have hh := measurePreserving_recurrenceCoordinates.quasiMeasurePreserving.ae
    (transferLyapunov_limit k hk).2.2.2.2
  filter_upwards [hh] with z hz
  exact derivative_rate_of_transfer_rate k hk z _ hz

lemma positive_standardLyapunov_of_deficit (k : ℝ) (hk : 0 ≤ k)
    (hdef : ∀ n : ℕ, 0 < n → meanDeficit k n < (1/8 : ℝ)) :
    0 < area {z | 0 < standardLyapunov k hk z} := by
  have hm : MeasurableSet {z | 0 < transferLyapunov k hk z} :=
    measurableSet_lt measurable_const (transferLyapunov_limit k hk).1
  have he := measurePreserving_recurrenceCoordinates.measure_preimage hm.nullMeasurableSet
  change 0 < area (recurrenceCoordinates ⁻¹' {z | 0 < transferLyapunov k hk z})
  rw [he]
  exact positive_transferLyapunov_of_deficit k hk hdef

end StandardMapEntropy

namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma standardDerivative_norm_bound (k : ℝ) (hk : 0 ≤ k) (z : Torus) :
    ‖standardDerivative k z‖ ≤ 9*growthBase k := by
  calc
    _ ≤ 9*‖transferStep (torusPotential k z.1)‖ := conjugate_norm_le _
    _ ≤ 9*(|torusPotential k z.1|+1) :=
      mul_le_mul_of_nonneg_left (transferStep_norm _) (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left (torusPotential_bound k hk z.1) (by norm_num)

lemma standardDerivativeProduct_step_lower (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) (v : ℂ) :
    ‖standardDerivativeProduct k z n v‖ ≤
      (9*growthBase k)*‖standardDerivativeProduct k z (n+1) v‖ := by
  exact ((standardDerivative_area k ((standardMap k)^[n] z)).norm_lower
    (standardDerivativeProduct k z n v)).trans
    (mul_le_mul_of_nonneg_right (standardDerivative_norm_bound k hk _) (norm_nonneg _))

end StandardMapEntropy
end
end

end OAI
