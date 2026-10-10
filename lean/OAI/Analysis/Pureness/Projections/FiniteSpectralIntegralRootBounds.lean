import OAI.Analysis.Pureness.Operators.FiniteDimensionPowers
import OAI.Analysis.Pureness.Projections.FiniteSpectralIntegralBounds

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
variable {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

theorem positive_root_cut_monotone (M : Positive D) (hM : ‖M.1‖ ≤ 1) (ε : ℝ≥0) :
    Monotone (fun k => Positive.cut ε (Positive.power (Positive.rootExponent k) M)) := by
  intro j k hjk
  change cfcₙ (fun t : ℝ => max (t-ε) 0) (M.1 ^ Positive.rootExponent j) ≤
    cfcₙ (fun t : ℝ => max (t-ε) 0) (M.1 ^ Positive.rootExponent k)
  rw [CFC.nnrpow_eq_cfcₙ_real M.1 _ M.2,CFC.nnrpow_eq_cfcₙ_real M.1 _ M.2,
    ← cfcₙ_comp' (fun t : ℝ => max (t-ε) 0) (fun t : ℝ => t ^ (Positive.rootExponent j : ℝ)) M.1
      (hf0 := Real.zero_rpow (show (Positive.rootExponent j : ℝ) ≠ 0 by exact_mod_cast (Positive.rootExponent_pos j).ne')),
    ← cfcₙ_comp' (fun t : ℝ => max (t-ε) 0) (fun t : ℝ => t ^ (Positive.rootExponent k : ℝ)) M.1
      (hf0 := Real.zero_rpow (show (Positive.rootExponent k : ℝ) ≠ 0 by exact_mod_cast (Positive.rootExponent_pos k).ne'))]
  apply (cfcₙ_le_iff _ _ M.1
    (hf0 := by simp [Real.zero_rpow (show (Positive.rootExponent j : ℝ) ≠ 0 by exact_mod_cast (Positive.rootExponent_pos j).ne')])
    (hg0 := by simp [Real.zero_rpow (show (Positive.rootExponent k : ℝ) ≠ 0 by exact_mod_cast (Positive.rootExponent_pos k).ne')])
    (ha := IsSelfAdjoint.of_nonneg M.2)).mpr
  intro t ht
  have ht0 := quasispectrum_nonneg_of_nonneg M.1 M.2 t ht
  have ht1 : t ≤ 1 := (le_abs_self t).trans
    ((NonUnitalIsometricContinuousFunctionalCalculus.norm_quasispectrum_le M.1 ht
      (IsSelfAdjoint.of_nonneg M.2)).trans hM)
  exact max_le_max (sub_le_sub_right (Real.rpow_le_rpow_of_exponent_ge' ht0 ht1
    (Positive.rootExponent k).2 (Positive.rootExponent_antitone hjk)) ε) le_rfl

theorem positive_cut_le_smul_root_cut (M : Positive D) (hM : ‖M.1‖ ≤ 1)
    (δ r α : ℝ≥0) (hr : 0 < r) (hα : (α : ℝ) < (δ : ℝ) ^ (r : ℝ)) :
    (Positive.cut δ M).1 ≤ (1/((δ : ℝ)^(r : ℝ)-α)) •
      (Positive.cut α (Positive.power r M)).1 := by
  change cfcₙ (fun t : ℝ => max (t-δ) 0) M.1 ≤
    (1/((δ : ℝ)^(r : ℝ)-α)) • cfcₙ (fun t : ℝ => max (t-α) 0) (M.1 ^ r)
  rw [CFC.nnrpow_eq_cfcₙ_real M.1 r M.2,
    ← cfcₙ_comp' (fun t : ℝ => max (t-α) 0) (fun t : ℝ => t^(r : ℝ)) M.1
      (hf0 := Real.zero_rpow (show (r : ℝ) ≠ 0 by exact_mod_cast hr.ne')),
    ← cfcₙ_smul (1/((δ : ℝ)^(r : ℝ)-α)) (fun t : ℝ => max (t^(r : ℝ)-α) 0) M.1
      (h0 := by simp [Real.zero_rpow (show (r : ℝ) ≠ 0 by exact_mod_cast hr.ne')])]
  apply (cfcₙ_le_iff _ _ M.1 (hf0 := by simp)
    (hg0 := by simp [Real.zero_rpow (show (r : ℝ) ≠ 0 by exact_mod_cast hr.ne')])
    (ha := IsSelfAdjoint.of_nonneg M.2)).mpr
  intro t ht
  change max (t-δ) 0 ≤ (1/((δ : ℝ)^(r : ℝ)-α))*max (t^(r : ℝ)-α) 0
  by_cases htδ : t ≤ δ
  · rw [max_eq_right (sub_nonpos.mpr htδ)]
    exact mul_nonneg (one_div_nonneg.mpr (sub_pos.mpr hα).le) (le_max_right _ _)
  · have hpow : (δ : ℝ)^(r : ℝ) ≤ t^(r : ℝ) :=
      Real.rpow_le_rpow δ.2 (le_of_not_ge htδ) r.2
    have ht1 : t ≤ 1 := (le_abs_self t).trans
      ((NonUnitalIsometricContinuousFunctionalCalculus.norm_quasispectrum_le M.1 ht
        (IsSelfAdjoint.of_nonneg M.2)).trans hM)
    calc
      max (t-δ) 0 ≤ 1 := max_le ((sub_le_self t δ.2).trans ht1) zero_le_one
      _ = (1/((δ : ℝ)^(r : ℝ)-α))*((δ : ℝ)^(r : ℝ)-α) := by field_simp [(sub_pos.mpr hα).ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((sub_le_sub_right hpow α).trans (le_max_left _ _))
        (one_div_nonneg.mpr (sub_pos.mpr hα).le)

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma finiteSpectralIntegral_roots_monotone
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (M : Positive (FinMatrix A n)) (hM : ‖M.1‖ ≤ 1) :
    Monotone (fun k => finiteSpectralIntegral d n (Positive.power (Positive.rootExponent k) M)) := by
  intro j k hjk
  apply lintegral_mono
  intro t
  apply hd
  apply (finitePositiveClass_le_iff n _ _).mpr
  exact (cuntzSubequiv_iff_shared _ _).mpr
    (CuntzBelow.of_le _ _ (positive_root_cut_monotone M hM t.toNNReal hjk))

lemma finiteSpectralIntegral_root_le
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (M : Positive (FinMatrix A n)) (hM : ‖M.1‖ ≤ 1) (k : ℕ) :
    finiteSpectralIntegral d n (Positive.power (Positive.rootExponent k) M) ≤
      d (finitePositiveClass n M) := by
  have h := finiteSpectralIntegral_le d hd n (Positive.power (Positive.rootExponent k) M)
  rw [finitePositiveClass_power n M _ (Positive.rootExponent_pos k)] at h
  exact h.trans (mul_le_of_le_one_right bot_le (by
    simpa using ENNReal.ofReal_le_ofReal (Positive.power_norm_le_one _ (Positive.rootExponent_pos k) M hM)))
end CuntzPureness

end

end OAI
