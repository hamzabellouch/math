import OAI.Geometry.RCD.Coordinates.NormalizationRebase
import OAI.Geometry.RCD.Heat.HeatGramError

namespace OAI

/-! # Returning the heat comparison to the original coordinate frame -/

open Set MeasureTheory
open Filter
open scoped InnerProductSpace Topology

noncomputable section

namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)
  {χ : X → ℝ} (hχ : Continuous χ) (hsχ : HasCompactSupport χ)

/-- Rebasing the columns preserves the unregularized normalized heat
matrix; the original regularizer contributes its exact conjugate. -/
theorem cutoffHeatGram_rebase (U : E →L[ℝ] SobolevSpace μ hQ)
    (T A : E ≃L[ℝ] E) {t : ℝ} (ht : 0 < t) (x : X) (lambda : ℝ) :
    (A : E →L[ℝ] E).adjoint.comp
      ((cutoffHeatGram μ hQ hk hχ hsχ U ht x lambda).comp (A : E →L[ℝ] E)) =
    (A.trans T.symm : E →L[ℝ] E).adjoint.comp
      ((cutoffHeatGram μ hQ hk hχ hsχ (U.comp (T : E →L[ℝ] E)) ht x 0).comp
        (A.trans T.symm : E →L[ℝ] E)) +
      (lambda * t) • (A : E →L[ℝ] E).adjoint.comp (A : E →L[ℝ] E) := by
  rw [cutoffHeatGram_conjugate, cutoffHeatGram_conjugate, normalized_column_rebase]
  simp only [zero_mul, zero_smul, add_zero]

/-- The scalar regularizer in the original frame costs the squared norm
of the one working-scale normalization. This constant is independent of
all subsequent finer scales. -/
theorem cutoffHeatGram_rebase_norm_le (U : E →L[ℝ] SobolevSpace μ hQ)
    (T A : E ≃L[ℝ] E) {t : ℝ} (ht : 0 < t) (x : X) (lambda : ℝ)
    {b : ℝ} (hA : ‖(A.trans T.symm : E →L[ℝ] E)‖ ^ 2 ≤ b) :
    ‖(A : E →L[ℝ] E).adjoint.comp
        ((cutoffHeatGram μ hQ hk hχ hsχ U ht x lambda).comp (A : E →L[ℝ] E)) -
      ContinuousLinearMap.id ℝ E‖ ≤
    ‖(A.trans T.symm : E →L[ℝ] E).adjoint.comp
        ((cutoffHeatGram μ hQ hk hχ hsχ (U.comp (T : E →L[ℝ] E)) ht x 0).comp
          (A.trans T.symm : E →L[ℝ] E)) - ContinuousLinearMap.id ℝ E‖ +
      |lambda * t| * ‖(T : E →L[ℝ] E)‖ ^ 2 * b := by
  have heq : (A : E →L[ℝ] E) =
      (T : E →L[ℝ] E).comp (A.trans T.symm : E →L[ℝ] E) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply]
  have hnorm : ‖(A : E →L[ℝ] E)‖ ^ 2 ≤ ‖(T : E →L[ℝ] E)‖ ^ 2 * b := by
    calc
      _ = ‖(T : E →L[ℝ] E).comp (A.trans T.symm : E →L[ℝ] E)‖ ^ 2 := by rw [← heq]
      _ ≤ (‖(T : E →L[ℝ] E)‖ * ‖(A.trans T.symm : E →L[ℝ] E)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.opNorm_comp_le _ _) 2
      _ ≤ _ := by rw [mul_pow]; exact mul_le_mul_of_nonneg_left hA (sq_nonneg _)
  have hreg : ‖(lambda * t) • (A : E →L[ℝ] E).adjoint.comp (A : E →L[ℝ] E)‖ ≤
      |lambda * t| * ‖(T : E →L[ℝ] E)‖ ^ 2 * b := by
    rw [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_adjoint_comp_self]
    simpa only [mul_assoc, pow_two] using mul_le_mul_of_nonneg_left hnorm (abs_nonneg (lambda * t))
  rw [cutoffHeatGram_rebase μ hQ hk hχ hsχ U T A ht x lambda]
  have he : ∀ P Q I : E →L[ℝ] E, P + Q - I = (P - I) + Q := by intros; abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (le_refl _) hreg)

omit [CompleteSpace E] in
/-- A fixed bound for the working frame permits a uniform fine-scale
choice for the original scalar regularizer. -/
theorem exists_rebased_regularizer_threshold {B R lambda η : ℝ}
    (hB : 0 ≤ B) (hη : 0 < η) :
    ∃ N : ℕ, ∀ k, N ≤ k → ∀ r, 0 ≤ r → (2 : ℝ) ^ k * r ≤ R →
      ∀ T : E →L[ℝ] E, ‖T‖ ^ 2 ≤ B →
        |lambda * r ^ 2| * ‖T‖ ^ 2 * (2 : ℝ) ^ k < η := by
  have hdecay : Tendsto (fun k : ℕ => (|lambda| * R ^ 2 * B) * (1 / 2 : ℝ) ^ k)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (|lambda| * R ^ 2 * B)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hdecay.eventually_lt_const hη)
  refine ⟨N, fun k hk r hr hR T hT => ?_⟩
  have h₁ := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hT (abs_nonneg (lambda * r ^ 2)))
    (by positivity : 0 ≤ (2 : ℝ) ^ k)
  have h₂ := mul_le_mul_of_nonneg_right (dyadic_regularizer_le_geometric
    (lambda := lambda) hr k hR) hB
  have h₃ : |lambda * r ^ 2| * B * (2 : ℝ) ^ k ≤
      (|lambda| * R ^ 2 * B) * (1 / 2 : ℝ) ^ k := by nlinarith only [h₂]
  exact (h₁.trans h₃).trans_lt (hN k hk)

end RegularPointCoordinates

end

end OAI
