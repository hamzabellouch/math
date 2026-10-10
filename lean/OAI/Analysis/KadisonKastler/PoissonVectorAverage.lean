import OAI.Analysis.KadisonKastler.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! # Vector integration for Poisson smoothing

The averages are taken on each Hilbert-space vector. No norm measurability
of an operator-valued field is required. The fixed standard Cauchy measure
allows dominated convergence at every point of strong continuity.
-/

namespace KadisonKastler

open MeasureTheory Filter Topology

noncomputable section

variable {S H : Type*} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem integrable_vectorField (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hm : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    {C : ℝ} (hb : ∀ᵐ s ∂μ, ‖F s‖ ≤ C) (x : H) :
    Integrable (fun s => F s x) μ := by
  apply (integrable_const (C * ‖x‖)).mono' (hm x)
  filter_upwards [hb] with s hs
  exact ((F s).le_opNorm x).trans (mul_le_mul_of_nonneg_right hs (norm_nonneg x))

/-- An actual bounded operator obtained by integrating its values on vectors. -/
def probabilityOperatorIntegral (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hm : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    (C : ℝ) (hb : ∀ᵐ s ∂μ, ‖F s‖ ≤ C) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun x => ∫ s, F s x ∂μ
      map_add' := fun x y => by
        simp only [map_add]
        exact integral_add (integrable_vectorField μ F hm hb x)
          (integrable_vectorField μ F hm hb y)
      map_smul' := fun c x => by
        simp only [map_smul, RingHom.id_apply]
        exact integral_smul c (fun s => F s x) }
    C (fun x => by
      have h := norm_integral_le_of_norm_le_const (μ := μ) (C := C * ‖x‖)
        (by
          filter_upwards [hb] with s hs
          exact ((F s).le_opNorm x).trans
            (mul_le_mul_of_nonneg_right hs (norm_nonneg x)))
      simpa using h)

omit [CompleteSpace H] in
@[simp] theorem probabilityOperatorIntegral_apply (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hm : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    (C : ℝ) (hb : ∀ᵐ s ∂μ, ‖F s‖ ≤ C) (x : H) :
    probabilityOperatorIntegral μ F hm C hb x = ∫ s, F s x ∂μ := rfl

omit [CompleteSpace H] in
theorem norm_probabilityOperatorIntegral_le (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hm : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ s ∂μ, ‖F s‖ ≤ C) :
    ‖probabilityOperatorIntegral μ F hm C hb‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  have h := norm_integral_le_of_norm_le_const (μ := μ) (C := C * ‖x‖)
    (by
      filter_upwards [hb] with s hs
      exact ((F s).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right hs (norm_nonneg x)))
  simpa only [probabilityOperatorIntegral_apply, probReal_univ, mul_one] using h

theorem probabilityOperatorIntegral_star (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hm : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    (hmstar : ∀ x, AEStronglyMeasurable (fun s => star (F s) x) μ)
    (C : ℝ) (hb : ∀ᵐ s ∂μ, ‖F s‖ ≤ C) :
    probabilityOperatorIntegral μ (fun s => star (F s)) hmstar C
        (hb.mono fun s hs => (norm_star (F s)).le.trans hs) =
      star (probabilityOperatorIntegral μ F hm C hb) := by
  ext x
  apply ext_inner_left ℂ
  intro y
  rw [probabilityOperatorIntegral_apply, ← integral_inner
    (integrable_vectorField μ (fun s => star (F s)) hmstar
      (hb.mono fun s hs => (norm_star (F s)).le.trans hs) x)]
  simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  rw [probabilityOperatorIntegral_apply]
  calc
    (∫ s, inner ℂ (F s y) x ∂μ) =
        ∫ s, star (inner ℂ x (F s y)) ∂μ := by
      congr 1
      funext s
      exact (inner_conj_symm _ _).symm
    _ = star (∫ s, inner ℂ x (F s y) ∂μ) := integral_conj
    _ = star (inner ℂ x (∫ s, F s y ∂μ)) := by
      rw [integral_inner (integrable_vectorField μ F hm hb y)]
    _ = inner ℂ (∫ s, F s y ∂μ) x := inner_conj_symm _ _

omit [CompleteSpace H] in
theorem norm_probabilityOperatorIntegral_sub_le (μ : Measure S) [IsProbabilityMeasure μ]
    (F G : S → H →L[ℂ] H)
    (hmF : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    (hmG : ∀ x, AEStronglyMeasurable (fun s => G s x) μ)
    (C D : ℝ) (hF : ∀ᵐ s ∂μ, ‖F s‖ ≤ C) (hG : ∀ᵐ s ∂μ, ‖G s‖ ≤ D)
    {e : ℝ} (he : 0 ≤ e) (hFG : ∀ᵐ s ∂μ, ‖F s - G s‖ ≤ e) :
    ‖probabilityOperatorIntegral μ F hmF C hF -
      probabilityOperatorIntegral μ G hmG D hG‖ ≤ e := by
  apply ContinuousLinearMap.opNorm_le_bound _ he
  intro x
  change ‖(∫ s, F s x ∂μ) - ∫ s, G s x ∂μ‖ ≤ e * ‖x‖
  rw [← integral_sub (integrable_vectorField μ F hmF hF x)
    (integrable_vectorField μ G hmG hG x)]
  have h := norm_integral_le_of_norm_le_const (μ := μ) (C := e * ‖x‖)
    (by
      filter_upwards [hFG] with s hs
      exact ((F s - G s).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right hs (norm_nonneg x)))
  simpa only [sub_apply, probReal_univ, mul_one] using h

/-- Poisson averaging, written with the standard Cauchy random variable. -/
def poissonVectorAverage (F : ℝ → H →L[ℂ] H)
    (hF : ∀ x, Continuous (fun s => F s x)) (C : ℝ) (hC : ∀ s, ‖F s‖ ≤ C)
    (t r : ℝ) : H →L[ℂ] H :=
  probabilityOperatorIntegral (ProbabilityTheory.cauchyMeasure 0 1)
    (fun s => F (t + r * s))
    (fun x => ((hF x).comp (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable)
    C (ae_of_all _ fun _ => hC _)

theorem poissonVectorAverage_tendsto (F : ℝ → H →L[ℂ] H)
    (hF : ∀ x, Continuous (fun s => F s x)) (C : ℝ) (hC : ∀ s, ‖F s‖ ≤ C)
    (t : ℝ) (x : H) :
    Tendsto (fun r => poissonVectorAverage F hF C hC t r x) (𝓝 0) (𝓝 (F t x)) := by
  have hlim : Tendsto (fun r : ℝ => ∫ s, F (t + r * s) x
      ∂ProbabilityTheory.cauchyMeasure 0 1) (𝓝 0)
      (𝓝 (∫ _ : ℝ, F t x ∂ProbabilityTheory.cauchyMeasure 0 1)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => C * ‖x‖)
    · exact Eventually.of_forall fun r =>
        ((hF x).comp (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable
    · exact Eventually.of_forall fun r => ae_of_all _ fun s =>
        ((F (t + r * s)).le_opNorm x).trans
          (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg x))
    · exact integrable_const _
    · exact ae_of_all _ fun s => by
        have ht : Tendsto (fun r : ℝ => t + r * s) (𝓝 0) (𝓝 t) := by
          simpa only [zero_mul, add_zero] using
            (tendsto_const_nhds.add (tendsto_id.mul_const s) :
              Tendsto (fun r : ℝ => t + r * s) (𝓝 0) (𝓝 (t + 0 * s)))
        exact (hF x).continuousAt.tendsto.comp ht
  simpa only [poissonVectorAverage, probabilityOperatorIntegral_apply,
    integral_const, probReal_univ, one_smul] using hlim

/-- The adjoints also converge at every time of strong-* continuity. -/
theorem poissonVectorAverage_star_tendsto (F : ℝ → H →L[ℂ] H)
    (hF : ∀ x, Continuous (fun s => F s x))
    (hFs : ∀ x, Continuous (fun s => star (F s) x))
    (C : ℝ) (hC : ∀ s, ‖F s‖ ≤ C) (t : ℝ) (x : H) :
    Tendsto (fun r => star (poissonVectorAverage F hF C hC t r) x)
      (𝓝 0) (𝓝 (star (F t) x)) := by
  have he (r : ℝ) : star (poissonVectorAverage F hF C hC t r) =
      poissonVectorAverage (fun s => star (F s)) hFs C
        (fun s => (norm_star (F s)).le.trans (hC s)) t r := by
    exact (probabilityOperatorIntegral_star (ProbabilityTheory.cauchyMeasure 0 1)
      (fun s => F (t + r * s)) _ _ C _).symm
  simp_rw [he]
  exact poissonVectorAverage_tendsto _ hFs C _ t x

end

end KadisonKastler

end OAI
