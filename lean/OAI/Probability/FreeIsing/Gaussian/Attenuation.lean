import OAI.Probability.FreeIsing.Energy.Attenuation
import OAI.Probability.FreeIsing.Gaussian.SmallBall

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367
namespace GaussianAttenuation

private lemma tanh_strictMono : StrictMono Real.tanh := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(hasDerivAt_tanh_response x).deriv]
  exact sub_pos.mpr (Real.tanh_sq_lt_one x)

private lemma tanh_abs (x : ℝ) : Real.tanh |x| = |Real.tanh x| := by
  rcases le_total 0 x with hx | hx
  · have ht : 0 ≤ Real.tanh x := by
      simpa only [Real.tanh_zero] using tanh_strictMono.monotone hx
    rw [abs_of_nonneg hx, abs_of_nonneg ht]
  · have ht : Real.tanh x ≤ 0 := by
      simpa only [Real.tanh_zero] using tanh_strictMono.monotone hx
    rw [abs_of_nonpos hx, Real.tanh_neg, abs_of_nonpos ht]

lemma attenuation_sq_le_one {θ : ℝ} (hθ : θ ^ 2 ≤ 1) (x : ℝ) :
    responseAttenuation θ x ^ 2 ≤ 1 := by
  have hpos := responseAttenuation_pos hθ x
  have hle := responseAttenuation_le_one hθ x
  nlinarith

lemma integrable_attenuation_sq (m : ℝ) (v : ℝ≥0) {θ : ℝ} (hθ : θ ^ 2 ≤ 1) :
    Integrable (fun x => responseAttenuation θ x ^ 2) (gaussianReal m v) := by
  have hm : Measurable (fun x => responseAttenuation θ x ^ 2) := by
    simp only [responseAttenuation, Real.tanh_eq_sinh_div_cosh]
    fun_prop
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact attenuation_sq_le_one hθ x

theorem integral_attenuation_sq_le
    {θ : ℝ} (hθ : θ ^ 2 < 1) (m : ℝ) {δ v : ℝ≥0}
    (hδ : 0 < δ) (hδv : δ ≤ v) :
    ∫ x, responseAttenuation θ x ^ 2 ∂gaussianReal m v ≤
      1 - ((1 - θ ^ 2) * Real.tanh (gaussianSmallRadius δ) ^ 2) / 2 := by
  apply integral_gaussian_le_one_sub_half_gap m hδ hδv
    (integrable_attenuation_sq m v hθ.le)
  · exact mul_nonneg (sub_nonneg.mpr hθ.le) (sq_nonneg _)
  · exact attenuation_sq_le_one hθ.le
  · intro x hx
    have ht0 : 0 ≤ Real.tanh (gaussianSmallRadius δ) := by
      simpa only [Real.tanh_zero] using
        tanh_strictMono.monotone (gaussianSmallRadius_pos hδ).le
    have ht : Real.tanh (gaussianSmallRadius δ) ≤ |Real.tanh x| := by
      rw [← tanh_abs]
      exact tanh_strictMono.monotone hx.le
    have hsq : Real.tanh (gaussianSmallRadius δ) ^ 2 ≤ Real.tanh x ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ ht0 (abs_nonneg (Real.tanh x))).mpr ht
    have hmul := mul_le_mul_of_nonneg_left hsq (sub_nonneg.mpr hθ.le)
    have hpos := responseAttenuation_pos hθ.le x
    have hone := responseAttenuation_le_one hθ.le x
    have hbound := responseAttenuation_le_one_sub hθ.le x
    nlinarith

theorem integral_attenuation_sq_le_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {θ m : ℝ} {δ v : ℝ≥0} (hX : HasLaw X (gaussianReal m v) P)
    (hθ : θ ^ 2 < 1) (hδ : 0 < δ) (hδv : δ ≤ v) :
    ∫ ω, responseAttenuation θ (X ω) ^ 2 ∂P ≤
      1 - ((1 - θ ^ 2) * Real.tanh (gaussianSmallRadius δ) ^ 2) / 2 := by
  have heq := hX.integral_comp (integrable_attenuation_sq m v hθ.le).aestronglyMeasurable
  change (∫ ω, ((fun x => responseAttenuation θ x ^ 2) ∘ X) ω ∂P) ≤ _
  rw [heq]
  exact integral_attenuation_sq_le hθ m hδ hδv

theorem exists_uniform_attenuation_gap
    {θ : ℝ} (hθ : θ ^ 2 < 1) {δ : ℝ≥0} (hδ : 0 < δ) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧
      ∀ (m : ℝ) (v : ℝ≥0), δ ≤ v →
        ∫ x, responseAttenuation θ x ^ 2 ∂gaussianReal m v ≤ 1 - κ := by
  let κ := ((1 - θ ^ 2) * Real.tanh (gaussianSmallRadius δ) ^ 2) / 2
  have ht : 0 < Real.tanh (gaussianSmallRadius δ) := by
    simpa only [Real.tanh_zero] using tanh_strictMono (gaussianSmallRadius_pos hδ)
  refine ⟨κ, ?_, ?_, fun m v hv => integral_attenuation_sq_le hθ m hδ hv⟩
  · dsimp [κ]
    positivity
  · have hp := mul_nonneg (sq_nonneg θ) (sq_nonneg (Real.tanh (gaussianSmallRadius δ)))
    have hlt := Real.tanh_sq_lt_one (gaussianSmallRadius δ)
    dsimp [κ]
    nlinarith

theorem integral_shifted_attenuation_sq_mul_le
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    {shift weight : Y → ℝ} (hshift : Measurable shift) (hweight : Measurable weight)
    (hint : Integrable weight ν) (hnonneg : ∀ y, 0 ≤ weight y)
    {θ : ℝ} (hθ : θ ^ 2 < 1) (m : ℝ) {δ v : ℝ≥0}
    (hδ : 0 < δ) (hδv : δ ≤ v) :
    ∫ p : ℝ × Y, responseAttenuation θ (p.1 + shift p.2) ^ 2 * weight p.2
        ∂(gaussianReal m v).prod ν ≤
      (1 - ((1 - θ ^ 2) * Real.tanh (gaussianSmallRadius δ) ^ 2) / 2) *
        ∫ y, weight y ∂ν := by
  let q := 1 - ((1 - θ ^ 2) * Real.tanh (gaussianSmallRadius δ) ^ 2) / 2
  let F : ℝ × Y → ℝ := fun p =>
    responseAttenuation θ (p.1 + shift p.2) ^ 2 * weight p.2
  have hm : Measurable F := by
    dsimp [F]
    simp only [responseAttenuation, Real.tanh_eq_sinh_div_cosh]
    fun_prop
  have hF : Integrable F ((gaussianReal m v).prod ν) := by
    apply (hint.comp_snd (gaussianReal m v)).mono' hm.aestronglyMeasurable
    refine Filter.Eventually.of_forall fun p => ?_
    change ‖responseAttenuation θ (p.1 + shift p.2) ^ 2 * weight p.2‖ ≤ weight p.2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hnonneg p.2))]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (attenuation_sq_le_one hθ.le (p.1 + shift p.2)) (hnonneg p.2)
  have hbound (y : Y) : (∫ x, F (x, y) ∂gaussianReal m v) ≤ q * weight y := by
    have hLaw : HasLaw (fun x : ℝ => x + shift y)
        (gaussianReal (m + shift y) v) (gaussianReal m v) :=
      ⟨(measurable_id.add_const _).aemeasurable, gaussianReal_map_add_const _⟩
    have h := integral_attenuation_sq_le_of_hasLaw hLaw hθ hδ hδv
    change (∫ x, responseAttenuation θ (x + shift y) ^ 2 * weight y
      ∂gaussianReal m v) ≤ q * weight y
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right h (hnonneg y)
  change (∫ p, F p ∂(gaussianReal m v).prod ν) ≤ q * ∫ y, weight y ∂ν
  rw [integral_prod_symm F hF]
  calc
    _ ≤ ∫ y, q * weight y ∂ν :=
      integral_mono hF.integral_prod_right (hint.const_mul q) hbound
    _ = _ := integral_const_mul _ _

theorem integral_shifted_attenuation_sq_mul_le_of_indepFun
    {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    {P : Measure Ω} [IsFiniteMeasure P] {X : Ω → ℝ} {Z : Ω → Y}
    {m : ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal m v) P)
    (hZ : AEMeasurable Z P) (hind : IndepFun X Z P)
    {shift weight : Y → ℝ} (hshift : Measurable shift) (hweight : Measurable weight)
    (hint : Integrable (fun ω => weight (Z ω)) P) (hnonneg : ∀ y, 0 ≤ weight y)
    {θ : ℝ} (hθ : θ ^ 2 < 1) {δ : ℝ≥0} (hδ : 0 < δ) (hδv : δ ≤ v) :
    ∫ ω, responseAttenuation θ (X ω + shift (Z ω)) ^ 2 * weight (Z ω) ∂P ≤
      (1 - ((1 - θ ^ 2) * Real.tanh (gaussianSmallRadius δ) ^ 2) / 2) *
        ∫ ω, weight (Z ω) ∂P := by
  let F : ℝ × Y → ℝ := fun p =>
    responseAttenuation θ (p.1 + shift p.2) ^ 2 * weight p.2
  have hm : Measurable F := by
    dsimp [F]
    simp only [responseAttenuation, Real.tanh_eq_sinh_div_cosh]
    fun_prop
  have hpair : HasLaw (fun ω => (X ω, Z ω)) ((gaussianReal m v).prod (P.map Z)) P := by
    refine ⟨hX.aemeasurable.prodMk hZ, ?_⟩
    rw [hind.map_prod_eq_prod_map_map hX.aemeasurable hZ, hX.map_eq]
  have hweightInt : Integrable weight (P.map Z) :=
    (integrable_map_measure hweight.aestronglyMeasurable hZ).2 hint
  have h := integral_shifted_attenuation_sq_mul_le (P.map Z) hshift hweight
    hweightInt hnonneg hθ m hδ hδv
  rw [integral_map hZ hweight.aestronglyMeasurable] at h
  calc
    _ = ∫ p, F p ∂(gaussianReal m v).prod (P.map Z) :=
      hpair.integral_comp hm.aestronglyMeasurable
    _ ≤ _ := h

end GaussianAttenuation
end Problem367

end

end OAI
