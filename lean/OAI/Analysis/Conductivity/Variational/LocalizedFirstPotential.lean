import Mathlib
import OAI.Analysis.Conductivity.Variational.AirySymbol
import OAI.Analysis.Conductivity.Fourier.SmoothPhase

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

def localizedFirstPotential {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : SmoothScalar E) (L : E →L[ℝ] ℝ) (H : SmoothScalar ℝ) (k : ℝ) :
    SmoothScalar E := k⁻¹ • (χ * smoothPhase (k • L) H)

def localizedSecondPotential {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : SmoothScalar E) (L : E →L[ℝ] ℝ) (H : SmoothScalar ℝ) (k : ℝ) :
    SmoothScalar E := (k ^ 2)⁻¹ • (χ * smoothPhase (k • L) H)

theorem localizedFirstPotential_derivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : E) (χ : SmoothScalar E) (L : E →L[ℝ] ℝ)
    (H : SmoothScalar ℝ) {k : ℝ} (hk : k ≠ 0) :
    smoothDirection v (localizedFirstPotential χ L H k) =
      L v • (χ * smoothPhase (k • L) (smoothDirection 1 H)) +
        k⁻¹ • (smoothPhase (k • L) H * smoothDirection v χ) := by
  simp only [localizedFirstPotential, map_smul, smoothDirection_mul,
    smoothDirection_phase]
  apply Subtype.ext
  funext x
  change k⁻¹ * (χ.val x * ((k * L v) *
    (smoothDirection 1 H).val (k * L x)) +
    H.val (k * L x) * (smoothDirection v χ).val x) =
    L v * (χ.val x * (smoothDirection 1 H).val (k * L x)) +
      k⁻¹ * (H.val (k * L x) * (smoothDirection v χ).val x)
  field_simp

theorem localizedSecondPotential_derivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v w : E) (χ : SmoothScalar E) (L : E →L[ℝ] ℝ)
    (H : SmoothScalar ℝ) {k : ℝ} (hk : k ≠ 0) :
    smoothDirection v (smoothDirection w (localizedSecondPotential χ L H k)) =
      (L v * L w) •
        (χ * smoothPhase (k • L) (smoothDirection 1 (smoothDirection 1 H))) +
      k⁻¹ • ((L w • smoothDirection v χ + L v • smoothDirection w χ) *
        smoothPhase (k • L) (smoothDirection 1 H)) +
      (k ^ 2)⁻¹ • (smoothPhase (k • L) H *
        smoothDirection v (smoothDirection w χ)) := by
  simp only [localizedSecondPotential, map_smul, map_add, smoothDirection_mul,
    smoothDirection_phase]
  apply Subtype.ext
  funext x
  change (k ^ 2)⁻¹ *
    (χ.val x * ((k * L w) * ((k * L v) *
       (smoothDirection 1 (smoothDirection 1 H)).val (k * L x))) +
    ((k * L w) * (smoothDirection 1 H).val (k * L x)) *
      (smoothDirection v χ).val x +
    (H.val (k * L x) * (smoothDirection v (smoothDirection w χ)).val x +
      (smoothDirection w χ).val x * ((k * L v) *
        (smoothDirection 1 H).val (k * L x)))) =
    (L v * L w) * (χ.val x *
      (smoothDirection 1 (smoothDirection 1 H)).val (k * L x)) +
    k⁻¹ * ((L w * (smoothDirection v χ).val x +
      L v * (smoothDirection w χ).val x) *
        (smoothDirection 1 H).val (k * L x)) +
    (k ^ 2)⁻¹ * (H.val (k * L x) *
      (smoothDirection v (smoothDirection w χ)).val x)
  field_simp
  ring

open Filter Topology

theorem uniform_zero_of_bound {X I : Type*} {l : Filter I}
    {f : I → X → ℝ} {b : I → ℝ}
    (hb : Tendsto b l (𝓝 0)) (hf : ∀ᶠ i in l, ∀ x, |f i x| ≤ b i) :
    TendstoUniformly f (fun _ => 0) l := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [hf, hb.eventually_lt_const hε] with i hi hib x
  simpa only [dist_zero_left, Real.norm_eq_abs] using (hi x).trans_lt hib

theorem localizedFirstPotential_error_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : E) (χ : SmoothScalar E) (L : E →L[ℝ] ℝ)
    (H : SmoothScalar ℝ) (hχ : HasCompactSupport χ.val)
    (hH : ∃ C : ℝ, ∀ t, |H.val t| ≤ C) :
    TendstoUniformly
      (fun k x => (smoothDirection v (localizedFirstPotential χ L H k)).val x -
        L v * (χ.val x * (smoothDirection 1 H).val (k * L x)))
      (fun _ => 0) atTop := by
  obtain ⟨A, hA⟩ := ((smoothScalar_contDiff (smoothDirection v χ)).continuous).bounded_above_of_compact_support (compactSupport_smoothDirection v hχ)
  obtain ⟨B, hB⟩ := hH
  have hBnonneg : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  apply uniform_zero_of_bound (b := fun k : ℝ => |k⁻¹| * B * A)
  · simpa using ((tendsto_inv_atTop_zero.abs.mul_const B).mul_const A)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with k hk x
    rw [localizedFirstPotential_derivative v χ L H (ne_of_gt hk)]
    change |L v * (χ.val x * (smoothDirection 1 H).val (k * L x)) +
      k⁻¹ * (H.val (k * L x) * (smoothDirection v χ).val x) -
        L v * (χ.val x * (smoothDirection 1 H).val (k * L x))| ≤ |k⁻¹| * B * A
    rw [add_sub_cancel_left, abs_mul, abs_mul, ← mul_assoc]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hB _) (abs_nonneg _))
      (by simpa only [Real.norm_eq_abs] using hA x)
      (abs_nonneg _) (mul_nonneg (abs_nonneg _) hBnonneg)

theorem localizedSecondPotential_error_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v w : E) (χ : SmoothScalar E) (L : E →L[ℝ] ℝ)
    (H : SmoothScalar ℝ) (hχ : HasCompactSupport χ.val)
    (hH : ∃ C : ℝ, ∀ t, |H.val t| ≤ C)
    (hH' : ∃ C : ℝ, ∀ t, |(smoothDirection 1 H).val t| ≤ C) :
    TendstoUniformly
      (fun k x =>
        (smoothDirection v (smoothDirection w (localizedSecondPotential χ L H k))).val x -
        (L v * L w) *
          (χ.val x * (smoothDirection 1 (smoothDirection 1 H)).val (k * L x)))
      (fun _ => 0) atTop := by
  obtain ⟨A, hA⟩ := ((smoothScalar_contDiff (smoothDirection v χ)).continuous).bounded_above_of_compact_support (compactSupport_smoothDirection v hχ)
  obtain ⟨B, hB⟩ := ((smoothScalar_contDiff (smoothDirection w χ)).continuous).bounded_above_of_compact_support (compactSupport_smoothDirection w hχ)
  obtain ⟨C, hC⟩ :=
    ((smoothScalar_contDiff (smoothDirection v (smoothDirection w χ))).continuous).bounded_above_of_compact_support
        (compactSupport_smoothDirection v (compactSupport_smoothDirection w hχ))
  obtain ⟨M, hM⟩ := hH
  obtain ⟨N, hN⟩ := hH'
  have hAn : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hBn : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hMn : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hTn : 0 ≤ |L w| * A + |L v| * B := by positivity
  apply uniform_zero_of_bound (b := fun k : ℝ =>
    |k⁻¹| * ((|L w| * A + |L v| * B) * N) + |(k ^ 2)⁻¹| * (M * C))
  · have hi : Tendsto (fun k : ℝ => |k⁻¹|) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).abs
    have hi2 : Tendsto (fun k : ℝ => |(k ^ 2)⁻¹|) atTop (𝓝 0) := by
      simpa [inv_pow, abs_pow] using hi.pow 2
    simpa using (hi.mul_const ((|L w| * A + |L v| * B) * N)).add
      (hi2.mul_const (M * C))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with k hk x
    rw [localizedSecondPotential_derivative v w χ L H (ne_of_gt hk)]
    change |(L v * L w) *
      (χ.val x * (smoothDirection 1 (smoothDirection 1 H)).val (k * L x)) +
      k⁻¹ * ((L w * (smoothDirection v χ).val x +
        L v * (smoothDirection w χ).val x) * (smoothDirection 1 H).val (k * L x)) +
      (k ^ 2)⁻¹ * (H.val (k * L x) *
        (smoothDirection v (smoothDirection w χ)).val x) -
      (L v * L w) *
        (χ.val x * (smoothDirection 1 (smoothDirection 1 H)).val (k * L x))| ≤ _
    rw [add_assoc, add_sub_cancel_left]
    apply (abs_add_le _ _).trans
    apply add_le_add
    · rw [abs_mul, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply mul_le_mul _ (hN _) (abs_nonneg _) hTn
      apply (abs_add_le _ _).trans
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using hA x) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left
          (by simpa only [Real.norm_eq_abs] using hB x) (abs_nonneg _))
    · rw [abs_mul, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact mul_le_mul (hM _) (by simpa only [Real.norm_eq_abs] using hC x)
        (abs_nonneg _) hMn

end ScalarConductivity

end

end OAI
