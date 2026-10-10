import Mathlib
import OAI.Analysis.Conductivity.Variational.SmoothSupportedAdd

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Filter Topology

def smoothCompose {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : SmoothScalar E) : SmoothScalar ℝ →ₐ[ℝ] SmoothScalar E where
  toFun H := ⟨H.val ∘ φ.val, (smoothScalar_contDiff H).comp (smoothScalar_contDiff φ)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] lemma smoothCompose_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (φ : SmoothScalar E) (H : SmoothScalar ℝ) (x : E) :
    (smoothCompose φ H).val x = H.val (φ.val x) := rfl

lemma smoothDirection_compose {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (φ : SmoothScalar E) (H : SmoothScalar ℝ) :
    smoothDirection v (smoothCompose φ H) =
      smoothDirection v φ * smoothCompose φ (smoothDirection 1 H) := by
  apply Subtype.ext
  funext x
  change fderiv ℝ (H.val ∘ φ.val) x v =
    fderiv ℝ φ.val x v * fderiv ℝ H.val (φ.val x) 1
  rw [fderiv_comp x ((smoothScalar_contDiff H).differentiable (by simp) _)
    ((smoothScalar_contDiff φ).differentiable (by simp) x)]
  simp only [ContinuousLinearMap.comp_apply]
  simpa only [smul_eq_mul, mul_one] using
    (fderiv ℝ H.val (φ.val x)).map_smul (fderiv ℝ φ.val x v) 1

def nonlinearFirstPotential {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ φ : SmoothScalar E) (H : SmoothScalar ℝ) (k : ℝ) : SmoothScalar E :=
  k⁻¹ • (χ * smoothCompose (k • φ) H)

lemma nonlinearFirstPotential_derivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : E) (χ φ : SmoothScalar E) (H : SmoothScalar ℝ)
    {k : ℝ} (hk : k ≠ 0) :
    smoothDirection v (nonlinearFirstPotential χ φ H k) =
      smoothDirection v φ * χ * smoothCompose (k • φ) (smoothDirection 1 H) +
        k⁻¹ • (smoothCompose (k • φ) H * smoothDirection v χ) := by
  simp only [nonlinearFirstPotential, map_smul, smoothDirection_mul,
    smoothDirection_compose]
  apply Subtype.ext
  funext x
  change k⁻¹ * (χ.val x * ((k * (smoothDirection v φ).val x) *
    (smoothDirection 1 H).val (k * φ.val x)) +
    H.val (k * φ.val x) * (smoothDirection v χ).val x) =
    (smoothDirection v φ).val x * χ.val x * (smoothDirection 1 H).val (k * φ.val x) +
      k⁻¹ * (H.val (k * φ.val x) * (smoothDirection v χ).val x)
  field_simp

lemma nonlinearFirstPotential_fderiv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (χ φ : SmoothScalar E) (H : SmoothScalar ℝ)
    {k : ℝ} (hk : k ≠ 0) (x : E) :
    fderiv ℝ (nonlinearFirstPotential χ φ H k).val x =
      (χ.val x * (smoothDirection 1 H).val (k * φ.val x)) • fderiv ℝ φ.val x +
        (k⁻¹ * H.val (k * φ.val x)) • fderiv ℝ χ.val x := by
  ext v
  have h := congrArg (fun f : SmoothScalar E => f.val x)
    (nonlinearFirstPotential_derivative v χ φ H hk)
  change fderiv ℝ (nonlinearFirstPotential χ φ H k).val x v =
    (χ.val x * (smoothDirection 1 H).val (k * φ.val x)) * fderiv ℝ φ.val x v +
      (k⁻¹ * H.val (k * φ.val x)) * fderiv ℝ χ.val x v
  change fderiv ℝ (nonlinearFirstPotential χ φ H k).val x v =
    fderiv ℝ φ.val x v * χ.val x * (smoothDirection 1 H).val (k * φ.val x) +
      k⁻¹ * (H.val (k * φ.val x) * fderiv ℝ χ.val x v) at h
  rw [h]
  ring

lemma nonlinearFirstPotential_support {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (χ φ : SmoothScalar E) (H : SmoothScalar ℝ) (k : ℝ) :
    tsupport (nonlinearFirstPotential χ φ H k).val ⊆ tsupport χ.val := by
  apply closure_mono
  intro x hx hχx
  apply hx
  change k⁻¹ * (χ.val x * H.val (k * φ.val x)) = 0
  rw [hχx, zero_mul, mul_zero]

lemma nonlinearFirstPotential_error_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : E) (χ φ : SmoothScalar E) (H : SmoothScalar ℝ)
    (hχ : HasCompactSupport χ.val) (hH : ∃ C : ℝ, ∀ t, |H.val t| ≤ C) :
    TendstoUniformly
      (fun k x => (smoothDirection v (nonlinearFirstPotential χ φ H k)).val x -
        (smoothDirection v φ).val x * χ.val x * (smoothDirection 1 H).val (k * φ.val x))
      (fun _ => 0) atTop := by
  obtain ⟨A, hA⟩ := (smoothScalar_contDiff (smoothDirection v χ)).continuous
    |>.bounded_above_of_compact_support (compactSupport_smoothDirection v hχ)
  obtain ⟨B, hB⟩ := hH
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  apply uniform_zero_of_bound (b := fun k : ℝ => |k⁻¹| * B * A)
  · simpa using ((tendsto_inv_atTop_zero.abs.mul_const B).mul_const A)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with k hk x
    have he := congrArg (fun f : SmoothScalar E => f.val x)
      (nonlinearFirstPotential_derivative v χ φ H (ne_of_gt hk))
    change (smoothDirection v (nonlinearFirstPotential χ φ H k)).val x =
      (smoothDirection v φ).val x * χ.val x * (smoothDirection 1 H).val (k * φ.val x) +
        k⁻¹ * (H.val (k * φ.val x) * (smoothDirection v χ).val x) at he
    rw [he, add_sub_cancel_left, abs_mul, abs_mul, ← mul_assoc]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hB _) (abs_nonneg _))
      (by simpa only [Real.norm_eq_abs] using hA x)
      (abs_nonneg _) (mul_nonneg (abs_nonneg _) hB0)

lemma nonlinearFirstPotential_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (χ φ : SmoothScalar E) (H : SmoothScalar ℝ)
    (hχ : HasCompactSupport χ.val) (hH : ∃ C : ℝ, ∀ t, |H.val t| ≤ C) :
    TendstoUniformly (fun k => (nonlinearFirstPotential χ φ H k).val)
      (fun _ => 0) atTop := by
  obtain ⟨A, hA⟩ := (smoothScalar_contDiff χ).continuous.bounded_above_of_compact_support hχ
  obtain ⟨B, hB⟩ := hH
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  apply uniform_zero_of_bound (b := fun k : ℝ => |k⁻¹| * A * B)
  · simpa using ((tendsto_inv_atTop_zero.abs.mul_const A).mul_const B)
  · exact Filter.Eventually.of_forall fun k x => by
      change |k⁻¹ * (χ.val x * H.val (k * φ.val x))| ≤ _
      rw [abs_mul, abs_mul, ← mul_assoc]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (by simpa using hA x) (abs_nonneg _))
        (hB _) (abs_nonneg _) (mul_nonneg (abs_nonneg _) hA0)

lemma nonlinearFirstPotential_eventually_positive {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (d : E) (χ φ : SmoothScalar E) (H : SmoothScalar ℝ)
    (hχ : HasCompactSupport χ.val) (hH : ∃ C : ℝ, ∀ t, |H.val t| ≤ C)
    (c m : ℝ) (hm : 0 < m)
    (hpos : ∀ k x, m ≤ 1 + c *
      ((smoothDirection d φ).val x * χ.val x * (smoothDirection 1 H).val (k * φ.val x))) :
    ∀ᶠ k : ℝ in atTop, ∀ x,
      0 < 1 + fderiv ℝ (c • nonlinearFirstPotential χ φ H k).val x d := by
  have ht := ((ContinuousLinearMap.id ℝ ℝ).smulRight c).uniformContinuous.comp_tendstoUniformly
    (nonlinearFirstPotential_error_tendsto d χ φ H hχ hH)
  have hs : ∀ᶠ k : ℝ in atTop, ∀ x,
      |c * ((smoothDirection d (nonlinearFirstPotential χ φ H k)).val x -
        (smoothDirection d φ).val x * χ.val x * (smoothDirection 1 H).val (k * φ.val x))| < m := by
    simpa [Function.comp_def, mul_comm, dist_zero_left, Real.norm_eq_abs] using
      (Metric.tendstoUniformly_iff.mp ht) m hm
  filter_upwards [hs] with k hk x
  change 0 < 1 + (smoothDirection d (c • nonlinearFirstPotential χ φ H k)).val x
  rw [map_smul]
  change 0 < 1 + c * (smoothDirection d (nonlinearFirstPotential χ φ H k)).val x
  have he := (abs_lt.mp (hk x)).1
  have hp := hpos k x
  nlinarith

theorem nonlinearFirstPotential_diffeomorphisms {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (d : E) (χ φ : SmoothScalar E) (H : SmoothScalar ℝ)
    (hχ : HasCompactSupport χ.val) (hH : ∃ C : ℝ, ∀ t, |H.val t| ≤ C)
    (c m : ℝ) (hm : 0 < m)
    (hpos : ∀ k x, m ≤ 1 + c *
      ((smoothDirection d φ).val x * χ.val x * (smoothDirection 1 H).val (k * φ.val x))) :
    ∀ᶠ k : ℝ in atTop, ∃ X : E ≃ E,
      (∀ x, X x = x + (c * (nonlinearFirstPotential χ φ H k).val x) • d) ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) X ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) X.symm := by
  filter_upwards [nonlinearFirstPotential_eventually_positive d χ φ H hχ hH c m hm hpos]
    with k hk
  apply exists_smooth_lineShift_inverse d (c • nonlinearFirstPotential χ φ H k) hk
  have hc : HasCompactSupport (nonlinearFirstPotential χ φ H k).val :=
    hχ.of_isClosed_subset (isClosed_tsupport _) (nonlinearFirstPotential_support χ φ H k)
  exact (smoothScalar_contDiff (c • nonlinearFirstPotential χ φ H k)).continuous
    |>.bounded_above_of_compact_support (hc.smul_left)

end ScalarConductivity

end

end OAI
