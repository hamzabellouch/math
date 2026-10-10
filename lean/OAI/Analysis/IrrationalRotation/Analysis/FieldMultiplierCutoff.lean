import OAI.Analysis.IrrationalRotation.Model.SpectralCutoff
import OAI.Analysis.IrrationalRotation.Analysis.FieldMultiplierAdjoint
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace Invariant233.WeightedShift.SpectralCutoff
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem boundedOperator_ae (a : X → ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x k, ‖a x k‖ ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ) (ξ : FieldHilbert μ) :
    ∀ᵐ x ∂μ, ∀ k, boundedOperator a C hC ha hm ξ x k = a x k * ξ x k :=
  fieldDiagonal_coordinate_ae _ _ _ _ _ ξ

theorem projection_ae (h : X → ℤ → ℝ) (hm : ∀ k, Measurable (fun x => h x k))
    (n : ℕ) (ξ : FieldHilbert μ) :
    ∀ᵐ x ∂μ, ∀ k, projection h hm n ξ x k = symbol n (h x k) * ξ x k :=
  boundedOperator_ae _ _ _ _ _ ξ

theorem symbol_mul_self (n : ℕ) (r : ℝ) : symbol n r * symbol n r = symbol n r := by
  classical
  by_cases hr : r ∈ window n <;> simp [symbol, hr]

theorem star_symbol (n : ℕ) (r : ℝ) : star (symbol n r) = symbol n r := by
  classical
  by_cases hr : r ∈ window n <;> simp [symbol, hr]

theorem projection_isStarProjection (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) :
    IsStarProjection (projection (μ := μ) h hm n) := by
  constructor
  · change projection h hm n * projection h hm n = projection h hm n
    apply ContinuousLinearMap.ext
    intro ξ
    apply fieldHilbert_ext
    filter_upwards [projection_ae h hm n ξ,
      projection_ae h hm n (projection h hm n ξ)] with x hξ hE
    intro k
    change projection h hm n (projection h hm n ξ) x k = projection h hm n ξ x k
    rw [hE, hξ, ← mul_assoc, symbol_mul_self]
  · rw [isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint]
    symm
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro ξ η
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [projection_ae h hm n ξ, projection_ae h hm n η] with x hξ hη
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    apply tsum_congr
    intro k
    rw [hξ, hη]
    simp only [RCLike.inner_apply', map_mul, starRingEnd_apply, star_symbol]
    ring

theorem symbol_eventually_one {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, symbol n r = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max r r⁻¹)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hrn : r ≤ n + 1 := by have := le_max_left r r⁻¹; linarith
  have hirn : r⁻¹ ≤ n + 1 := by have := le_max_right r r⁻¹; linarith
  have hin : r ∈ window n :=
    ⟨(inv_le_comm₀ (by positivity) hr).mpr hirn, hrn⟩
  simp [symbol, hin]

theorem fiber_error_norm_le (h : ℤ → ℝ) (n : ℕ) (ξ : Hilbert) :
    ‖diagonal (boundedWeight (fun (_ : Unit) k => symbol n (h k)) 1
      (fun _ k => norm_symbol_le n (h k)) ()) ξ - ξ‖ ≤ ‖ξ‖ := by
  apply lp.norm_mono (by norm_num)
  intro k
  change ‖symbol n (h k) * ξ k - ξ k‖ ≤ ‖ξ k‖
  classical
  by_cases hk : h k ∈ window n <;> simp [symbol, hk]

theorem fiber_error_sq_tendsto (h : ℤ → ℝ) (hh : ∀ k, 0 < h k) (ξ : Hilbert) :
    Tendsto (fun n => ‖diagonal (boundedWeight (fun (_ : Unit) k => symbol n (h k)) 1
      (fun _ k => norm_symbol_le n (h k)) ()) ξ - ξ‖ ^ 2) atTop (𝓝 0) := by
  have hsum : Summable (fun k => ‖ξ k‖ ^ 2) := by
    simpa using (lp.memℓp ξ).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  have ht := tendsto_tsum_of_dominated_convergence
    (f := fun n k => ‖symbol n (h k) * ξ k - ξ k‖ ^ 2)
    (g := fun _ : ℤ => (0 : ℝ)) hsum
    (fun k => tendsto_const_nhds.congr' ((symbol_eventually_one (hh k)).mono
      (fun n hn => by simp [hn])))
    (Filter.Eventually.of_forall fun n k => by
      classical
      by_cases hk : h k ∈ window n <;> simp [symbol, hk])
  have heq (n : ℕ) :
      ‖diagonal (boundedWeight (fun (_ : Unit) k => symbol n (h k)) 1
        (fun _ k => norm_symbol_le n (h k)) ()) ξ - ξ‖ ^ 2 =
          ∑' k, ‖symbol n (h k) * ξ k - ξ k‖ ^ 2 := by
    simpa [boundedWeight] using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal)
      (diagonal (boundedWeight (fun (_ : Unit) k => symbol n (h k)) 1
        (fun _ k => norm_symbol_le n (h k)) ()) ξ - ξ)
  simpa only [← heq, tsum_zero] using ht

theorem norm_sq_eq_integral (ξ : FieldHilbert μ) :
    ‖ξ‖ ^ 2 = ∫ x, ‖ξ x‖ ^ 2 ∂μ := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def]
  have hr := integral_re (L2.integrable_inner (𝕜 := ℂ) ξ ξ)
  simp only [RCLike.re_eq_complex_re] at hr ⊢
  rw [← hr]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => inner_self_eq_norm_sq (𝕜 := ℂ) (ξ x)

theorem projection_tendsto (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k))
    (hh : ∀ᵐ x ∂μ, ∀ k, 0 < h x k) (ξ : FieldHilbert μ) :
    Tendsto (fun n => projection h hm n ξ) atTop (𝓝 ξ) := by
  let D : ℕ → FieldHilbert μ := fun n => projection h hm n ξ - ξ
  have hD (n : ℕ) : ∀ᵐ x ∂μ, D n x =
      diagonal (boundedWeight (fun (_ : Unit) k => symbol n (h x k)) 1
        (fun _ k => norm_symbol_le n (h x k)) ()) (ξ x) - ξ x := by
    filter_upwards [projection_ae h hm n ξ, Lp.coeFn_sub (projection h hm n ξ) ξ]
      with x hE hsub
    change (projection h hm n ξ - ξ) x = _
    rw [hsub]
    apply lp.ext
    funext k
    change projection h hm n ξ x k - ξ x k = symbol n (h x k) * ξ x k - ξ x k
    rw [hE]
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => ‖D n x‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [ae_all_iff.mpr hD, hh] with x hx hh
    simp only [hx]
    exact fiber_error_sq_tendsto (h x) hh (ξ x)
  have hb (n : ℕ) : ∀ᵐ x ∂μ, ‖‖D n x‖ ^ 2‖ ≤ ‖ξ x‖ ^ 2 := by
    filter_upwards [hD n] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _), hx]
    exact pow_le_pow_left₀ (norm_nonneg _) (fiber_error_norm_le (h x) n (ξ x)) 2
  have hi : Integrable (fun x => ‖ξ x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable ξ)).mp (Lp.memLp ξ)
  have ht := tendsto_integral_of_dominated_convergence (fun x => ‖ξ x‖ ^ 2)
    (fun n => ((Lp.aestronglyMeasurable (D n)).norm).pow 2) hi hb hlim
  have hs : Tendsto (fun n => ‖D n‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Pi.pow_apply, ← norm_sq_eq_integral, integral_zero] using ht
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs.sqrt

theorem norm_boundedOperator_le (a : X → ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x k, ‖a x k‖ ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ) :
    ‖boundedOperator a C hC ha hm‖ ≤ C :=
  norm_fieldDiagonal_le _ _ _ _ _

theorem productOperator_ae (h : X → ℤ → ℝ) (hm : ∀ k, Measurable (fun x => h x k))
    (n : ℕ) (ξ : FieldHilbert μ) :
    ∀ᵐ x ∂μ, ∀ k, productOperator h hm n ξ x k = productSymbol n (h x k) * ξ x k :=
  boundedOperator_ae _ _ _ _ _ ξ

theorem inverseOperator_ae (h : X → ℤ → ℝ) (hm : ∀ k, Measurable (fun x => h x k))
    (n : ℕ) (ξ : FieldHilbert μ) :
    ∀ᵐ x ∂μ, ∀ k, inverseOperator h hm n ξ x k = inverseSymbol n (h x k) * ξ x k :=
  boundedOperator_ae _ _ _ _ _ ξ

theorem norm_productOperator_le (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) :
    ‖productOperator (μ := μ) h hm n‖ ≤ n + 1 := norm_boundedOperator_le _ _ _ _ _

theorem norm_inverseOperator_le (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) :
    ‖inverseOperator (μ := μ) h hm n‖ ≤ n + 1 := norm_boundedOperator_le _ _ _ _ _

theorem projection_mem_domain (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) (ξ : FieldHilbert μ) :
    projection h hm n ξ ∈ (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).domain := by
  apply (mem_fieldUnboundedMultiplier_domain_iff _ _).mpr
  refine ⟨productOperator h hm n ξ, ?_⟩
  filter_upwards [projection_ae h hm n ξ, productOperator_ae h hm n ξ] with x hP hT
  intro k
  rw [hP, hT]
  exact mul_assoc _ _ _

theorem multiplier_projection (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) (ξ : FieldHilbert μ) :
    fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))
      ⟨projection h hm n ξ, projection_mem_domain h hm n ξ⟩ = productOperator h hm n ξ := by
  apply fieldUnboundedMultiplier_eq_of_ae
  filter_upwards [projection_ae h hm n ξ, productOperator_ae h hm n ξ] with x hP hT
  intro k
  rw [hP, hT]
  exact mul_assoc _ _ _

theorem inverseSymbol_mul_productSymbol (n : ℕ) (r : ℝ) :
    inverseSymbol n r * productSymbol n r = symbol n r := by
  classical
  by_cases hr : r ∈ window n
  · have hr0 : r ≠ 0 := ne_of_gt (lt_of_lt_of_le (by positivity) hr.1)
    simp [inverseSymbol, productSymbol, symbol, hr, hr0]
  · simp [inverseSymbol, productSymbol, symbol, hr]

theorem inverseOperator_mul_productOperator (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) :
    inverseOperator (μ := μ) h hm n * productOperator h hm n = projection h hm n := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply fieldHilbert_ext
  filter_upwards [projection_ae h hm n ξ, productOperator_ae h hm n ξ,
    inverseOperator_ae h hm n (productOperator h hm n ξ)] with x hP hT hI
  intro k
  change inverseOperator h hm n (productOperator h hm n ξ) x k = projection h hm n ξ x k
  rw [hI, hT, hP, ← mul_assoc, inverseSymbol_mul_productSymbol]

theorem projection_apply_of_mem_range (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ)
    {ξ : FieldHilbert μ} (hξ : ξ ∈ (projection h hm n).range) : projection h hm n ξ = ξ := by
  obtain ⟨η, rfl⟩ := hξ
  exact congrArg (fun A : FieldHilbert μ →L[ℂ] FieldHilbert μ => A η)
    (projection_isStarProjection h hm n).isIdempotentElem.eq

theorem projection_range_le_domain (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) :
    (projection h hm n).range ≤
      (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).domain := by
  rintro ξ ⟨η, rfl⟩
  exact projection_mem_domain h hm n η

theorem multiplier_on_range (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ)
    (ξ : (projection (μ := μ) h hm n).range) :
    fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))
      ⟨ξ.val, projection_range_le_domain h hm n ξ.property⟩ = productOperator h hm n ξ.val := by
  have hmP := multiplier_projection h hm n ξ.val
  have heq := projection_apply_of_mem_range h hm n ξ.property
  simpa only [heq] using hmP

theorem multiplier_range_bounds (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ)
    (ξ : (projection (μ := μ) h hm n).range) :
    let η := fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))
      ⟨ξ.val, projection_range_le_domain h hm n ξ.property⟩
    ‖η‖ ≤ (n + 1 : ℝ) * ‖ξ.val‖ ∧ ‖ξ.val‖ ≤ (n + 1 : ℝ) * ‖η‖ := by
  dsimp only
  rw [multiplier_on_range]
  constructor
  · exact (productOperator h hm n).le_of_opNorm_le (norm_productOperator_le h hm n) ξ.val
  · have heq : inverseOperator h hm n (productOperator h hm n ξ.val) = ξ.val := by
      have he := congrArg (fun A : FieldHilbert μ →L[ℂ] FieldHilbert μ => A ξ.val)
        (inverseOperator_mul_productOperator (μ := μ) h hm n)
      exact he.trans (projection_apply_of_mem_range h hm n ξ.property)
    have hb := (inverseOperator h hm n).le_of_opNorm_le (norm_inverseOperator_le h hm n)
      (productOperator h hm n ξ.val)
    rwa [heq] at hb

theorem real_mul_inverseSymbol (n : ℕ) (r : ℝ) :
    (r : ℂ) * inverseSymbol n r = symbol n r := by
  classical
  by_cases hr : r ∈ window n
  · have hr0 : r ≠ 0 := ne_of_gt (lt_of_lt_of_le (by positivity) hr.1)
    simp [inverseSymbol, symbol, hr, hr0]
  · simp [inverseSymbol, symbol, hr]

theorem inverseOperator_mem_domain (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) (ξ : FieldHilbert μ) :
    inverseOperator h hm n ξ ∈
      (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).domain := by
  apply (mem_fieldUnboundedMultiplier_domain_iff _ _).mpr
  refine ⟨projection h hm n ξ, ?_⟩
  filter_upwards [projection_ae h hm n ξ, inverseOperator_ae h hm n ξ] with x hP hI
  intro k
  rw [hP, hI, ← mul_assoc, real_mul_inverseSymbol]

theorem multiplier_inverseOperator (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) (ξ : FieldHilbert μ) :
    fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))
      ⟨inverseOperator h hm n ξ, inverseOperator_mem_domain h hm n ξ⟩ = projection h hm n ξ := by
  apply fieldUnboundedMultiplier_eq_of_ae
  filter_upwards [projection_ae h hm n ξ, inverseOperator_ae h hm n ξ] with x hP hI
  intro k
  rw [hP, hI, ← mul_assoc, real_mul_inverseSymbol]

theorem projection_mem_inverse_domain (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) (ξ : FieldHilbert μ) :
    projection h hm n ξ ∈
      (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).inverse.domain := by
  rw [LinearPMap.inverse_domain]
  exact ⟨⟨inverseOperator h hm n ξ, inverseOperator_mem_domain h hm n ξ⟩,
    multiplier_inverseOperator h hm n ξ⟩

theorem projection_range_le_inverse_domain (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) :
    (projection h hm n).range ≤
      (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).inverse.domain := by
  rintro ξ ⟨η, rfl⟩
  exact projection_mem_inverse_domain h hm n η

theorem inverse_multiplier_projection (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k))
    (hh : ∀ᵐ x ∂μ, ∀ k, 0 < h x k) (n : ℕ) (ξ : FieldHilbert μ) :
    (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).inverse
      ⟨projection h hm n ξ, projection_mem_inverse_domain h hm n ξ⟩ = inverseOperator h hm n ξ := by
  have hker : (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).ker = ⊥ := by
    apply LinearPMap.ker_eq_bot.mpr
    apply fieldUnboundedMultiplier_injective
    filter_upwards [hh] with x hx k
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (hx k))
  exact LinearPMap.inverse_apply_eq
    (y := ⟨projection h hm n ξ, projection_mem_inverse_domain h hm n ξ⟩)
    (x := ⟨inverseOperator h hm n ξ, inverseOperator_mem_domain h hm n ξ⟩)
    hker (multiplier_inverseOperator h hm n ξ)

theorem inverse_multiplier_on_range (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k))
    (hh : ∀ᵐ x ∂μ, ∀ k, 0 < h x k) (n : ℕ)
    (ξ : (projection (μ := μ) h hm n).range) :
    (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).inverse
      ⟨ξ.val, projection_range_le_inverse_domain h hm n ξ.property⟩ = inverseOperator h hm n ξ.val := by
  have hmP := inverse_multiplier_projection h hm hh n ξ.val
  have heq := projection_apply_of_mem_range h hm n ξ.property
  simpa only [heq] using hmP

theorem productOperator_mul_inverseOperator (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) :
    productOperator (μ := μ) h hm n * inverseOperator h hm n = projection h hm n := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply fieldHilbert_ext
  filter_upwards [projection_ae h hm n ξ, inverseOperator_ae h hm n ξ,
    productOperator_ae h hm n (inverseOperator h hm n ξ)] with x hP hI hT
  intro k
  change productOperator h hm n (inverseOperator h hm n ξ) x k = projection h hm n ξ x k
  rw [hT, hI, hP, ← mul_assoc, mul_comm (productSymbol n _) (inverseSymbol n _),
    inverseSymbol_mul_productSymbol]

theorem inverse_multiplier_range_bounds (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k))
    (hh : ∀ᵐ x ∂μ, ∀ k, 0 < h x k) (n : ℕ)
    (ξ : (projection (μ := μ) h hm n).range) :
    let η := (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).inverse
      ⟨ξ.val, projection_range_le_inverse_domain h hm n ξ.property⟩
    ‖η‖ ≤ (n + 1 : ℝ) * ‖ξ.val‖ ∧ ‖ξ.val‖ ≤ (n + 1 : ℝ) * ‖η‖ := by
  dsimp only
  rw [inverse_multiplier_on_range h hm hh]
  constructor
  · exact (inverseOperator h hm n).le_of_opNorm_le (norm_inverseOperator_le h hm n) ξ.val
  · have heq : productOperator h hm n (inverseOperator h hm n ξ.val) = ξ.val := by
      have he := congrArg (fun A : FieldHilbert μ →L[ℂ] FieldHilbert μ => A ξ.val)
        (productOperator_mul_inverseOperator (μ := μ) h hm n)
      exact he.trans (projection_apply_of_mem_range h hm n ξ.property)
    have hb := (productOperator h hm n).le_of_opNorm_le (norm_productOperator_le h hm n)
      (inverseOperator h hm n ξ.val)
    rwa [heq] at hb

theorem cutoffSpace_eq_range (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) :
    cutoffSpace (μ := μ) h hm n = (projection h hm n).range := by
  exact (ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (projection_isStarProjection h hm n).isIdempotentElem).submodule_topologicalClosure_eq

theorem cutoffSpace_starProjection (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) :
    (cutoffSpace (μ := μ) h hm n).starProjection = projection h hm n := by
  obtain ⟨hi, he⟩ := isStarProjection_iff_eq_starProjection_range.mp
    (projection_isStarProjection (μ := μ) h hm n)
  let := hi
  simpa only [cutoffSpace_eq_range] using he.symm

theorem cutoffSpace_tendsto (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k))
    (hh : ∀ᵐ x ∂μ, ∀ k, 0 < h x k) (ξ : FieldHilbert μ) :
    Tendsto (fun n => (cutoffSpace h hm n).starProjection ξ) atTop (𝓝 ξ) := by
  simpa only [cutoffSpace_starProjection] using projection_tendsto h hm hh ξ

theorem cutoffSpace_le_domains (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) :
    cutoffSpace (μ := μ) h hm n ≤
      (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).domain ∧
    cutoffSpace (μ := μ) h hm n ≤
      (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).inverse.domain := by
  rw [cutoffSpace_eq_range]
  exact ⟨projection_range_le_domain h hm n, projection_range_le_inverse_domain h hm n⟩

end Invariant233.WeightedShift.SpectralCutoff

end

end OAI
