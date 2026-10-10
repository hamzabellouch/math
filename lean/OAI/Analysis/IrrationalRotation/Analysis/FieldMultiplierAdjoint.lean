import OAI.Analysis.IrrationalRotation.Analysis.FieldUnboundedMultiplier
import OAI.Analysis.IrrationalRotation.Rotation.FieldDiagonal

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

private def boundedFieldWeight (a : X → ℤ → ℂ) (ha : ∀ x k, ‖a x k‖ ≤ 1)
    (x : X) : Weight :=
  ⟨a x, memℓp_infty ⟨1, by rintro r ⟨k, rfl⟩; exact ha x k⟩⟩

omit [MeasurableSpace X] in
private theorem boundedFieldWeight_norm (a : X → ℤ → ℂ) (ha : ∀ x k, ‖a x k‖ ≤ 1)
    (x : X) : ‖boundedFieldWeight a ha x‖ ≤ 1 :=
  lp.norm_le_of_forall_le (by norm_num) (ha x)

private def boundedField (a : X → ℤ → ℂ) (ha : ∀ x k, ‖a x k‖ ≤ 1)
    (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ) :
    FieldHilbert μ →L[ℂ] FieldHilbert μ :=
  fieldDiagonal (boundedFieldWeight a ha) 1 (by norm_num)
    (boundedFieldWeight_norm a ha) hm

private theorem boundedField_ae (a : X → ℤ → ℂ) (ha : ∀ x k, ‖a x k‖ ≤ 1)
    (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ) (ξ : FieldHilbert μ) :
    ∀ᵐ x ∂μ, ∀ k, boundedField a ha hm ξ x k = a x k * ξ x k :=
  fieldDiagonal_coordinate_ae _ _ _ _ _ ξ

private def normalizer (z : ℂ) : ℂ := ((1 + ‖z‖)⁻¹ : ℝ)

private theorem normalizer_ne_zero (z : ℂ) : normalizer z ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  exact inv_ne_zero (by positivity)

private theorem normalizer_star (z : ℂ) : star (normalizer z) = normalizer z := by
  simp [normalizer]

private theorem norm_normalizer (z : ℂ) : ‖normalizer z‖ = (1 + ‖z‖)⁻¹ := by
  simp only [normalizer, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (by positivity)

private theorem normalizer_bound (z : ℂ) : ‖normalizer z‖ ≤ 1 := by
  rw [norm_normalizer]
  have hn := norm_nonneg z
  exact (inv_le_one₀ (by positivity)).mpr (by linarith)

private theorem normalized_bound (z : ℂ) : ‖z * normalizer z‖ ≤ 1 := by
  rw [norm_mul, norm_normalizer, ← div_eq_mul_inv]
  exact (div_le_one (by positivity)).mpr (by linarith [norm_nonneg z])

private theorem normalizer_measurable (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) (k : ℤ) :
    AEStronglyMeasurable (fun x => normalizer (h x k)) μ :=
  Complex.continuous_ofReal.comp_aestronglyMeasurable (((hm k).norm.const_add 1).inv₀)

private def normalizerOperator (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) :
    FieldHilbert μ →L[ℂ] FieldHilbert μ :=
  boundedField (fun x k => normalizer (h x k))
    (fun x k => normalizer_bound (h x k)) (normalizer_measurable h hm)

private def normalizedOperator (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) :
    FieldHilbert μ →L[ℂ] FieldHilbert μ :=
  boundedField (fun x k => h x k * normalizer (h x k))
    (fun x k => normalized_bound (h x k))
    (fun k => (hm k).mul (normalizer_measurable h hm k))

private theorem normalizerOperator_ae (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) (ξ : FieldHilbert μ) :
    ∀ᵐ x ∂μ, ∀ k, normalizerOperator h hm ξ x k = normalizer (h x k) * ξ x k :=
  boundedField_ae _ _ _ ξ

private theorem normalizedOperator_ae (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) (ξ : FieldHilbert μ) :
    ∀ᵐ x ∂μ, ∀ k, normalizedOperator h hm ξ x k =
      (h x k * normalizer (h x k)) * ξ x k :=
  boundedField_ae _ _ _ ξ

private theorem normalizerOperator_selfAdjoint (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) :
    IsSelfAdjoint (normalizerOperator h hm) := by
  rw [isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint]
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro ξ η
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [normalizerOperator_ae h hm ξ, normalizerOperator_ae h hm η]
    with x hξ hη
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  rw [hξ, hη]
  simp only [RCLike.inner_apply', map_mul, starRingEnd_apply, normalizer_star]
  ring

private theorem normalizerOperator_injective (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) :
    Function.Injective (normalizerOperator h hm) := by
  intro ξ η heq
  apply fieldHilbert_ext
  filter_upwards [normalizerOperator_ae h hm ξ, normalizerOperator_ae h hm η]
    with x hξ hη
  intro k
  apply mul_left_cancel₀ (normalizer_ne_zero (h x k))
  rw [← hξ, ← hη, heq]

private theorem normalizer_mem_domain (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) (ξ : FieldHilbert μ) :
    normalizerOperator h hm ξ ∈ (fieldUnboundedMultiplier μ h).domain := by
  apply (mem_fieldUnboundedMultiplier_domain_iff h _).mpr
  refine ⟨normalizedOperator h hm ξ, ?_⟩
  filter_upwards [normalizerOperator_ae h hm ξ, normalizedOperator_ae h hm ξ]
    with x hR hS
  intro k
  rw [hR, hS, mul_assoc]

private theorem multiplier_normalizer (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) (ξ : FieldHilbert μ) :
    fieldUnboundedMultiplier μ h
      ⟨normalizerOperator h hm ξ, normalizer_mem_domain h hm ξ⟩ =
        normalizedOperator h hm ξ := by
  apply fieldUnboundedMultiplier_eq_of_ae
  filter_upwards [normalizerOperator_ae h hm ξ, normalizedOperator_ae h hm ξ]
    with x hR hS
  intro k
  rw [hR, hS, mul_assoc]

theorem dense_fieldUnboundedMultiplier_domain (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) :
    Dense ((fieldUnboundedMultiplier μ h).domain : Set (FieldHilbert μ)) := by
  let R := normalizerOperator h hm
  have hs : R.adjoint = R := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using
      (normalizerOperator_selfAdjoint h hm).star_eq
  have hk : R.ker = ⊥ := LinearMap.ker_eq_bot.mpr (normalizerOperator_injective h hm)
  have hc : R.range.topologicalClosure = ⊤ := by
    have heq := R.orthogonal_ker
    rw [hs, hk, Submodule.bot_orthogonal_eq_top] at heq
    exact heq.symm
  have hd : Dense (R.range : Set (FieldHilbert μ)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr hc
  apply hd.mono
  rintro ξ ⟨η, rfl⟩
  exact normalizer_mem_domain h hm η

private def normalizedStarOperator (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) :
    FieldHilbert μ →L[ℂ] FieldHilbert μ :=
  boundedField (fun x k => star (h x k * normalizer (h x k)))
    (fun x k => by simpa only [norm_star] using normalized_bound (h x k))
    (fun k => ((hm k).mul (normalizer_measurable h hm k)).star)

private theorem normalizedStarOperator_ae (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) (ξ : FieldHilbert μ) :
    ∀ᵐ x ∂μ, ∀ k, normalizedStarOperator h hm ξ x k =
      (star (h x k) * normalizer (h x k)) * ξ x k := by
  filter_upwards [boundedField_ae
    (fun x k => star (h x k * normalizer (h x k)))
    (fun x k => by simpa only [norm_star] using normalized_bound (h x k))
    (fun k => ((hm k).mul (normalizer_measurable h hm k)).star) ξ] with x hx
  intro k
  simpa only [normalizedStarOperator, star_mul, normalizer_star, mul_comm] using hx k

private theorem normalizedOperator_adjoint (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) :
    (normalizedOperator h hm).adjoint = normalizedStarOperator h hm := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro ξ η
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [normalizedStarOperator_ae h hm ξ, normalizedOperator_ae h hm η]
    with x hξ hη
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  rw [hξ, hη]
  simp only [RCLike.inner_apply', map_mul, starRingEnd_apply, star_star, normalizer_star]
  ring

theorem adjoint_fieldUnboundedMultiplier_apply_ae (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ)
    (ξ : (fieldUnboundedMultiplier μ h).adjoint.domain) :
    ∀ᵐ x ∂μ, ∀ k, (fieldUnboundedMultiplier μ h).adjoint ξ x k =
      star (h x k) * ξ.val x k := by
  let R := normalizerOperator h hm
  let S := normalizedOperator h hm
  have hs : R.adjoint = R := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using
      (normalizerOperator_selfAdjoint h hm).star_eq
  have heq : R ((fieldUnboundedMultiplier μ h).adjoint ξ) = S.adjoint ξ.val := by
    apply ext_inner_right ℂ
    intro η
    calc
      inner ℂ (R ((fieldUnboundedMultiplier μ h).adjoint ξ)) η =
          inner ℂ ((fieldUnboundedMultiplier μ h).adjoint ξ) (R η) := by
        simpa only [hs] using
          R.adjoint_inner_left η ((fieldUnboundedMultiplier μ h).adjoint ξ)
      _ = inner ℂ ξ.val (S η) := by
        have hf := LinearPMap.adjoint_isFormalAdjoint
          (dense_fieldUnboundedMultiplier_domain h hm) ξ
          ⟨R η, normalizer_mem_domain h hm η⟩
        simpa only [R, S, multiplier_normalizer] using hf
      _ = inner ℂ (S.adjoint ξ.val) η := (S.adjoint_inner_left η ξ.val).symm
  have heq' : normalizerOperator h hm ((fieldUnboundedMultiplier μ h).adjoint ξ) =
      normalizedStarOperator h hm ξ.val := by
    simpa only [R, S, normalizedOperator_adjoint] using heq
  filter_upwards [normalizerOperator_ae h hm ((fieldUnboundedMultiplier μ h).adjoint ξ),
    normalizedStarOperator_ae h hm ξ.val] with x hR hS
  intro k
  apply mul_left_cancel₀ (normalizer_ne_zero (h x k))
  calc
    normalizer (h x k) * (fieldUnboundedMultiplier μ h).adjoint ξ x k =
        normalizerOperator h hm ((fieldUnboundedMultiplier μ h).adjoint ξ) x k :=
      (hR k).symm
    _ = normalizedStarOperator h hm ξ.val x k := by rw [heq']
    _ = (star (h x k) * normalizer (h x k)) * ξ.val x k := hS k
    _ = normalizer (h x k) * (star (h x k) * ξ.val x k) := by ring

theorem adjoint_fieldUnboundedMultiplier (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) :
    (fieldUnboundedMultiplier μ h).adjoint =
      fieldUnboundedMultiplier μ (fun x k => star (h x k)) := by
  apply le_antisymm
  · constructor
    · intro ξ hξ
      apply (mem_fieldUnboundedMultiplier_domain_iff _ _).mpr
      exact ⟨(fieldUnboundedMultiplier μ h).adjoint ⟨ξ, hξ⟩,
        adjoint_fieldUnboundedMultiplier_apply_ae h hm ⟨ξ, hξ⟩⟩
    · intro ξ η hξη
      symm
      apply fieldUnboundedMultiplier_eq_of_ae
      filter_upwards [adjoint_fieldUnboundedMultiplier_apply_ae h hm ξ] with x hx
      intro k
      rw [hx, hξη]
  · exact LinearPMap.IsFormalAdjoint.le_adjoint
      (dense_fieldUnboundedMultiplier_domain h hm)
      (fieldUnboundedMultiplier_formalAdjoint h)

theorem isSelfAdjoint_fieldUnboundedMultiplier_real (h : X → ℤ → ℝ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) :
    IsSelfAdjoint (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))) := by
  rw [LinearPMap.isSelfAdjoint_def,
    adjoint_fieldUnboundedMultiplier _
      (fun k => Complex.continuous_ofReal.comp_aestronglyMeasurable (hm k))]
  congr 1
  funext x k
  simp

theorem isClosed_fieldUnboundedMultiplier_real (h : X → ℤ → ℝ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) :
    (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).IsClosed :=
  (isSelfAdjoint_fieldUnboundedMultiplier_real h hm).isClosed

theorem fieldMultiplier_denseRange (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ)
    (hh : ∀ᵐ x ∂μ, ∀ k, h x k ≠ 0) :
    DenseRange (fieldUnboundedMultiplier μ h) := by
  change Dense (LinearMap.range (fieldUnboundedMultiplier μ h).toFun : Set (FieldHilbert μ))
  rw [fieldMultiplier_range h hh]
  exact dense_fieldUnboundedMultiplier_domain _ (fun k => (hm k).inv₀)

end Invariant233.WeightedShift

end

end OAI
