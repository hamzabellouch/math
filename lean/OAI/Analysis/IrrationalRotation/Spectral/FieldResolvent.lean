import OAI.Analysis.IrrationalRotation.Analysis.FieldUnboundedMultiplier
import OAI.Analysis.IrrationalRotation.Spectral.FieldDiagonalPolar

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexOrder

namespace Invariant233.WeightedShift

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

private theorem resolventCoefficient_bound (t : ℝ) (ht : 0 ≤ t) :
    ‖((1 + t)⁻¹ : ℝ)‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
  exact (inv_le_one₀ (by positivity)).mpr (by linarith)

def positiveResolventWeight (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k)
    (x : X) : Weight :=
  ⟨fun k => (((1 + h x k)⁻¹ : ℝ) : ℂ), memℓp_infty <| by
    refine ⟨1, ?_⟩
    rintro r ⟨k, rfl⟩
    simpa only [Complex.norm_real] using
      resolventCoefficient_bound (h x k) (hpos x k)⟩

omit [MeasurableSpace X] in
private theorem positiveResolventWeight_bound
    (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k) (x : X) :
    ‖positiveResolventWeight h hpos x‖ ≤ 1 := by
  apply lp.norm_le_of_forall_le (by norm_num)
  intro k
  simpa only [positiveResolventWeight, Complex.norm_real] using
    resolventCoefficient_bound (h x k) (hpos x k)

private theorem positiveResolventWeight_measurable
    (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) (k : ℤ) :
    AEStronglyMeasurable (fun x => positiveResolventWeight h hpos x k) μ :=
  Complex.continuous_ofReal.comp_aestronglyMeasurable (((hm k).const_add 1).inv₀)

def positiveFieldResolvent (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) :
    FieldHilbert μ →L[ℂ] FieldHilbert μ :=
  fieldDiagonal (positiveResolventWeight h hpos) 1 (by norm_num)
    (positiveResolventWeight_bound h hpos)
    (positiveResolventWeight_measurable h hpos hm)

theorem positiveFieldResolvent_ae
    (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) (ξ : FieldHilbert μ) :
    ∀ᵐ x ∂μ, ∀ k,
      positiveFieldResolvent h hpos hm ξ x k =
        (((1 + h x k)⁻¹ : ℝ) : ℂ) * ξ x k :=
  fieldDiagonal_coordinate_ae _ _ _ _ _ ξ

theorem positiveFieldResolvent_nonneg
    (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) :
    0 ≤ positiveFieldResolvent h hpos hm := by
  apply fieldDiagonal_nonneg
  apply Eventually.of_forall
  intro x k
  change 0 ≤ ((((1 + h x k)⁻¹ : ℝ) : ℂ))
  exact Complex.nonneg_iff.mpr
    ⟨inv_nonneg.mpr (add_nonneg (by norm_num) (hpos x k)), rfl⟩

theorem norm_positiveFieldResolvent_le
    (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) :
    ‖positiveFieldResolvent h hpos hm‖ ≤ 1 :=
  norm_fieldDiagonal_le _ _ _ _ _

private theorem resolvent_scalar_identity (t : ℝ) (ht : 0 ≤ t) (z : ℂ) :
    z - (((1 + t)⁻¹ : ℝ) : ℂ) * z =
      (t : ℂ) * ((((1 + t)⁻¹ : ℝ) : ℂ) * z) := by
  have hne : (1 + (t : ℂ)) ≠ 0 := by
    exact_mod_cast (show (1 + t : ℝ) ≠ 0 by positivity)
  push_cast
  field_simp
  ring

theorem positiveFieldResolvent_mem_domain
    (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) (ξ : FieldHilbert μ) :
    positiveFieldResolvent h hpos hm ξ ∈
      (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).domain := by
  apply (mem_fieldUnboundedMultiplier_domain_iff _ _).mpr
  refine ⟨ξ - positiveFieldResolvent h hpos hm ξ, ?_⟩
  filter_upwards [positiveFieldResolvent_ae h hpos hm ξ,
    Lp.coeFn_sub ξ (positiveFieldResolvent h hpos hm ξ)] with x hR hsub
  intro k
  rw [hsub]
  change ξ x k - positiveFieldResolvent h hpos hm ξ x k = _
  rw [hR]
  exact resolvent_scalar_identity (h x k) (hpos x k) (ξ x k)

theorem fieldUnboundedMultiplier_positiveFieldResolvent
    (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) (ξ : FieldHilbert μ) :
    fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))
      ⟨positiveFieldResolvent h hpos hm ξ,
        positiveFieldResolvent_mem_domain h hpos hm ξ⟩ =
      ξ - positiveFieldResolvent h hpos hm ξ := by
  apply fieldUnboundedMultiplier_eq_of_ae
  filter_upwards [positiveFieldResolvent_ae h hpos hm ξ,
    Lp.coeFn_sub ξ (positiveFieldResolvent h hpos hm ξ)] with x hR hsub
  intro k
  rw [hsub]
  change ξ x k - positiveFieldResolvent h hpos hm ξ x k = _
  rw [hR]
  exact resolvent_scalar_identity (h x k) (hpos x k) (ξ x k)

theorem positiveFieldResolvent_apply_add_multiplier
    (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ)
    (ξ : (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).domain) :
    positiveFieldResolvent h hpos hm
      (ξ.val + fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ξ) = ξ.val := by
  apply fieldHilbert_ext
  filter_upwards [positiveFieldResolvent_ae h hpos hm
      (ξ.val + fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ξ),
    fieldUnboundedMultiplier_apply_ae (fun x k => (h x k : ℂ)) ξ,
    Lp.coeFn_add ξ.val (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ξ)]
    with x hR hH hadd
  intro k
  rw [hR, hadd]
  change (((1 + h x k)⁻¹ : ℝ) : ℂ) *
    (ξ.val x k + fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ξ x k) = _
  rw [hH]
  have hne : (1 + (h x k : ℂ)) ≠ 0 := by
    exact_mod_cast (show (1 + h x k : ℝ) ≠ 0 by
      have := hpos x k
      positivity)
  push_cast
  field_simp

theorem fieldUnboundedMultiplier_domain_eq_resolvent_range
    (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) :
    (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).domain =
      LinearMap.range (positiveFieldResolvent h hpos hm).toLinearMap := by
  ext ξ
  constructor
  · intro hξ
    exact ⟨ξ + fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ⟨ξ, hξ⟩,
      positiveFieldResolvent_apply_add_multiplier h hpos hm ⟨ξ, hξ⟩⟩
  · rintro ⟨η, rfl⟩
    exact positiveFieldResolvent_mem_domain h hpos hm η

theorem fieldUnboundedMultiplier_domain_invariant_of_commute_resolvent
    (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ)
    (A : FieldHilbert μ →L[ℂ] FieldHilbert μ)
    (hA : Commute A (positiveFieldResolvent h hpos hm))
    (ξ : (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).domain) :
    A ξ.val ∈ (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).domain := by
  apply (fieldUnboundedMultiplier_domain_eq_resolvent_range h hpos hm).ge
  refine ⟨A (ξ.val + fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ξ), ?_⟩
  have heq := congrArg (fun B : FieldHilbert μ →L[ℂ] FieldHilbert μ =>
    B (ξ.val + fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ξ)) hA.eq
  change positiveFieldResolvent h hpos hm
    (A (ξ.val + fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ξ)) = A ξ.val
  change A (positiveFieldResolvent h hpos hm
    (ξ.val + fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ξ)) =
    positiveFieldResolvent h hpos hm
      (A (ξ.val + fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ξ)) at heq
  rw [← heq, positiveFieldResolvent_apply_add_multiplier h hpos hm ξ]

theorem fieldUnboundedMultiplier_commutes_of_commute_resolvent
    (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ)
    (A : FieldHilbert μ →L[ℂ] FieldHilbert μ)
    (hA : Commute A (positiveFieldResolvent h hpos hm))
    (ξ : (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).domain) :
    fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))
      ⟨A ξ.val,
        fieldUnboundedMultiplier_domain_invariant_of_commute_resolvent h hpos hm A hA ξ⟩ =
      A (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ξ) := by
  let η := ξ.val + fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ξ
  have hRη : positiveFieldResolvent h hpos hm η = ξ.val :=
    positiveFieldResolvent_apply_add_multiplier h hpos hm ξ
  have hRA : positiveFieldResolvent h hpos hm (A η) = A ξ.val := by
    have heq := congrArg (fun B : FieldHilbert μ →L[ℂ] FieldHilbert μ => B η) hA.eq
    change A (positiveFieldResolvent h hpos hm η) =
      positiveFieldResolvent h hpos hm (A η) at heq
    exact heq.symm.trans (congrArg A hRη)
  have hξ : (⟨A ξ.val,
      fieldUnboundedMultiplier_domain_invariant_of_commute_resolvent h hpos hm A hA ξ⟩ :
        (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).domain) =
      ⟨positiveFieldResolvent h hpos hm (A η),
        positiveFieldResolvent_mem_domain h hpos hm (A η)⟩ :=
    Subtype.ext hRA.symm
  rw [hξ, fieldUnboundedMultiplier_positiveFieldResolvent, hRA]
  dsimp [η]
  rw [map_add, add_sub_cancel_left]

end Invariant233.WeightedShift

end

end OAI
